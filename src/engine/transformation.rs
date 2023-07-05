use std::{
    cmp::{max, min},
    collections::HashSet,
    hash::Hash,
    process::Child,
};

use itertools::Itertools;
use syntax::ast::Meta;

use crate::{
    commons::util::{getstmtlist, visitrnode, workrnode, worksnode},
    engine::cocci_vs_rs::MetavarBinding,
    parsing_cocci::{
        ast0::{MetaVar, Snode, MODKIND},
        parse_cocci::{processcocci, Rule},
    },
    parsing_rs::{
        ast_rs::{Rnode, Wrap},
        parse_rs::processrs,
    },
};

use super::{
    cocci_vs_rs::{Environment, Looper, MetavarName},
    disjunctions::{getdisjunctions, Disjunction},
};

fn duplicaternode(node: &Rnode) -> Rnode {
    let mut rnode =
        Rnode { wrapper: Wrap::dummy(), astnode: node.astnode.clone(), children: vec![] };
    if node.children.len() == 0 {
        return rnode;
    } else {
        for child in &node.children {
            rnode.children.push(duplicaternode(&child));
        }
    }
    return rnode;
}

fn copytornodewithenv(rulename: &String, snode: Snode, env: &Environment) -> Rnode {
    if !snode.wrapper.metavar.isnotmeta() {
        if let Some(index) =
            env.bindings.iter().position(|x| x.metavarinfo.varname == snode.astnode.to_string())
        {
            return duplicaternode(env.bindings[index].rnode);
        } else {
            panic!("Metavariable should already be present in environment.");
        }
    }
    let mut rnode = Rnode { wrapper: Wrap::dummy(), astnode: snode.astnode, children: vec![] };
    for child in snode.children {
        rnode.children.push(copytornodewithenv(rulename, child, env));
    }
    rnode
}

fn snodetornode(rulename: &String, snodes: Vec<Snode>, env: &Environment) -> Vec<Rnode> {
    let mut rnodevec = vec![];
    for snode in snodes {
        rnodevec.push(copytornodewithenv(rulename, snode, env));
    }
    rnodevec
}

pub fn transform(rulename: &String, node: &mut Rnode, env: &Environment) {
    let f = &mut |x: &mut Rnode| -> bool {
        let mut shouldgodeeper: bool = false;
        let pos = x.getpos();
        for minus in env.minuses.clone() {
            if pos == minus {
                x.wrapper.isremoved = true;
                shouldgodeeper = true;
            } else if max(pos.0, minus.0) <= min(pos.1, minus.1) {
                //this if checks for an overlap between the rnode and all minuses
                //(and pluses too which will be added)
                shouldgodeeper = true;
                //if there is even one minus which partially
                //overlaps with the node we go deeper
            }
        }
        for (pluspos, pluses) in env.pluses.clone() {
            if pos.0 == pluspos && x.children.len() == 0 {
                x.wrapper.plussed.0 = snodetornode(rulename, pluses, env);
                //println!("======================== {:?}", x);
            } else if pos.1 == pluspos && x.children.len() == 0 {
                x.wrapper.plussed.1 = snodetornode(rulename, pluses, env);
            } else if pluspos >= pos.0 && pluspos <= pos.1 {
                shouldgodeeper = true;
            }
        }
        return shouldgodeeper;
    };
    workrnode(node, f);
}

fn trimpatchbindings(
    patchbindings: &mut Vec<Vec<MetavarBinding>>,
    usedafter: HashSet<MetavarName>,
) {
    for bindings in patchbindings.iter_mut() {
        //this only retains elements which are used later, but this may form duplicares
        bindings.retain(|x| usedafter.contains(&x.metavarinfo));
    }

    let mut tmp = HashSet::new();
    patchbindings.retain(|x| tmp.insert(x.clone()));
    //this line removes duplicates ^
}

pub fn transformfile(patchstring: String, rustcode: String) -> Rnode {
    fn tokenf<'a>(node1: &'a Snode, node2: &'a Rnode) -> Vec<MetavarBinding<'a>> {
        // this is
        // Tout will have the generic types in itself
        // ie  ('a * 'b) tout //Ocaml syntax
        // Should I replace Snode and Rnode with generic types?
        // transformation.ml's tokenf
        // info_to_fixpos
        vec![]
    }

    let rules = processcocci(&patchstring);
    //rules[0].patch.plus.print_tree();

    let rnode = processrs(&rustcode);
    let mut transformedcode = processrs(&rustcode);
    let mut patchbindings: Vec<Vec<MetavarBinding>> = vec![vec![]];
    let looper = Looper::new(tokenf);

    for mut rule in rules {
        let mut a: Disjunction =
            getdisjunctions(Disjunction(vec![getstmtlist(&mut rule.patch.minus).clone().children]));

        for disj in &mut a.0 {
            for node in disj {
                worksnode(node, (), &mut |x: &mut Snode, _| {
                    if x.wrapper.plusesaft.len() != 0 {
                        //println!("{:#?} attached after {}", x.wrapper.plusesaft, x.astnode.to_string());
                    }
                    if x.wrapper.plusesbef.len() != 0 {
                        //println!("{:#?} before {}", x.wrapper.plusesbef, x.astnode.to_string());
                    }
                    if let Some(MODKIND::MINUS) = x.wrapper.modkind {}
                });
            }
        }
        //let metavars = rule.metavars;

        let mut tmpbindings: Vec<Vec<MetavarBinding>> = vec![];
        for bindings in &patchbindings {
            if !(rule.freevars.iter().all(|x| bindings.iter().find(|y| y.metavarinfo == x.getminfo().0).is_some())) {
                //if all inherited dependencies of this rule is not satisfied by the bindings then move on
                //to the next bindings
                continue;
            }
            let envs = visitrnode(&a.0, &rnode, &|k, l| looper.handledisjunctions(k, l, bindings.clone()));
            for env in envs.clone() {
                transform(&rule.name, &mut transformedcode, &env);
                tmpbindings.push(env.bindings.clone());
            }
        }
        patchbindings.extend(tmpbindings);

        trimpatchbindings(&mut patchbindings, rule.usedafter);
        //rulebindings.extend(envs.iter().map(|x| x.bindings.clone()).collect_vec());
    }

    return transformedcode;
}
