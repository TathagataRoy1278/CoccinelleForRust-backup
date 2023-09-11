// SPDX-License-Identifier: GPL-2.0

use std::{
    cmp::{max, min},
    collections::HashSet,
};

use itertools::Itertools;

use crate::{
    commons::{
        info::ParseError,
        util::{getstmtlist, workrnode},
    },
    engine::cocci_vs_rs::{visitrnode, MetavarBinding},
    parsing_cocci::{
        ast0::{MetaVar, MetavarName, Snode},
        parse_cocci::Rule,
    },
    parsing_rs::{
        ast_rs::{Rnode, Wrap},
        parse_rs::processrs,
    },
};

use super::{
    cocci_vs_rs::{Environment, Looper},
    disjunctions::{getdisjunctions, Disjunction},
};

fn tokenf<'a>(_node1: &'a Snode, _node2: &'a Rnode) -> Vec<MetavarBinding> {
    vec![]
}

fn copytornodewithenv(snode: Snode, env: &Environment) -> Rnode {
    if !snode.wrapper.metavar.isnotmeta() {
        if let Some(mvar) = env.bindings.iter().find(|x| x.metavarinfo.varname == snode.getstring())
        {
            return (*mvar.rnode).clone();
        } else {
            panic!("Metavariable should already be present in environment.");
        }
    }
    let kind = snode.kind();
    let mut rnode = Rnode::new(
        Wrap::dummy(snode.children.len()),
        snode.asttoken,
        kind,
        vec![],
    );
    for child in snode.children {
        rnode.children.push(copytornodewithenv(child, env));
    }
    rnode
}

fn snodetornode(snodes: Vec<Snode>, env: &Environment) -> Vec<Rnode> {
    let mut rnodevec = vec![];
    for snode in snodes {
        rnodevec.push(copytornodewithenv(snode, env));
    }
    rnodevec
}

pub fn transform(node: &mut Rnode, env: &Environment) {
    let transformmods = &mut |x: &mut Rnode| -> bool {
        let mut shouldgodeeper: bool = false;
        let pos = x.getpos();
        for minus in env.modifiers.minuses.clone() {
            if pos == minus || pos.0 >= minus.0 && pos.1 <= minus.1 {
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
        for (pluspos, isbef, pluses) in env.modifiers.pluses.clone() {
            if pos.0 == pluspos && x.children.len() == 0 && isbef {
                x.wrapper.plussed.0 = snodetornode(pluses, env);
                println!("TESTIG bef {}", x.totoken());
                //println!("======================== {:?}", x);
            } else if pos.1 == pluspos && x.children.len() == 0 && !isbef {
                x.wrapper.plussed.1 = snodetornode(pluses, env);
                println!("TESTIG aft {}", x.totoken());
            } else if pluspos >= pos.0 && pluspos <= pos.1 {
                shouldgodeeper = true;
            }
        }
        return shouldgodeeper;
    };
    workrnode(node, transformmods);
}

fn trimpatchbindings(
    patchbindings: &mut Vec<Vec<MetavarBinding>>,
    usedafter: &HashSet<MetavarName>,
) {
    for bindings in patchbindings.iter_mut() {
        //this only retains elements which are used later, but this may form duplicares
        bindings.retain(|x| usedafter.contains(&x.metavarinfo));
    }

    let mut tmp = HashSet::new();
    patchbindings.retain(|x| tmp.insert(x.clone()));
    //this line removes duplicates ^
}

pub fn getexpandedbindings(mut bindings: Vec<Vec<MetavarBinding>>) -> Vec<Vec<MetavarBinding>> {
    let mut exbindings = vec![vec![]]; //expanded bindings
    if let Some(tmvars) = bindings.pop() {
        let obindings = getexpandedbindings(bindings.clone());
        for binding in tmvars {
            for mut obinding in obindings.clone() {
                obinding.push(binding.clone());
                exbindings.push(obinding);
            }
        }

        exbindings.remove(0); //removes the first vec![]
    }
    return exbindings;
}

pub fn getfiltered(
    freevars: &Vec<MetaVar>,
    bindings: &Vec<Vec<MetavarBinding>>,
) -> Vec<Vec<MetavarBinding>> {
    let mut toret: Vec<Vec<MetavarBinding>> = vec![];
    for var in freevars {
        let mut set = HashSet::new();
        for binding in bindings {
            if let Some(b) = binding.iter().find(|x| x.metavarinfo == var.getminfo().0) {
                set.insert(b.clone());
            }
        } //from all the collected bindings it gets all unique bindings for a given metavar

        if set.len() == 0 {
            //no bindings have been made
            continue;
        }
        toret.push(set.into_iter().collect_vec());
    }

    return toret;
}

pub fn transformrnode(rules: &Vec<Rule>, rnode: Rnode) -> Result<Rnode, ParseError>{

    let mut transformedcode = rnode;

    let mut savedbindings: Vec<Vec<MetavarBinding>> = vec![vec![]];
    for rule in rules {
        println!("Rule: {}, freevars: {:?}", rule.name, rule.freevars);
        let a: Disjunction =
            getdisjunctions(Disjunction(vec![getstmtlist(&rule.patch.minus).clone().children]));
        println!("filtered bindings : {:?}", getfiltered(&rule.freevars, &savedbindings));
        let expandedbindings = getexpandedbindings(getfiltered(&rule.freevars, &savedbindings));
        println!("Expanded bindings: {:?}", expandedbindings);
        let mut tmpbindings: Vec<Vec<MetavarBinding>> = vec![]; //this captures the bindings collected in current rule applciations
                                                                //let mut usedbindings = HashSet::new(); //this makes sure the same binding is not repeated
        for gbindings in expandedbindings {
            /*
            let bindings = gbindings
                .into_iter()
                .filter(|x| rule.freevars.iter().any(|y| y.getminfo().0 == x.metavarinfo))
                .collect_vec(); //This filters only those metavariables which are present in freevars
            if !(rule
                .freevars
                .iter()
                .all(|x| bindings.iter().any(|y| y.metavarinfo == x.getminfo().0)))
            //This checks if all necessary inherited metavars are present in this environment, if not, it is discarded
            {
                //if all inherited dependencies of this rule is not satisfied by the bindings then move on
                //to the next bindings
                continue;
            }
            */
            println!("For rule {}, inherited: {:#?}", rule.name, gbindings);
            let looper = Looper::new(tokenf);
            let envs = visitrnode(&a.0, &transformedcode, &|k, l| {
                looper.handledisjunctions(k, l, gbindings.iter().collect_vec())
            });

            for mut env in envs.clone() {
                transform(&mut transformedcode, &env);
                env.bindings.retain(|x| x.metavarinfo.rulename == rule.name);
                tmpbindings.push(env.bindings);
            }
        }
        //patchbindings.extend(tmpbindings);
        savedbindings.extend(tmpbindings);
        println!("usedafter : {:#?}", rule.usedafter);
        trimpatchbindings(&mut savedbindings, &rule.usedafter);
        println!("After trimming {:?}", savedbindings);

        let transformedstring = transformedcode.getunformatted();

        transformedcode = match processrs(&transformedstring) {
            Ok(node) => node,
            Err(errors) => {
                return Err(ParseError::RULEERROR(rule.name.clone(), errors, transformedstring));
                //this error is thrown if a previous transformation does
                //some weird syntactically wrong transformation
            }
        };

        //TODO this part can be improved. instead of reparsing the whole string
        //we modify rnode.finalizetransformation() such that in addition to doing
        //transformations it also deals with the character positions properly,
        //updating them in the new code for the minuses to work
        //removes unneeded and duplicate bindings
    }
    return Ok(transformedcode);
}

pub fn transformfile(rules: &Vec<Rule>, rustcode: String) -> Result<Rnode, ParseError> {

    let parsedrnode = processrs(&rustcode);
    let transformedcode: Rnode = match parsedrnode {
        Ok(node) => node,
        Err(errors) => {
            return Err(ParseError::TARGETERROR(errors, rustcode));
        }
    };
    //If this passes then The rnode has been parsed successfully

    return transformrnode(rules, transformedcode);
}
