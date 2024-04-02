// SPDX-License-Identifier: GPL-2.0

use std::{
    cmp::{max, min},
    collections::HashSet,
};

use itertools::Itertools;

use crate::{
    commons::{
        info::ParseError,
        util::{show_cfg, show_ctl_graph, workrnode},
    },
    ctl::ctl_ast::{GenericSubst, GenericWitnessTree},
    debugcocci,
    engine::{
        cocci_vs_rs::MetavarBinding,
        ctl_cocci::{processctl, BoundValue},
    },
    interface::interface::CoccinelleForRust,
    parsing_cocci::{
        ast0::{MetaVar, MetavarName, Snode},
        parse_cocci::Rule,
    },
    parsing_rs::{
        ast_rs::{Rcode, Rnode, Wrap},
        control_flow::asts_to_flow,
        parse_rs::processrs,
    },
};

use super::{cocci_vs_rs::Environment, ctl_cocci::CWitnessTree};

fn _tokenf<'a>(_node1: &'a Snode, _node2: &'a Rnode) -> Vec<MetavarBinding> {
    vec![]
}

fn copytornodewithenv(snode: Snode, env: &Environment) -> Rnode {
    if !snode.wrapper.metavar.isnotmeta() {
        if let Some(mvar) = env.bindings.iter().find(|x| x.metavarinfo.varname == snode.getstring())
        {
            let mut rnode = (*mvar.rnode).clone();
            let wsf = format!(" {}", rnode.wrapper.wspaces.0);
            rnode.wrapper.wspaces.0 = wsf;
            return rnode;
        } else {
            panic!("Metavariable should already be present in environment.");
        }
    }
    let kind = snode.kinds().clone();

    let wdummy = Wrap::dummy(snode.children.len());
    // if snode.children.len() == 0 {
    // let dat = snode.getstring().chars().into_iter().collect_vec();
    // if dat.len() == 1 && dat[0].is_ascii_punctuation() {
    // wdummy.wspaces.0 = String::new();
    // }
    // }
    let mut rnode = Rnode::new(wdummy, snode.asttoken, kind, vec![]);
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
        //println!("minuses - {:?}", env.modifiers.minuses.clone());
        for minus in env.modifiers.minuses.clone() {
            if pos == minus || pos.0 >= minus.0 && pos.1 <= minus.1 {
                x.wrapper.isremoved = true;
                //println!("Removed : {:?}", x);
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
            // eprintln!("Pluses - {:?} {:?} {:?}", pluspos, isbef, pluses);
            if pos.0 == pluspos && x.children.len() == 0 && isbef {
                x.wrapper.plussed.0 = snodetornode(pluses, env);
                // eprintln!("TESTIG bef {}", x.totoken());
                // eprintln!("======================== {:?}", x);
            } else if pos.1 == pluspos && x.children.len() == 0 && !isbef {
                x.wrapper.plussed.1 = snodetornode(pluses, env);
                // println!("TESTIG aft {}", x.totoken());
            } else if pluspos >= pos.0 && pluspos <= pos.1 {
                shouldgodeeper = true;
            }
        }
        return shouldgodeeper;
    };
    workrnode(node, transformmods);
}

fn _trimpatchbindings(
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

pub fn transformrnodes(rules: &Vec<Rule>, rnodes: Rcode, debug: bool) -> Result<Rcode, ParseError> {
    let mut transformed_code = rnodes;

    let savedbindings: Vec<Vec<MetavarBinding>> = vec![vec![]];
    for rule in rules {
        debugcocci!("Rule: {}, freevars: {:?}", rule.name, rule.freevars);
        debugcocci!("filtered bindings : {:?}", getfiltered(&rule.freevars, &savedbindings));
        // debugcocci!("Expanded bindings: {:?}", expandedbindings);
        let mut rnodes = transformed_code.0.into_iter().map(|x| vec![x]).collect_vec();
        let flows = asts_to_flow(&rnodes);
        let mut forests = vec![];
        flows.iter().for_each(|flow| {
            let triples = processctl(&rule.ctl, &flow, &vec![], debug);
            let forest = triples.into_iter().map(|(_, _, tree)| tree).collect_vec();
            forests.push(forest);
        });

        forests.into_iter().enumerate().for_each(|(i, forest)| {
            transformrnode(&forest, &mut rnodes[i][0]);
        });

        let transformedstring = rnodes.iter().fold(String::new(), |mut acc, rnode| {
            acc.push_str(&rnode[0].getunformatted());
            acc
        });

        transformed_code = match processrs(&transformedstring) {
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
        if debug {
            show_ctl_graph()
        }
    }
    return Ok(transformed_code);
}

pub fn transformfile(
    args: &CoccinelleForRust,
    rules: &Vec<Rule>,
    rustcode: String,
) -> Result<Rcode, ParseError> {
    let parsedrnode = processrs(&rustcode);
    let transformedcode = match parsedrnode {
        Ok(node) => node,
        Err(errors) => {
            return Err(ParseError::TARGETERROR(errors, rustcode));
        }
    };
    //If this passes then The rnode has been parsed successfully

    if args.show_cfg {
        let asts = &transformedcode.0.clone().into_iter().map(|x| vec![x]).collect_vec();
        let flows = asts_to_flow(asts);
        flows.into_iter().for_each(|flow| {
            show_cfg(&flow);
        })
    }

    if args.show_ctl {
        rules.iter().for_each(|rule| eprintln!("{}", rule.ctl));
    }

    return transformrnodes(rules, transformedcode, args.verbose_ctl_engine);
}

// fn transformrnode(trees: &Vec<Vec<CWitnessTree>>, rnode: &mut Rnode) {
//     eprintln!("transforming");
//     fn aux(wit: &CWitnessTree) -> Vec<Environment> {
//         eprintln!("wit - {:?}", wit);
//         let mut genvs = vec![];
//         let mut cenv = Environment::new();
//         match wit {
//             GenericWitnessTree::Wit(_state, subs, _, witforest) => {
//                 for sub in subs {
//                     match sub {
//                         GenericSubst::Subst(mvar, value) => match value {
//                             SubOrMod::Sub(node) => cenv.addbinding(MetavarBinding {
//                                 metavarinfo: mvar.clone(),
//                                 rnode: node.clone(),
//                                 neg: false,
//                             }),

//                             SubOrMod::Mod(_, modif) => {
//                                 cenv.modifiers.add_modifs(modif.clone());
//                             }
//                         },
//                         GenericSubst::NegSubst(_, _) => panic!(),
//                     }
//                 }

//                 genvs.push(cenv);
//                 if witforest.is_empty() {
//                 } else {
//                     eprintln!("forest - {:?}\n", witforest);
//                     for tree in witforest {
//                         eprintln!("tree - {:?}", tree);
//                         let envs = aux(tree);
//                         eprintln!("envs - {:?}", envs);
//                         //joining the envs
//                         genvs
//                             .iter_mut()
//                             .for_each(|genv| envs.iter().for_each(|env| genv.add(env.clone())));
//                     }
//                 }
//             }
//             GenericWitnessTree::NegWit(_) => {}
//         }
//         return genvs;
//     }

//     for tree in trees {
//         //tree is one of the changes
//         for wit in tree {
//             let envs = aux(wit);
//             eprintln!("env - {:?}", envs);
//             envs.into_iter().for_each(|env| {
//                 transform(rnode, &env);
//             });
//         }
//     }
// }

fn _display(pad: String, wit: CWitnessTree) {
    match wit {
        GenericWitnessTree::Wit(state, subs, _, witforest) => {
            eprintln!("{}{:?}", pad, state);
            eprintln!("{}{:?}", pad, subs);
            for wit in witforest {
                _display(format!("{}    ", pad), wit);
            }
        }
        GenericWitnessTree::NegWit(_) => todo!(),
    }
}

fn transformrnode(trees: &Vec<Vec<CWitnessTree>>, rnode: &mut Rnode) {
    // eprintln!("transforming");
    fn aux(wit: &CWitnessTree, mut envs: Vec<Environment>) -> Vec<Environment> {
        // eprintln!("Env - {:?}", envs);
        let mut genvs = vec![];
        let mut nge = vec![];
        let mut flag = None;
        match wit {
            GenericWitnessTree::Wit(_state, subs, _, witforest) => {
                for sub in subs {
                    match sub {
                        GenericSubst::Subst(mvar, value) => match value {
                            BoundValue::Sub(node) => {
                                flag = Some(true);
                                let mut cv = envs.clone();
                                cv.iter_mut().for_each(|cv| {
                                    cv.addbinding(MetavarBinding {
                                        metavarinfo: mvar.clone(),
                                        rnode: node.clone(),
                                        neg: false,
                                    })
                                });
                                genvs.extend(cv);
                            }

                            BoundValue::Mod(_, modif) => {
                                flag = Some(false);
                                envs.iter_mut().for_each(|env| {
                                    env.modifiers.add_modifs(modif.clone());
                                });
                            }
                            BoundValue::Label(_label) => {}
                        },
                        GenericSubst::NegSubst(_, _) => {}
                    }
                }

                assert!(flag.clone().unwrap() == (witforest.len() > 0));
                if flag.unwrap() {
                    for wit in witforest {
                        nge.extend(aux(wit, genvs.clone()));
                    }
                }
            }
            GenericWitnessTree::NegWit(_) => {}
        }

        if flag.is_none() {
            return envs;
        }

        if flag.unwrap() {
            return nge;
        }
        return envs;
    }

    for tree in trees {
        //tree is one of the changes
        // eprintln!("len -= {}", trees.len());
        for wit in tree {
            // display(String::from("   "), wit.clone());
            let envs = aux(wit, vec![Environment::new()]);
            envs.into_iter().for_each(|env| {
                transform(rnode, &env);
            });
        }
    }
}
