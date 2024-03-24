// SPDX-License-Identifier: GPL-2.0

use clap::Parser;
use coccinelleforrust::commons::info::ParseError::*;
use coccinelleforrust::commons::util::{attach_spaces_right, getstmtlist};
use coccinelleforrust::ctl::ctl_ast::{GenericSubst, GenericWitnessTree};
use coccinelleforrust::ctl::wrapper_ctl::make_ctl_simple;
use coccinelleforrust::engine::cocci_vs_rs::Environment;
use coccinelleforrust::engine::ctl_cocci::{processctl, CWitnessTree, BoundValue};
use coccinelleforrust::parsing_cocci::parse_cocci::processcocci;
use coccinelleforrust::parsing_rs::ast_rs::Rcode;
use coccinelleforrust::parsing_rs::control_flow::asts_to_flow;
use coccinelleforrust::parsing_rs::parse_rs::
    processrs
;
use coccinelleforrust::debugcocci;
use coccinelleforrust::{
    engine::cocci_vs_rs::MetavarBinding, engine::transformation,
    interface::interface::CoccinelleForRust, parsing_cocci::ast0::Snode, parsing_rs::ast_rs::Rnode,
};
use env_logger::{Builder, Env};
use itertools::{izip, Itertools};
use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};
use std::fs::{canonicalize, DirEntry};
use std::io;
use std::io::Write;
use std::process::{Command, Output};
use std::{fs, path::Path, process::exit};

#[allow(dead_code)]
fn tokenf<'a>(_node1: &'a Snode, _node2: &'a Rnode) -> Vec<MetavarBinding> {
    // this is
    // Tout will have the generic types in itself
    // ie  ('a * 'b) tout //Ocaml syntax
    // Should I replace Snode and Rnode with generic types?
    // transformation.ml's tokenf
    // info_to_fixpos
    vec![]
}

fn init_logger(args: &CoccinelleForRust) {
    let mut options = String::new();
    if args.debug {
        options.push_str(
            "
            coccinelleforrust::parsing_cocci,
            coccinelleforrust::commons,
            coccinelleforrust::engine
        ",
        );
    }
    let env = Env::default().default_filter_or(&options);

    Builder::from_env(env)
        .format(|buf, record| writeln!(buf, "{}: {}", record.level(), record.args()))
        .init();
}

pub fn adjustformat(node1: &mut Rnode, node2: &Rnode, mut line: Option<usize>) -> Option<usize> {
    // if line.is_some() {
        // eprintln!("{:?}", line);
        // eprintln!("{} here", node1.getunformatted());
    // }

    if node1.wrapper.wspaces.0.contains("/*COCCIVAR*/") {
        node1.wrapper.wspaces = node2.wrapper.wspaces.clone();
        line = Some(node1.wrapper.info.sline);
    }
    let mut prev_space = String::new();
    let mut preva = None;
    for (childa, childb) in izip!(&mut node1.children, &node2.children) {
        line.map(|sline| {
            //eprintln!("{}, {:?}=={:?}", sline, childa.getunformatted(), childb.getunformatted());
            if childa.wrapper.info.eline == sline {
                childa.wrapper.wspaces = childb.wrapper.wspaces.clone();
            }
            // else {
            //     line = None;
            // }
        });
        line = adjustformat(childa, &childb, line);
        if line.is_some() {
            if preva.is_some() {
                attach_spaces_right(preva.unwrap(), prev_space.clone());
                preva = None;
                prev_space = String::new();
            }
        } else {
            preva = Some(childa);
            prev_space = childb.get_spaces_right();
        }
    }

    return line;
}

/// Get the formatted contents and diff of a file
///
/// ## Arguments
///
///  - `cfr`: Configuration object containing arguments provided by the user
///  - `transformedcode`: Mutable reference to a node of modified Rust code
///  - `targetpath`: Output path of the file to be written
///
/// ## Return Value
///
/// This function returns a tuple of [`String`]s, which represent respectively
/// the formatted content of the file, and the delta or 'diff' resulting from
/// the file prior to modification.
fn getformattedfile(
    cfr: &CoccinelleForRust,
    transformedcode: &mut Rcode,
    targetpath: &str,
) -> (String, String) {
    //eprintln!("Dealing with - {}", targetpath);

    let tp = std::path::Path::new(targetpath);
    let parent = tp.parent().unwrap_or(std::path::Path::new("/tmp"));

    //-let randrustfile = format!("{}/tmp{}.rs", parent.display(), rng.gen::<u32>());
    let dirpath = parent.to_str().expect("Cannot get directory");
    let randfile =
        tempfile::Builder::new().tempfile_in(dirpath).expect("Cannot create temporary file.");
    let mut randrustfile = randfile.path().to_str().expect("Cannot get temporary file.");

    // In all cases, write the transformed code to a file so we can diff
    //VERY IMPORTANT :-
    //CHECK TO REMOVE THIS FILE FOR ALL ERROR CASES
    transformedcode.writetotmpnamedfile(&randrustfile);
    debugcocci!(
        (|| {
            fs::write("/tmp/tmp_CFR_COCCI.rs", transformedcode.getunformatted())
                .expect("Failed to write to tmp");
        })
    );
    // Now, optionally, we may want to not rust-format the code.
    if !cfr.suppress_formatting {
        //should never be disabled except for debug
        //let original = fs::read_to_string(&targetpath).expect("Unable to read file");

        // Depending on whether the user provided a `rustfmt` config file or not,
        // add it to the invokation.
        // As it turns out, argument order for rustfmt does not matter, you can
        // add the configuration file later and it is still accounted for when
        // parsing files provided before.

        // Core command is in a separate binding so it stays alive. The others
        // are just references to it.

        let output: Output;
        let mut core_command = Command::new("rustfmt");
        if let Some(fmtconfig_path) = &cfr.rustfmt_config {
            let fmtconfp = format!("--config-path {}", fmtconfig_path.as_str());
            output = core_command
                .arg(&randrustfile)
                .arg("--edition")
                .arg("2021")
                .arg(fmtconfp)
                .output()
                .expect("rustfmt failed");
        } else {
            output = core_command
                .arg(&randrustfile)
                .arg("--edition")
                .arg("2021")
                .output()
                .expect("rustfmt failed");
        }

        if !output.status.success() {
            if cfr.show_fmt_errors {
                eprint!(
                    "RUSTFMT ERR - {}",
                    String::from_utf8(output.stderr).unwrap_or(String::from("NONE"))
                );
            }
        } {
            // let s = fs::read_to_string(&randrustfile);
            // eprintln!("wjere = {}", s.unwrap());
        }
        //if let Some(fmtconfig_path) = &cfr.rustfmt_config {
        //  fcommand = fcommand.arg("--config-path").arg(fmtconfig_path.as_str());
        //}

        //if fcommand.spawn().expect("rustfmt failed").wait().is_err() {
        //  eprintln!("Formatting failed.");
        //}
        let formattednode =
            match processrs(&fs::read_to_string(&randrustfile).expect("Could not read")) {
                Ok(rnode) => rnode,
                Err(_) => {
                    panic!("Cannot parse temporary file.");
                }
            };
        //let formattednode =
        //  processrs(&fs::read_to_string(&randrustfile).expect("Could not read")).unwrap();

        // eprintln!("Formatted - {}", formattednode.getunformatted());
        transformedcode.0.iter_mut().enumerate().for_each(|(i, rnode)| {
            adjustformat(rnode, &formattednode.0[i], None);
        });
        randrustfile = randfile.path().to_str().expect("Cannot get temporary file.");
        transformedcode.writetotmpnamedfile(&randrustfile);
    }

    let diffed = if !cfr.suppress_diff {
        let diffout = Command::new("diff")
            .arg("-u")
            .arg("--text")
            .arg(targetpath)
            .arg(&randrustfile)
            .output()
            .expect("diff failed");

        String::from_utf8(diffout.stdout).expect("Bad diff")
    } else {
        String::new()
    };

    let formatted = fs::read_to_string(&randrustfile).expect("Unable to read file");

    (formatted, diffed)
}

fn showdiff(
    args: &CoccinelleForRust,
    transformedcode: &mut Rcode,
    targetpath: &str,
    hasstars: bool,
) {
    let (data, diff) = getformattedfile(&args, transformedcode, &targetpath);
    if !hasstars {
        if !args.suppress_diff {
            if !diff.is_empty() {
                println!("{}", diff);
            }
        }

        if args.apply {
            fs::write(targetpath, data).expect("Unable to write")
        } else {
            if let Some(outputfile) = &args.output {
                if let Err(written) = fs::write(outputfile, data) {
                    eprintln!("Error in writing file.\n{:?}", written);
                }
            }
        }
    } else {
        println!("Code highlighted with *");
        for line in diff.split("\n").collect_vec() {
            if line.len() != 0 && line.chars().next().unwrap() == '-' {
                println!("*{}", &line[1..]);
            } else {
                println!("{}", line)
            }
        }
    }
}

fn transformfiles(args: &CoccinelleForRust, files: &[String]) {
    let patchstring = fs::read_to_string(&args.coccifile).expect("Could not read file.");
    // let (_, needsti, _) = processcocci(&patchstring);

    if true {
        let transform = |targetpath: &String| {
            //eprintln!("Processing {}", targetpath);
            let (rules, _, hasstars) = processcocci(&patchstring);
            //Currently have to parse cocci again because Rule has SyntaxNode which which has
            //rowan `NonNull<rowan::cursor::NodeData>` which cannot be shared between threads safely
            // let files_tmp = do_get_files(&args, &args.targetpath, &rules);
            // eprintln!("{:?}", files_tmp);
            // rules[0].patch.minus.print_tree();
            let rcode = fs::read_to_string(&targetpath)
                .expect(&format!("{} {}", "Could not read file", targetpath));
            let transformedcode = transformation::transformfile(args, &rules, rcode);
            let mut transformedcode = match transformedcode {
                Ok(node) => node,
                Err(error) => {
                    //failedfiles.push((error, targetpath));
                    match error {
                        TARGETERROR(msg, _) => eprintln!("{}", msg),
                        RULEERROR(msg, error, _) => {
                            println!("Transformation Error at rule {} : {}", msg, error)
                        }
                    }
                    println!("Failed to transform {}", targetpath);
                    return;
                }
            };
            showdiff(args, &mut transformedcode, targetpath, hasstars);
        };

        if !args.no_parallel {
            files.par_iter().for_each(transform);
        } else {
            files.iter().for_each(transform);
        }
    } else {
        // if files.len() == 0 {
        //     return;
        // }

        // let (host, vfs) = gettypedb(&files[0]);
        // let db = host.raw_database();
        // //let semantics = &mut Semantics::new(db);
        // let semantics = &Semantics::new(db);

        // let transform = |targetpath: &String| {
        //     let (rules, _needsti, hasstars) = processcocci(&patchstring);
        //     let fileid = vfs
        //         .file_id(&VfsPath::new_real_path(targetpath.clone()))
        //         .expect(&format!("Could not get FileId for file {}", &targetpath));
        //     let syntaxnode = semantics.parse_or_expand(fileid.into());
        //     let rcode = fs::read_to_string(targetpath).expect("Could not read file");

        //     let mut rnode = processrswithsemantics(&rcode, syntaxnode)
        //         .expect("Could not convert SyntaxNode to Rnode");

        //     set_types(&mut rnode, semantics, db);

        //     let transformedcode = transformation::transformrnodes(&rules, rnode);

        //     let mut transformedcode = match transformedcode {
        //         Ok(node) => node,
        //         Err(error) => {
        //             //failedfiles.push((error, targetpath));
        //             match error {
        //                 TARGETERROR(msg, _) => eprintln!("{}", msg),
        //                 RULEERROR(msg, error, _) => eprintln!("{}:{}", msg, error),
        //             }
        //             println!("Failed to transform {}", targetpath);
        //             return;
        //         }
        //     };

        //     showdiff(args, &mut transformedcode, targetpath, hasstars);
        //     //transformrnode(&rules, rnode);
        // };

        // if !args.no_parallel {
        //     todo!("Parallel for type inference has not been implemented.");
        //     //files.par_iter().for_each(transform);
        // } else {
        //     files.iter().for_each(transform);
        // }
    };
}

fn makechecks(args: &CoccinelleForRust) {
    if !Path::new(args.targetpath.as_str()).exists() {
        eprintln!("Target file/path does not exist.");
        exit(1);
    }

    if !Path::new(args.coccifile.as_str()).exists() {
        eprintln!("Semantic file/path does not exist.");
        exit(1);
    }
}

#[allow(dead_code)]
fn findfmtconfig(args: &mut CoccinelleForRust) {
    let height_lim: usize = 5;

    let mut target = Path::new(args.targetpath.as_str()).parent().unwrap().to_path_buf();
    for _ in 0..height_lim {
        let paths = fs::read_dir(target.to_str().unwrap())
            .unwrap()
            .into_iter()
            .filter(|x| x.is_ok())
            .map(|x| x.unwrap().path().to_str().unwrap().to_string())
            .collect_vec();
        let path = paths.into_iter().find(|x| x.ends_with("rustfmt.toml"));
        if let Some(path) = path {
            args.rustfmt_config = Some(path);
            break;
        } else {
            target = target.join("../");
        }
    }
}

// one possible implementation of walking a directory only visiting files
fn visit_dirs(dir: &Path, ignore: &str, cb: &mut dyn FnMut(&DirEntry)) -> io::Result<()> {
    if dir.is_dir() && (ignore == "" || dir.to_str().is_some_and(|x| !x.contains(ignore))) {
        for entry in fs::read_dir(dir)? {
            let entry = entry?;
            let path = entry.path();
            if path.is_dir() {
                visit_dirs(&path, ignore, cb)?;
            } else {
                cb(&entry);
            }
        }
    }
    Ok(())
}

// fn transform_prog(tree: CWitnessTree, rnode: &mut Rnode) {
//     // let bindings = vec![];
//     fn aux(tree: &CWitnessTree, mut env: Environment) -> (Environment, Vec<Modifiers>) {
//         match tree {
//             GenericWitnessTree::Wit(noden, subst, _, rtree) => {
//                 let mut mods = vec![];
//                 let mut mbindings = vec![];

//                 for m in subst {
//                     match m {
//                         GenericSubst::Subst(mvar, val) => match val {
//                             SubOrMod::Sub(rnode) => {
//                                 mbindings.push(MetavarBinding::from_subs(
//                                     mvar.clone(),
//                                     rnode.clone(),
//                                     false,
//                                 ));
//                                 //rnode here is an Rc<> so only the reference is copied
//                             }
//                             SubOrMod::Mod(snodes, modifs) => mods.push(modifs),
//                         },
//                         GenericSubst::NegSubst(mvar, val) => match val {
//                             SubOrMod::Sub(rnode) => mbindings.push(MetavarBinding::from_subs(
//                                 mvar.clone(),
//                                 rnode.clone(),
//                                 true,
//                             )),
//                             SubOrMod::Mod(snodes, modifs) => {
//                                 panic!("There shouldnt be mods in NegSubst")
//                             }
//                         },
//                     }
//                 }
//                 if mbindings.len() != 0 {
//                     assert_eq!(mods.len(), 0);

//                     env.addbindings(&mbindings.iter().collect_vec());
//                     todo!()
//                 } else {
//                     panic!("Should not come here");
//                 }
//             }
//             GenericWitnessTree::NegWit(wit) => aux(wit, env),
//         }
//     }

//     // let bindings =
// }

fn transform(trees: &Vec<Vec<CWitnessTree>>, rnode: &mut Rnode) {
    fn aux(wit: &CWitnessTree) -> Vec<Environment> {
        let mut genvs = vec![];
        let mut cenv = Environment::new();
        match wit {
            GenericWitnessTree::Wit(_state, subs, _, witforest) => {
                for sub in subs {
                    match sub {
                        GenericSubst::Subst(mvar, value) => match value {
                            BoundValue::Sub(node) => cenv.addbinding(MetavarBinding {
                                metavarinfo: mvar.clone(),
                                rnode: node.clone(),
                                neg: false,
                            }),

                            BoundValue::Mod(_, modif) => {
                                cenv.modifiers.add_modifs(modif.clone());
                            }
                        },
                        GenericSubst::NegSubst(_, _) => panic!(),
                    }
                }

                if witforest.is_empty() {
                    genvs.push(cenv);
                } else {
                    for tree in witforest {
                        let envs = aux(tree);
                        //joining the envs
                        envs.into_iter().for_each(|env| {
                            let mut cenv = cenv.clone();
                            cenv.add(env);
                            genvs.push(cenv);
                        })
                    }
                }
            }
            GenericWitnessTree::NegWit(_) => {}
        }
        return genvs;
    }

    for tree in trees {
        //tree is one of the changes
        for wit in tree {
            let envs = aux(wit);
            envs.into_iter().for_each(|env| {
                transformation::transform(rnode, &env);
            });
        }
    }
}

// fn transform(trees: &Vec<Vec<CWitnessTree>>, rnode: &mut Rnode) {
//     let mut modifiers = Modifiers { pluses: vec![], minuses: vec![] };
//     let mut env = Environment::new();

//     fn aux(wits: &Vec<CWitnessTree>) -> Vec<Environment> {
//         for wit in wits {
//             let mut env = Environment::new();
//             match wit {
//                 GenericWitnessTree::Wit(node, subs, _, wit) => {
//                     for sub in subs {
//                         match sub {
//                             GenericSubst::Subst(mvar, val) => match val {
//                                 SubOrMod::Sub(sub) => {
//                                     env.addbinding(MetavarBinding {
//                                         metavarinfo: mvar.clone(),
//                                         rnode: sub.clone(),
//                                         neg: false,
//                                     });
//                                 }
//                                 SubOrMod::Mod(_, modif) => {
//                                     //once modifiers are reached, there are no
//                                     //more substitutions after that
//                                     //Should I put an assertion
//                                     env.modifiers.add_modifs(modif.clone());
//                                 }
//                             },
//                             GenericSubst::NegSubst(_, _) => {
//                                 panic!(
//                                     "Negative Subs here has no meaning because we are transforming"
//                                 )
//                             }
//                         }
//                         let nenv = aux(wit);
//                         env.add(nenv);
//                     }
//                     return env;
//                 }
//                 GenericWitnessTree::NegWit(_) => {
//                     panic!("It does not make sense for the last witness to have negative substitutions")
//                 }
//             }
//         }
//         todo!()
//     }

//     for tree in trees {
//         //tree is one of the changes
//         for wit in tree {
//             let env = aux(wit);
//         }
//     }
// }

// fn transform_old(trees: &Vec<Vec<CWitnessTree>>, rnode: &mut Rnode) {
//     for tree in trees {
//         //tree is one of the changes
//         for wit in tree {
//             match wit {
//                 GenericWitnessTree::Wit(_, wits, _, _) => {
//                     for wit in wits {
//                         match wit {
//                             GenericSubst::Subst(mvar, subs) => match subs {
//                                 SubOrMod::Sub(_) => panic!(
//                                     "I do not have the strength today to implement substitutions"
//                                 ),
//                                 SubOrMod::Mod(_, mods) => {
//                                     let mut env = Environment::new();
//                                     env.modifiers = mods.clone();
//                                     transformation::transform(rnode, &env);
//                                 }
//                             },
//                             GenericSubst::NegSubst(_, _) => todo!(),
//                         }
//                     }
//                 }
//                 GenericWitnessTree::NegWit(_) => todo!(),
//             }
//         }
//     }
// }

fn _run_test(_args: &CoccinelleForRust) {
    // let contents = fs::read_to_string(&args.coccifile).unwrap();
    // let mut snodes = getstmtlist(&processcocci(&contents).0.remove(0).patch.minus).clone().children;
    // let st = snodes.clone();
    // // eprintln!("{:?}", snode.kind());
    // let s1 = snodes.remove(0);
    // let s2 = s1.clone();
    // // let s2 = snodes.remove(0);
    // // let arg = args.dots.split("...");
    // // let s = arg.collect_vec();
    // // let (s1, s2) = (s[0], s[1]);
    // // let s1 = vec![];
    // // let s2 = vec![];

    // // let s1 = parse_stmts_snode(s1);
    // // let s2 = parse_stmts_snode(s2);
    // // s1_ & AX A[ !(s1 V s2) U s2]
    // let p1_modif = GeneircCtl::Pred(Predicate::Match(s1.clone(), Modif::<Snode>::Modif(s1.clone())));
    // let p2_modif = C![Pred, Predicate::Match(s2.clone(), Modif::<Snode>::Modif(s2.clone()))];
    // let p1_unmodif = C![Pred, Predicate::Match(s1.clone(), Modif::<Snode>::Control)];
    // let p2_unmodif = C![Pred, Predicate::Match(s2.clone(), Modif::<Snode>::Control)];
    // let e1 = GenericCtl::Exists(true, MetavarName::create_v(), Box::new(p1_modif.clone()));
    // // let e1 = p1_modif.clone();
    // // let e2 = GenericCtl::Exists(true, MetavarName::create_pv(), Box::new(p2.clone()));
    // // let e1 = p1.clone();
    // let e2 = p2_unmodif.clone();

    // // let f1 = GenericCtl::And(Strict, (Box::new(p1.clone()), Box::new(p2.clone())));
    // let yy1 = if s1.wrapper.is_modded {
    //     eprintln!("modif");
    //     p1_modif.clone()
    // } else {
    //     p1_modif.clone()
    // };

    // let yy2 = GenericCtl::Exists(true, MetavarName::create_v(), Box::new(p2_modif.clone()));
    // let t0 = GenericCtl::Or(Box::new(yy1), Box::new(p2_unmodif.clone()));
    // let t1 = C![Not, t0.clone()];
    // // let t1 = GenericCtl::Exists(true, MetavarName::create_v(), Box::new(t1.clone()));
    // // let ctl = C![AU, Direction::Forward, Strict::Strict, C![Pred, p1], C![Pred, p2]];
    // let t2 = C![AU, Forward, Strict, t1.clone(), yy2];
    // // let t2 = C![AU, Forward, Strict, t1.clone(), p2_unmodif.clone()];
    // let t3 = GenericCtl::AX(Forward, Strict, Box::new(t2.clone()));
    // let t4 = GenericCtl::And(Strict, Box::new(e1.clone()), Box::new(t3.clone()));
    // let t5 = GenericCtl::Exists(true, MetavarName::create_v(), Box::new(t4.clone()));

    // let rfile = fs::read_to_string(&args.targetpath).unwrap();
    // let mut rnode = processrs_old(&rfile).unwrap();
    // let mut rnodes = vec![rnode];
    // let flow = ast_to_flow(&rnodes);

    // if args.show_cfg {
    //     show_cfg(&flow);
    // }

    // if args.show_ctl {
    //     let a = make_ctl_simple(st);
    //     eprintln!("CTL - {}", a);
    // }
    // // make_graphviz(&flow, "/home/troy/tmp/tmp.gviz");
    // // flow.nodes().iter().for_each(|x| {
    // //     if !flow.node(*x).data().is_dummy() {
    // //         eprint!(
    // //             "{}:{:?} - {:?}",
    // //             x.0,
    // //             flow.node(*x).data().rnode().kind(),
    // //             flow.node(*x).data().rnode().getstring()
    // //         );
    // //     } else {
    // //         eprint!("{} - DummyNode", x.0);
    // //     }

    // //     eprintln!(" : succs - {:?} | preds - {:?}", flow.successors(*x), flow.predecessors(*x));
    // // });

    // let res = processctl(&t4, &flow, &vec![]);
    // if res.len() > 0 {
    //     res.iter().for_each(|(x, _, witf)| {
    //         if flow.node(*x).data().is_dummy() {
    //             eprintln!("{} -> dummy", x.to_usize());
    //             return;
    //         }
    //         eprintln!("witf - {:?}", witf);
    //         eprintln!("{} -> {}", x.to_usize(), flow.node(*x).data().rnode().getstring())
    //     });
    // }
    // let trees = res.into_iter().map(|(_, _, wit)| wit).collect_vec();
    // transform(trees, &mut rnodes[0]);
    // // eprintln!("transformed - {}", rnodes[0].getstring());
    // showdiff(args, &mut rnodes[0], &args.targetpath, false);
    // // let _ = res.iter().map(|(x, _, _)| {
    // //     eprintln!("{} -> {:?}", x.to_usize(), flow.node(*x).data().rnode().getstring());
    // // });
}

fn run(args: &CoccinelleForRust) {
    let contents = fs::read_to_string(&args.coccifile).unwrap();
    let rules = processcocci(&contents).0;
    let snode = if rules.len() > 1 { todo!() } else { getstmtlist(&rules[0].patch.minus) };
    // let mut snodes = getstmtlist(&processcocci(&contents).0.remove(0).patch.minus).clone().children;
    // let st = snodes.clone();

    let rfile = fs::read_to_string(&args.targetpath).unwrap();
    let rnodes = processrs(&rfile).unwrap();

    //Notice how we use vec![x] to wrap each function
    let mut rnodes = rnodes.0.into_iter().map(|x| vec![x]).collect_vec();

    // let rnodes = rnodes.into_iter()
    let flows = asts_to_flow(&rnodes);

    let a = make_ctl_simple(snode, false);

    if args.show_cfg {
        coccinelleforrust::commons::util::show_cfg(&flows[0]);
    }

    if args.show_ctl {
        eprintln!("CTL - {}", a);
    }

    let mut trees = vec![];
    for flow in flows.iter() {
        let res = processctl(&a, flow, &vec![]);
        eprintln!("Churno - {:?}", res);
        trees.push(res.into_iter().map(|(_, _, tree)| tree).collect_vec());
    }

    for (i, tree) in trees.iter().enumerate() {
        eprintln!("TREE - {:#?}", tree);
        transform(tree, &mut rnodes[i][0]);
    }

    for rnode in rnodes {
        eprintln!("{}", rnode[0].getstring());
    }
    // make_graphviz(&flow, "/home/troy/tmp/tmp.gviz");
}

fn main() {
    let args = CoccinelleForRust::parse();
    init_logger(&args);

    if args.dots.is_some() {
        run(&args);
        exit(1);
    }

    makechecks(&args);

    let targetpath = Path::new(&args.targetpath);
    if targetpath.is_file() {
        transformfiles(&args, &[String::from(canonicalize(targetpath).unwrap().to_str().unwrap())]);
    } else {
        let mut files = vec![];
        let _ = visit_dirs(targetpath, &args.ignore, &mut |f: &DirEntry| {
            if f.file_name().to_str().unwrap().ends_with(".rs") {
                files.push(String::from(canonicalize(f.path()).unwrap().to_str().unwrap()));
            }
        });
        transformfiles(&args, &files[..]);
    }
}
