// SPDX-License-Identifier: GPL-2.0

use core::panic;
/// Parse a Single .cocci file
/// Structure supported as of now
/// @ rulename (depends on bool_exp)? @
/// metavars(exp and id)
/// .
/// .
/// .
/// @@
///
/// _context_
/// (+/-) code
use std::{collections::HashSet, rc::Rc, vec};

use ra_parser::SyntaxKind;

use super::ast0::{wrap_root, Mcodekind, MetaVar, MetavarName, Snode};
use crate::{
    commons::{
        info::{COCCI_DISJ_NAME, WILDCARD},
        util::{self, attach_pluses_back, attach_pluses_front, collecttree, worksnode, },
    },
    ctl::{
        ctl_ast::{GenericCtl, GenericSubst},
        ctl_engine::{Pred, Subs},
        wrapper_ctl::make_ctl_simple,
    },
    debugcocci,
    engine::ctl_cocci::{BoundValue, Predicate},
    parsing_cocci::ast0::MetavarType,
    syntaxerror,
};

type Name = String;

#[derive(Debug, Clone)]
pub enum Dep {
    NoDep,
    FailDep,
    Dep(Name),
    AndDep(Box<(Dep, Dep)>),
    OrDep(Box<(Dep, Dep)>),
    AntiDep(Box<Dep>),
}

fn getrule<'a>(rules: &'a Vec<Rule>, rulename: &str, lino: usize) -> &'a Rule {
    for rule in rules {
        if rule.name.eq(rulename) {
            return rule;
        }
    }
    syntaxerror!(lino, "no such rule", rulename);
}

/// Given a metavar type and name, returns a MetaVar object
fn makemetavar(
    rules: &Vec<Rule>,
    rulename: &Name,
    varname: &Name,
    metatype: &MetavarType,
    lino: usize,
) -> MetaVar {
    let split = varname.split(".").collect::<Vec<&str>>();
    match (split.get(0), split.get(1), split.get(2)) {
        (Some(var), None, None) => {
            debugcocci!("Added Metavar {}.{}", rulename, var);
            MetaVar::new(rulename, var, metatype, false)
                .unwrap_or_else(|| syntaxerror!(lino, "Unexpected Metavariable type"))
        }
        (Some(rulen), Some(var), None) => {
            //Inherited Metavars
            let var = *var;
            let rule = getrule(rules, &rulen, lino);
            if let Some(mvar) = rule.metavars.iter().find(|x| x.getname() == var) {
                if let Some(minfo) = rule.unusedmetavars.iter().find(|x| x.getname() == var) {
                    syntaxerror!(
                        lino,
                        format!(
                            "Metavariable {} is unused un rule {}",
                            minfo.getname(),
                            minfo.getrulename()
                        ),
                        varname
                    );
                }
                debugcocci!("Added Metavar {}.{}", mvar.getrulename(), mvar.getname());
                let inhertedvar = mvar.makeinherited();
                return inhertedvar;
            } else {
                syntaxerror!(lino, format!("No such metavariable in rule {}", rule.name), varname)
            }
        }
        _ => syntaxerror!(lino, "Invalid meta-variable name", varname),
    }
}

#[derive(Clone)]
pub struct Patch {
    pub minus: Snode,
    pub plus: Snode,
}

impl Patch {
    // In many cases Dots need to be represented by an ident
    // and not a comment, so this does that 
    pub fn fix_dots(&mut self) {
        let f = &mut |node: &mut Snode, _| {
            if node.has_kind(&SyntaxKind::TUPLE_EXPR) && node.children[1].is_dots { //TupleKind always has atleast two children because of the Parens
                node.change_kinds(&[SyntaxKind::PAREN_EXPR]);
            }
        };
        
        worksnode(&mut self.minus, (), f);
        worksnode(&mut self.plus, (), f);
    }

    fn setmetavars(&mut self, metavars: &Vec<MetaVar>) {
        fn setmetavars_aux(node: &mut Snode, metavars: &Vec<MetaVar>) {
            let mut freevars: Vec<MetaVar> = metavars.clone();
            let mut work = |node: &mut Snode| {
                //The if statement below lists the types of metavariables allowed
                if node.isexpr()
                    || node.istype()
                    || node.isid()
                    || node.islifetime()
                    || node.isparam()
                {
                    let stmp = node.getstring(); //FIX ME should not convert to string before checking
                    if let Some(mvar) = metavars.iter().find(|x| x.getname() == stmp) {
                        debugcocci!("MetaVar found - {:?}", mvar);
                        node.wrapper.metavar = mvar.clone();

                        if let Some(ind) = freevars.iter().position(|y| y == mvar) {
                            node.wrapper.freevars = freevars.clone();
                            freevars.remove(ind);
                            return;
                        }
                    }
                }

                node.wrapper.freevars = freevars.clone();
            };
            util::worktree(node, &mut work);
        }

        setmetavars_aux(&mut self.plus, metavars);
        setmetavars_aux(&mut self.minus, metavars);
    }

    fn setminus(&mut self) {
        let mut tagmods =
            |node: &mut Snode, (lino, modifier): (usize, Mcodekind)| -> (usize, Mcodekind) {
                let (start, end) = node.wrapper.getlinenos();

                match node.wrapper.mcodekind {
                    Mcodekind::Context(_, _) => {
                        if lino == 0 {
                            return (0, Mcodekind::Context(vec![], vec![]));
                        } else if start == lino && start == end {
                            //debugstart
                            if node.children.len() == 0 {
                                debugcocci!(
                                    "Setting {}:{:?} to modifier:- {:?}",
                                    node.getstring(),
                                    node.kinds(),
                                    modifier
                                );
                            } //debugend

                            node.wrapper.is_modded = true;
                            node.wrapper.mcodekind = modifier.clone();
                            return (lino, modifier);
                            //everytime lino is not 0, modkind is
                            //a Some value
                        } else if start == lino && start != end {
                            //this node spills onto the next line
                            node.wrapper.is_modded = true;
                            return (lino, modifier.clone());
                        }
                        return (0, Mcodekind::Context(vec![], vec![]));
                    }
                    Mcodekind::Plus | Mcodekind::Minus(_) | Mcodekind::Star => {
                        //println!("NODE - {}, {}", node.getstring());
                        if start == end {
                            //debugstart
                            if node.children.len() == 0 {
                                debugcocci!(
                                    "Setting {}:{:?} to modifier:- {:?}",
                                    node.getstring(),
                                    node.kinds(),
                                    modifier
                                );
                            } //debugend

                            node.wrapper.is_modded = true;
                            //already marked pre mod setting
                            //node.wrapper.mcodekind = modifier.clone();
                            return (start, node.wrapper.mcodekind.clone());
                        } else {
                            let tmpmod = node.wrapper.mcodekind.clone();
                            node.wrapper.mcodekind = Mcodekind::Context(vec![], vec![]);
                            return (start, tmpmod);
                        }
                    }
                }
            };

        worksnode(&mut self.plus, (0, Mcodekind::Context(vec![], vec![])), &mut tagmods);
        worksnode(&mut self.minus, (0, Mcodekind::Context(vec![], vec![])), &mut tagmods);
    }

    pub fn group_dots(&mut self) {
        self.minus = group_dots(&self.minus);
    }

    pub fn process_dots(&mut self) {
        process_dots_plus(&mut self.minus);
    }

    //remove let from around the type
    pub fn striplet(&mut self, hastype: bool) {
        if !hastype {
            return;
        }

        fn striplet_aux(node: &mut Snode) {
            //at this point node is a SourceFile
            //with a function with a stmtlist without braces
            let stmtlist = &mut node.children[3]; //function
            if stmtlist.children.len() == 0 {
                //handles empty type patches
                //Either no type or only minus
                return;
            }
            stmtlist.children = vec![stmtlist.children[0] //letstmt
                .children[3]
                .clone()] //Type;
        }
        striplet_aux(&mut self.plus);
        striplet_aux(&mut self.minus);
    }

    // pub fn tag_plus(&mut self) {
    //     let mut achildren = self.minus.into_preorder().iter();
    //     let mut bchildren = self.plus.into_preorder().iter();
    //     let mut a = achildren.next();
    //     let mut b = bchildren.next();
    //     let mut pvec = vec![];

    //     loop {
    //         match (a, b) {
    //             (Some(ak), Some(bk)) => {
    //                 match (ak.wrapper.mcodekind, bk.wrapper.mcodekind) {
    //                     (_, Mcodekind::Plus) => {
    //                         pvec.push((*bk).clone());
    //                         b = bchildren.next();
    //                     }
    //                     (Mcodekind::Minus(_), _) => {
    //                         attach_pluses_front(*ak, pvec);
    //                         pvec = vec![];
    //                         a = achildren.next();
    //                     }
    //                     (Mcodekind::Context(_, _), Mcodekind::Context(_, _)) => {
    //                         if ak.wrapper.isdisj {
    //                             ak.wrapper.mcodekind.push_pluses_front(pvec);
    //                         }
    //                     }
    //                 }
    //             }
    //         }
    //     }
    // }

    pub fn tag_plus(&mut self) {
        fn tagplus_aux(achildren1: Vec<&mut Snode>, bchildren1: Vec<&mut Snode>) -> Vec<Snode> {
            //There is no need to propagate pluses
            //because a plus cannot exist without code around it
            //when a '+' mod is written an ast is pushed at that
            //very level in the tree. That is I cannot write a plus
            //statement after a minus or context code and not have it
            //in a level same as the statement above it even around braces
            let mut pvec: Vec<Snode> = vec![];
            let mut achildren = achildren1.into_iter();
            let mut bchildren = bchildren1.into_iter();
            let mut a = achildren.next();
            let mut b = bchildren.next();
            loop {
                // eprintln!("{:?} {:?}", a, b);
                match (&mut a, &b) {
                    (Some(ak), Some(bk)) => {
                        match (&ak.wrapper.mcodekind, &bk.wrapper.mcodekind) {
                            (Mcodekind::Minus(_), _) => {
                                //minus code
                                //with any thing other than a plus
                                // eprintln!("Comes with {:?}", pvec);

                                // pvec should be empty. because if plus is persent
                                // before minus the minus is consumed before
                                // the plus is encountered
                                assert_eq!(pvec.len(), 0);

                                // attach_pluses_front(ak, pvec);
                                // pvec = vec![];
                                a = achildren.next();
                            }
                            (_, Mcodekind::Plus) => {
                                pvec.push((*bk).clone());
                                b = bchildren.next();
                            }
                            (Mcodekind::Context(_, _), Mcodekind::Context(_, _)) => {
                                //context code
                                //with context code
                                // if ak.wrapper.isdisj {
                                //     //DISJUNCTIONS ARE THE ONLY PART
                                //     //WHERE PLUSES ARE ADDED TO A NODE
                                //     //AND NOT A TOKEN
                                //     ak.wrapper.mcodekind.push_pluses_front(pvec);
                                //     //ak.wrapper.plusesbef.extend(pvec);
                                // } else {

                                attach_pluses_front(ak, pvec);

                                pvec = vec![];
                                a = achildren.next();
                                b = bchildren.next();
                            }
                            (Mcodekind::Star, Mcodekind::Star) => {
                                a = achildren.next();
                                b = bchildren.next();
                            }
                            (Mcodekind::Star, _) | (_, Mcodekind::Star) => {
                                panic!("Minus and Plus buffers do not have matching stars");
                            }
                            _ => {
                                panic!("There are plusses in the minus buffer, or minuses in the plus buffer.");
                            }
                        }
                    }
                    (None, Some(bk)) => match bk.wrapper.mcodekind {
                        Mcodekind::Plus => {
                            pvec.push((*bk).clone());
                            b = bchildren.next();
                        }
                        _ => {
                            break;
                        }
                    },
                    (Some(_), None) => {
                        break;
                    } //means only minuses are left
                    (None, None) => {
                        break;
                    }
                }
            }
        return pvec;
        }

        let v1 = self.minus.into_preorder();
        let v2 = self.plus.into_preorder();
        // eprintln!("v1 - {:?}\nv2 - {:?}", v1.iter().map(|x| x.getstring()).join(" "), v2.iter().map(|x| x.getstring()).join(" "));
        let pvec = tagplus_aux(v1, v2);

        if pvec.len() != 0 {
            //Plus statements exist after
            //the context and need to be attached to the
            //closes context above/before
            attach_pluses_back(&mut self.minus, pvec);
        }
    }

    pub fn getunusedmetavars(&self, mut bindings: Vec<MetaVar>) -> Vec<MetaVar> {
        let mut f = |x: &Snode| match &x.wrapper.metavar {
            MetaVar::NoMeta => {}
            MetaVar::Exp(info)
            | MetaVar::Id(info)
            | MetaVar::Lifetime(info)
            | MetaVar::Type(info)
            | MetaVar::Parameter(info)
            | MetaVar::Adt(_, info) => {
                if let Some(index) =
                    bindings.iter().position(|node| node.getname() == info.0.varname)
                //only varname is checked because a rule cannot have two metavars with same name but
                //different rulenames
                {
                    //this removes the metavaraible from the list of unused vars
                    //when encountered
                    bindings.remove(index);
                };
            }
        };

        collecttree(&self.minus, &mut f);
        collecttree(&self.plus, &mut f);
        debugcocci!("Unused Metavars:- {:?}", bindings);
        return bindings;
    }
}

#[derive(Clone)]
pub struct Rule {
    pub name: Name,
    pub dependson: Dep,
    pub metavars: Vec<MetaVar>,
    pub unusedmetavars: Vec<MetaVar>,
    pub patch: Patch,
    pub freevars: Vec<MetaVar>,
    pub usedafter: HashSet<MetavarName>,
    pub hastype: bool,
    pub ctl: GenericCtl<
        <Predicate as Pred>::ty,
        <Rc<GenericSubst<MetavarName, BoundValue>> as Subs>::Mvar,
        Vec<String>,
    >,
}

// Given the depends clause it converts it into a Dep object
fn _getdep(_rules: &Vec<Rule>, _lino: usize, _dep: &mut Snode) -> Dep {
    // dep.print_tree();
    // // match dep.kinds() {
    // //     Tag::PREFIX_EXPR => {
    // //         //for NOT depends
    // //         let [cond, expr] = util::tuple_of_2(&mut dep.children);
    // //         match cond.kinds() {
    // //             Tag::BANG => Dep::AntiDep(Box::new(getdep(rules, lino, expr))),
    // //             _ => syntaxerror!(lino, "Dependance must be a boolean expression"),
    // //         }
    // //     }
    // //     Tag::BIN_EXPR => {
    // //         let [lhs, cond, rhs] = util::tuple_of_3(&mut dep.children);
    // //         match cond.kinds() {
    // //             Tag::AMP2 => {
    // //                 //Recurses
    // //                 Dep::AndDep(Box::new((getdep(rules, lino, lhs), getdep(rules, lino, rhs))))
    // //             }
    // //             Tag::PIPE2 => {
    // //                 //Recurses
    // //                 Dep::OrDep(Box::new((getdep(rules, lino, lhs), getdep(rules, lino, rhs))))
    // //             }
    // //             _ => syntaxerror!(lino, "Dependance must be a boolean expression"),
    // //         }
    // //     }
    // //     Tag::PATH_EXPR => {
    // //         let name = dep.getstring();
    // //         if rules.iter().any(|x| x.name == name) {
    // //             //IndexMap trait
    // //             Dep::Dep(name)
    // //         } else {
    // //             syntaxerror!(lino, "no such Rule", name)
    // //         }
    // //     }
    // //     Tag::PAREN_EXPR => {
    // //         let expr = &mut dep.children[1];
    // //         getdep(rules, lino, expr)
    // //     }
    // //     _ => syntaxerror!(lino, "malformed Rule", dep.getstring()),
    // }
    todo!()
}

// fn get_expr(contents: &str) -> Snode {
//     //assumes that a
//     //binary expression exists

//     get_blxpr(contents) //BlockExpr
//         .children
//         .swap_remove(0) //StmtList
//         .children
//         .swap_remove(2) //TailExpr
// }

/// Parses the depends on clause in the rule definition by calling getdep
// fn _getdependson(rules: &Vec<Rule>, rule: &str, lino: usize) -> Dep {
//     let fnstr = format!("fn coccifn {{ {} }}", rule);
//     _getdep(rules, lino, &mut get_expr(fnstr.as_str()))
// }

/// Deals with the first line of a rule definition
fn handlerules(_rules: &Vec<Rule>, decl: Vec<&str>, lino: usize) -> (Name, Dep, bool) {
    let decl = decl.join("\n");
    let mut hastype: bool = false;
    let mut tokens = decl.trim().split([' ', '\n']);
    let currrulename = {
        if let Some(currrulename) = tokens.next() {
            if currrulename == "type" {
                hastype = true;
                Name::from("")
            } else {
                Name::from(currrulename) //converted &str to Name,
                                         //because rule should own its name
            }
        } else {
            format!("rule{lino}")
        } //if currrulename does not exist
    };

    let sword = tokens.next();
    let tword = tokens.next();
    let fword = tokens.next();
    let fiword = tokens.next();

    let (depends, istype) = match (sword, tword, fword, fiword) {
        (Some("depends"), Some("on"), Some(rule), hastype) => {
            let _booleanexp: Name = rule.to_string();
            let hastype: bool = hastype.is_some_and(|x| x == "type");
            // (getdependson(rules, Name::from(booleanexp).as_str(), lino), hastype)
            (Dep::NoDep, hastype)
        }
        (hastype, None, None, None) => (Dep::NoDep, hastype.is_some_and(|x| x == "type")),
        _ => syntaxerror!(lino, "Bad Syntax"),
    };

    (currrulename, depends, hastype || istype)
}

// Gives ((a...b)...c)
// This is important for process_dots_plus
fn group_dots(snode: &Snode) -> Snode {
    if snode.children.is_empty() {
        return snode.clone();
    }

    let rchildren = snode.children.iter();
    let mut nchidlren: Vec<Snode> = vec![];
    let mut prev: Option<Snode> = None;//unwrap because the list is not empty
    let mut prev_dot: Option<Snode> = None;

    for child in rchildren {
        let child = group_dots(child);
        match (prev_dot.is_some(), prev.is_some(), child.is_dots) {
            (true, true, true) => {
                //b  ...       a      ...
                //  ^prev_dot  ^ prev ^child
                let mut dots = Snode::make_wildcard(child.wrapper.mcodekind);
                dots.children = vec![prev_dot.unwrap()];
                prev_dot = Some(dots);
                prev = None;
            },
            (true, true, false) => {
                // ...        b        c
                // ^prev_dots ^prev    ^child
                nchidlren.push(prev_dot.unwrap());
                prev = Some(child);
                prev_dot = None;
            },
            (true, false, true) => {
                // ... x ...
                //not possible
                panic!("Not possible")
            },
            (true, false, false) => {
                // ... x c
                prev_dot.as_mut().unwrap().children.push(child.clone());
                prev = Some(child);
            },
            (false, true, true) => {
                //b ...
                let mut dots = Snode::make_wildcard(child.wrapper.mcodekind);
                dots.children = vec![prev.unwrap()];
                prev = None;
                prev_dot = Some(dots);
            },
            (false, true, false) => {
                // a b c
                nchidlren.push(prev.unwrap());
                prev = Some(child);
                prev_dot = None;
            },
            (false, false, true) => {
                // x x ...
                //starts with ...
                let mut dots = Snode::make_wildcard(child.wrapper.mcodekind);
                dots.children = vec![Snode::make_fake()];
                prev = None;
                prev_dot = Some(dots);
            },
            (false, false, false) => {
                //x x b
                //start
                prev = Some(child);
                prev_dot = None;
            },
        }
    }

    match (prev_dot.is_some(), prev.is_some()) {
        (true, true) => {
            //... a 
            nchidlren.push(prev_dot.unwrap());
        },
        (true, false) => {
            //ends with ...
            let mut dot = prev_dot.unwrap();
            dot.children.push(Snode::make_fake());
            nchidlren.push(dot);
        },
        (false, true) => {
            //a b
            nchidlren.push(prev.unwrap());
        },
        (false, false) => {
            //x
            panic!("Not possibe")
        },
    }

    let mut snode = snode.clone_without_children();
    snode.children = nchidlren;
    return snode;
}

fn process_dots_plus(snode: &mut Snode) {
    if snode.children.is_empty() {
        return;
    }

    fn aux(snode: &mut Snode, pluses: Vec<Snode>) {
        if snode.is_dots {
            aux(&mut snode.children[0], pluses);
        }
        else {
            attach_pluses_back(snode, pluses);
        }
    }

    if snode.is_dots {
        if snode.wrapper.mcodekind.has_pluses() {
            let pluses = snode.wrapper.mcodekind.getpluses();
            aux(&mut snode.children[0], pluses.0);
            attach_pluses_front(&mut snode.children[1], pluses.1);
            // snode.children[1].wrapper.mcodekind.push_pluses_front(pluses.1);
        }
    }

    for snode in &mut snode.children {
        process_dots_plus(snode)
    }
}

// fn group_dotss(snode: &mut Snode) {
//     if snode.children.is_empty() {
//         return;
//     }

//     let mut rchildren = snode.children.iter_mut().rev().enumerate();
//     let (_, mut prev) = rchildren.next().unwrap();//unwrap because the list is not empty
//     let mut prev_dot: Option<Snode> = if prev.is_dots {
//         todo!()//make an empty Snode here
//     } else { 
//         None 
//     };

//     for (i, child ) in rchildren {
//         if child.is_dots {
//             let mut dots = Snode::make_wildcard();
//             let dchild = if prev_dot.is_none() { 
//                 vec![prev.clone()] 
//             } else {
//                 let child = prev_dot.unwrap(); 
//                 vec![child] 
//             };
//             dots.children = dchild;
//             prev_dot = Some(dots);
//         }
//         else {
//             if let Some(ref mut dot) = prev_dot {
//                 dot.children.insert(0, child.clone());
//             }
//             prev = child;
//         }
//     }
// }

fn get_body(snode: &mut Snode) {
    let stmtlist = &mut snode.children[3];
    stmtlist.children.remove(0);
    stmtlist.children.remove(stmtlist.children.len() - 1);
}

/// Turns values from handlemods into a patch object
fn getpatch(
    plusbuf: &str,
    minusbuf: &str,
    llino: usize,
    metavars: &Vec<MetaVar>,
    hastype: bool,
) -> Patch {
    let plusbuf = format!("{}{}", "\n".repeat(llino), plusbuf);
    let minusbuf = format!("{}{}", "\n".repeat(llino), minusbuf);
    let mut p = Patch {
        plus: {
            match wrap_root(plusbuf.as_str()) {
                Ok(node) => node,
                Err(errstr) => {
                    eprintln!("Error in parsing Plus Buffer: {}", errstr);
                    panic!("Unparsable Semantic Patch")
                }
            }
        },
        minus: match wrap_root(minusbuf.as_str()) {
            Ok(node) => node,
            Err(errstr) => {
                eprintln!("Error in parsing Minus Buffer: {}", errstr);
                panic!("Unparsable Semantic Patch")
            }
        },
    };
    p.fix_dots();
    // p.plus.print_tree();
    // p.minus.print_tree();
    p.setmetavars(metavars);
    p.setminus();
    get_body(&mut p.minus);
    get_body(&mut p.plus);
    p.striplet(hastype);
    p.tag_plus();
    p.group_dots();
    p.process_dots();
    p
}

/// Gets the stmtlist for the collapsed tree
fn get_stmtlist<'a>(snode: &'a Snode) -> &'a Snode {
    &snode.children[3]
}

/// Given all the info about name, depends, metavars and modifiers and context
/// it consolidates everything into a line preserved rule object
fn buildrule(
    currrulename: &Name,
    currdepends: Dep,
    mut metavars: Vec<MetaVar>, //mutable because unused metavars are removed
    blanks: usize,
    pbufmod: &String,
    mbufmod: &String,
    lastruleline: usize,
    istype: bool,
) -> Rule {
    //end of the previous rule
    let mut plusbuf = String::new();
    let mut minusbuf = String::new();
    plusbuf.push_str(format!("fn {currrulename}_plus() {{\n").as_str());
    minusbuf.push_str(format!("fn {currrulename}_minus() {{\n").as_str());

    plusbuf.push_str(&"\n".repeat(blanks));
    minusbuf.push_str(&"\n".repeat(blanks));

    if istype {
        let pbufmod = if pbufmod.trim() != "" {
            format!("let COCCIVAR: \n{}\n;", pbufmod)
        } else {
            String::new()
        };

        let mbufmod = if mbufmod.trim() != "" {
            format!("let COCCIVAR: \n{}\n;", mbufmod)
        } else {
            String::new()
        };

        plusbuf.push_str(&pbufmod);
        minusbuf.push_str(&mbufmod);
    } else {
        plusbuf.push_str(pbufmod);
        minusbuf.push_str(mbufmod);
    }

    plusbuf.push_str("}");
    minusbuf.push_str("}");
    // eprintln!("plusbuf - {}", plusbuf);
    // eprintln!("minusbuf - {}", minusbuf);
    let currpatch = getpatch(&plusbuf, &minusbuf, lastruleline, &metavars, istype);
    let unusedmetavars = currpatch.getunusedmetavars(metavars.clone());

    for metavar in &unusedmetavars {
        eprintln!("Warning: Unused metavariable {}.{}", metavar.getrulename(), metavar.getname());
        if let Some(index) = metavars.iter().position(|x| x.getname() == metavar.getname()) {
            //All this will be optimised when using hashsets
            metavars.remove(index);
        }
    }

    let mut freevars: Vec<MetaVar> = vec![];
    for metavar in &metavars {
        if metavar.getrulename() != currrulename {
            debugcocci!("Freevar found- {:?}", metavar);
            freevars.push(metavar.clone());
        }
    }

    let ctl = make_ctl_simple(get_stmtlist(&currpatch.minus), false);

    let rule = Rule {
        name: Name::from(currrulename),
        dependson: currdepends,
        metavars: metavars,
        unusedmetavars: unusedmetavars,
        patch: currpatch,
        freevars: freevars,
        usedafter: HashSet::new(),
        hastype: istype,
        ctl: ctl,
    };
    rule
}    

/// Does nothing much as of now. Just appends lines inside the rules
/// while preserving line numbers with new lines
pub fn handlemods(block: &Vec<&str>) -> Result<(String, String, bool), (usize, String)> {
    let mut plusbuf = String::new();
    let mut minusbuf = String::new();
    let mut lino: usize = 0;
    let mut hasstar: bool = false;
    let mut hastforms: bool = false;
    let mut indisj = 0;

    for line in block {
        if line.trim() == "..." {
            minusbuf.push_str(&format!("{}{}", WILDCARD, '\n'));
            plusbuf.push_str(&format!("{}{}", WILDCARD, '\n'));
            continue;
        }
        else if line.trim_end() == ("-...") {
            minusbuf.push_str(&format!("/*-*/{}{}", WILDCARD, '\n'));
            plusbuf.push('\n');
            continue;
        }

        match line.chars().next() {
            Some('+') => {
                if hasstar {
                    return Err((
                        lino,
                        String::from("Transformations cannot be applied because of star prior"),
                    ));
                }
                hastforms = true;
                plusbuf.push_str(&format!("{}{}{}", "/*+*/", &line[1..], '\n'));
                minusbuf.push('\n');
            }
            Some('-') => {
                if hasstar {
                    return Err((
                        lino,
                        String::from("Transformations cannot be applied because of star prior"),
                    ));
                }
                hastforms = true;
                minusbuf.push_str(&format!("{}{}{}", "/*-*/", &line[1..], '\n'));
                plusbuf.push('\n');
            }
            Some('(') => {
                let holder = &format!("{}[", COCCI_DISJ_NAME);
                plusbuf.push_str(holder);
                minusbuf.push_str(holder);
                indisj += 1;
            }
            Some('|') => {
                let holder = "***|***\n";
                plusbuf.push_str(holder);
                minusbuf.push_str(holder);
            }
            Some(')') => {
                if indisj == 0 {
                    syntaxerror!(lino, 
                        "Disjunction does not exist. ')' in column 0 is only used for closing disjunctions. \n\
                        Put a space before ')' if not a part of disjunction.")
                }
                plusbuf.push_str("]\n");
                minusbuf.push_str("]\n");
                indisj -= 1;
            }
            Some('*') => {
                if hastforms {
                    return Err((
                        lino,
                        String::from("Star cannot be applied because of transformation prior"),
                    ));
                }
                hasstar = true;
                plusbuf.push_str(&format!("{}{}{}", "/***/", &line[1..], '\n'));
                minusbuf.push_str(&format!("{}{}{}", "/***/", &line[1..], '\n'));
            }
            _ => {
                plusbuf.push_str(&line[..]);
                plusbuf.push('\n');

                minusbuf.push_str(&line[..]);
                minusbuf.push('\n');
            }
        }

        lino += 1;
    }
    return Ok((plusbuf, minusbuf, hasstar));
}

/// Parses the metavar declarations
pub fn handle_metavar_decl(
    rules: &Vec<Rule>,
    block: &Vec<&str>,
    rulename: &Name,
    lino: usize,
) -> (Vec<MetaVar>, usize, bool) {
    let mut offset: usize = 0;
    let mut blanks: usize = 0;
    let mut metavars: Vec<MetaVar> = vec![]; //stores the mvars encounteres as of now
    let mut hastypes = false;

    for line in block {
        offset += 1;
        let line = line.trim();
        if line == "" {
            continue;
        }
        let mut tokens = line.split(&[',', ' ', ';'][..]);
        let ty = tokens.next().unwrap().trim();
        let ty = MetavarType::build(ty);
        if ty.is_adt() {
            hastypes = true;
        }

        for var in tokens {
            let var = var.trim().to_string();
            if var != "" {
                if !metavars.iter().any(|x| x.getname() == var) {
                    metavars.push(makemetavar(rules, rulename, &var, &ty, lino));
                } else {
                    syntaxerror!(
                        offset + lino,
                        format!("Redefining {:?} metavariable {}", ty, var)
                    );
                }
            }
        }
        blanks += 1;
    }
    (metavars, blanks, hastypes)
}

fn handleprepatch(contents: &str) {
    let lines = contents.lines();

    for line in lines {
        if !line.starts_with("//") && line.trim() != "" {
            syntaxerror!(0, "SyntaxError");
        }
    }
}

fn setusedafter(rules: &mut Vec<Rule>) {
    let mut tmp: HashSet<MetavarName> = HashSet::new();
    for rule in rules.iter_mut().rev() {
        rule.usedafter = tmp.clone();
        for freevar in &rule.freevars {
            tmp.insert(MetavarName {
                rulename: freevar.getrulename().to_string(),
                varname: freevar.getname().to_string(),
            });
        }
    }
}

pub fn processcocci(contents: &str) -> (Vec<Rule>, bool, bool) {
    debugcocci!("{}", "Started Parsing");
    let mut blocks: Vec<&str> = contents.split("@").collect();
    let mut lino = 0; //stored line numbers
                      //mutable because I supply it with modifier statements

    let mut rules: Vec<Rule> = vec![];
    //check for empty
    if blocks.len() == 0 {
        return (vec![], false, false);
    }
    //throwing away the first part before the first @
    handleprepatch(blocks.remove(0));
    let nrules = blocks.len() / 4; //this should always be an integer if case of a proper cocci file
                                   //if it fails we will find out in the next for loop

    let mut lastruleline = 0;
    let mut hasstars = false; //this does not ensure that all rules have only * or none
                              //TODO enforce that
    let mut hastypes = false;
    for i in 0..nrules {
        debugcocci!("Processing rule {}", i);
        let block1: Vec<&str> = blocks[i * 4].trim().lines().collect(); //rule
        let block2: Vec<&str> = blocks[i * 4 + 1].lines().collect(); //metavars
        let block3: Vec<&str> = blocks[i * 4 + 2].lines().collect(); //empty
        let block4: Vec<&str> = blocks[i * 4 + 3].lines().collect(); //actual patch and mods

        //getting rule info
        let (currrulename, currdepends, istype) = handlerules(&rules, block1, lino);
        debugcocci!("Rulename: {} Depends on: {:?}", currrulename, currdepends);
        lino += 1;
        let (metavars, blanks, hastype) = handle_metavar_decl(&rules, &block2, &currrulename, lino);
        hastypes = hastypes || hastype;
        //metavars
        lino += block2.len();

        if block3.len() != 0 {
            syntaxerror!(lino, "Syntax Error");
        }

        //modifiers
        lino += block4.len() - 1;
        let (pbufmod, mbufmod, hasstar) = handlemods(&block4).unwrap_or_else(|(lino, msg)| {
            syntaxerror!(lino, 0, msg);
        });
        if hasstar {
            hasstars = true;
            //This part needs to be completed
            //as it does not enforce all rules having *
        }

        let rule = buildrule(
            &currrulename,
            currdepends,
            metavars,
            blanks,
            &pbufmod,
            &mbufmod,
            lastruleline,
            istype,
        );
        rules.push(rule);

        lastruleline = lino;
    }
    setusedafter(&mut rules);
    (rules, hastypes, hasstars) //FIXME
                                //flag_logilines(0, &mut root);
}
