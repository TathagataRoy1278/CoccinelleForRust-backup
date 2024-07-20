use std::rc::Rc;

use ra_parser::SyntaxKind;

use crate::{
    commons::info::{L_BROS, R_BROS},
    ctl::ctl_ast::{Direction, Strict},
    engine::ctl_cocci::{BoundValue, Predicate},
    parsing_cocci::ast0::{MetavarName, Snode},
};

use super::{
    ctl_ast::{GenericCtl, GenericSubst, Modif},
    ctl_engine::{Pred, Subs},
};

// pub type WrappedCtl<Pred, Mvar> = GenericCtl<(Pred, Modif<Mvar>), Mvar, usize>;

#[derive(Clone, PartialEq, Eq)]
pub enum WrappedBinding<Value> {
    ClassicVal(Value),
    PredVal(Modif),
}

// pub fn wrap_label(f: impl Fn(<Predicate as Pred>::ty) -> Vec<(usize, SubstitutionList)>) {
//     fn oldlabelfn(p: Pre) {

//     }

// }

type CTL = GenericCtl<
    <Predicate as Pred>::ty,
    <Rc<GenericSubst<MetavarName, BoundValue>> as Subs>::Mvar,
    Vec<String>,
>;

type Tag = SyntaxKind;

macro_rules! AND {
    ($a: expr, $b: expr) => {
        Box::new(CTL::And(Strict::Strict, $a, $b))
    };
}
macro_rules! AX {
    ($a: expr) => {
        Box::new(CTL::AX(Direction::Forward, Strict::Strict, $a))
    };
}
macro_rules! OR {
    ($a: expr, $b: expr) => {
        Box::new(CTL::Or($a, $b))
    };
}
macro_rules! EX {
    ($a: expr) => {
        Box::new(CTL::EX(Direction::Forward, $a))
    };
}

macro_rules! aux {
    ($a: expr, $b: expr, $c: expr, $d: expr) => {
        aux($a, $b, $c, $d, Connector::CAX, WrapperOptions::None)
    };
    ($a: expr, $b: expr, $c: expr, $d: expr, $e: expr, $f: expr) => {
        aux($a, $b, $c, $d, $e, $f)
    };
}

impl CTL {
    pub fn add_paren(self, name: String) -> Box<Self> {
        let p = Box::new(CTL::Pred(Predicate::Paren(MetavarName::new(name), false)));
        AND!(Box::new(self), p)
    }
}

fn dots_has_mv(dots: &Snode) -> bool {
    dots.children[1].wrapper.metavar.ismeta()
}

enum Connector {
    CAX,
    NIL,
    CEX,
    _CAG,
}

enum WrapperOptions {
    None,
    NoParenMvar,
}

pub fn make_ctl_simple(snode: &Snode, _prev_is_mvar: bool) -> CTL {
    fn get_kind_pred(ctl: Box<CTL>, kind: &Vec<SyntaxKind>, prev_is_mvar: bool) -> Box<CTL> {
        let kind_pred = Box::new(CTL::Pred(Predicate::Kind(kind.clone(), prev_is_mvar)));
        let fctl = CTL::And(Strict::Strict, kind_pred, AX!(ctl));
        Box::new(fctl)
    }

    fn handle_dots(dots: &Snode, attach_end: Option<Box<CTL>>, pim: bool, ln: &mut usize) -> Box<CTL> {
        // The parent_kinds is not required for dots children
        // So it is okay to set any value
        if dots.children[0].has_kind(&Tag::L_CURLY) && dots.children[1].has_kind(&Tag::R_CURLY) {
            let a2 = aux!(&dots.children[1], attach_end, false, ln); // }
            let tmp = AND!(Box::new(CTL::Pred(Predicate::AfterNode)), AX!(a2)); // After & AX(})
            let tmp = EX![tmp]; // Ex (After & AX (}))
                                // eprintln!("ln - {}", ln);
            let a1 = aux!(&dots.children[0], None, pim, ln);
            // eprintln!("ln2 - {}", ln);
            let a1 = AND!(a1, tmp);
            return Box::new(CTL::Exists(
                false,
                MetavarName::new(format!("l{}", (*ln + 1))),
                a1,
            ));
        }

        //This is just for
        //Everything in the comments assume a...b

        //a
        let s1 = &dots.children[0];
        //b
        let s2 = &dots.children[1];

        //checks is a itsels is dots
        //(a1...a2)...b
        let mut a1 = if s1.is_dots {
            aux!(&s1.children[1], None, false, &mut (ln.clone()))
        } else {
            aux!(s1, None, false, &mut (ln.clone()))
        };

        //b for !(a V b)
        let mut b1 = aux!(s2, None, false, &mut (ln.clone()));
        //b for A[!(...) U b]
        let b2 = aux!(s2, attach_end, false, ln);

        let mut f = |ctl: &mut CTL| match ctl {
            CTL::Pred(p) => p.set_unmodif(),
            CTL::Exists(_keep, _, _) => {}
            _ => {}
        };

        //removes any mods from a and b in
        // !(a v b)
        CTL::do_ctl(&mut b1, &mut f);
        CTL::do_ctl(&mut a1, &mut f);

        //creates the !(a v b)
        let tmp1 = if dots.wrapper.is_modded {
            let tt = Box::new(CTL::Not(OR!(a1, b1)));
            let tt2 = Box::new(CTL::Exists(
                true,
                MetavarName::create_v(),
                Box::new(CTL::Pred(Predicate::Token(true))),
            ));
            CTL::And(Strict::Strict, tt, tt2)
        } else {
            CTL::Not(OR!(a1, b1))
        };

        //makes the A[U]
        let tmp2 = CTL::AU(Direction::Forward, Strict::Strict, Box::new(tmp1), b2);

        //depending on it being a...b or (a1...a2)...b it proceeds
        if s1.is_dots {
            handle_dots(&s1, Some(Box::new(tmp2)), pim, ln)
        } else {
            aux!(&dots.children[0], Some(Box::new(tmp2)), pim, ln)
        }
    }

    fn set_pm_true(ctl: &mut Box<CTL>) {
        match ctl.as_mut() {
            GenericCtl::False => {}
            GenericCtl::True => {}
            GenericCtl::Pred(p) => p.set_pm_true(),
            GenericCtl::Not(ctl) => set_pm_true(ctl),
            GenericCtl::Exists(_, _, ctl) => set_pm_true(ctl),
            GenericCtl::And(_, ctl, _) => set_pm_true(ctl),
            GenericCtl::AndAny(_, _, ctl, _) => set_pm_true(ctl),
            GenericCtl::HackForStmt(_, _, _, _) => todo!(),
            GenericCtl::Or(ctl, _) => set_pm_true(ctl),
            GenericCtl::Implies(ctl, _) => set_pm_true(ctl),
            GenericCtl::AF(_, _, ctl) => set_pm_true(ctl),
            GenericCtl::AX(_, _, ctl) => set_pm_true(ctl),
            GenericCtl::AG(_, _, ctl) => set_pm_true(ctl),
            GenericCtl::AW(_, _, ctl, _) => set_pm_true(ctl),
            GenericCtl::AU(_, _, ctl, _) => set_pm_true(ctl),
            GenericCtl::EF(_, ctl) => set_pm_true(ctl),
            GenericCtl::EX(_, ctl) => set_pm_true(ctl),
            GenericCtl::EG(_, ctl) => set_pm_true(ctl),
            GenericCtl::EU(_, ctl, _) => set_pm_true(ctl),
            GenericCtl::Let(_, _, _) => todo!(),
            GenericCtl::LetR(_, _, _, _) => todo!(),
            GenericCtl::Ref(_) => todo!(),
            GenericCtl::SeqOr(_, _) => todo!(),
            GenericCtl::Uncheck(_) => todo!(),
            GenericCtl::InnerAnd(ctl) => set_pm_true(ctl),
            GenericCtl::XX(_, _) => todo!(),
        }
    }

    fn aux(
        snode: &Snode,
        attach_end: Option<Box<CTL>>,
        prev_is_mvar: bool,
        ln: &mut usize,
        //optional args
        connector: Connector,
        options: WrapperOptions,
    ) -> Box<CTL> {
        if snode.children.is_empty() || snode.wrapper.metavar.ismeta() || snode.is_dots {
            if !snode.is_dots {
                //Sets the modif
                let tmpp = if snode.wrapper.is_modded {
                    Box::new(CTL::Pred(Predicate::Match(
                        snode.clone(),
                        Modif::Modif,
                        prev_is_mvar,
                    )))
                } else {
                    Box::new(CTL::Pred(Predicate::Match(
                        snode.clone(),
                        Modif::Unmodif,
                        prev_is_mvar,
                    )))
                };

                //adds the _v for modifs
                let mut tmpp = if snode.wrapper.is_modded {
                    //is minused or has pluses attached to it
                    Box::new(CTL::Exists(true, MetavarName::create_v(), tmpp))
                } else {
                    tmpp
                };

                //if the node is one of the braces, add a label to it
                let kind = snode.kinds().last().unwrap();
                let lname;
                if !matches!(options, WrapperOptions::NoParenMvar) {
                    if L_BROS.contains(kind) {
                        lname = format!("l{}", ln);
                        *ln -= 1;
                        tmpp = (*tmpp).add_paren(lname);
                    } else if R_BROS.contains(kind) {
                        //Rs
                        *ln += 1;
                        lname = format!("l{}", ln);
                        tmpp = (*tmpp).add_paren(lname);
                    };
                }

                //propagates
                let nextctl = if let Some(mut attach_end) = attach_end {
                    if snode.wrapper.metavar.ismeta() {
                        set_pm_true(&mut attach_end);
                    }

                    //If the node is one of { ( [ <
                    if snode.kinds().iter().any(|x| L_BROS.contains(x)) {
                        //if there is a { then there also exists an AfterNode
                        //this also adds the OR AfterNode condition for all
                        //left braces other than { but that should not be a problem right?
                        //Since AfterNodes only appear for {s
                        let connector = match connector {
                            Connector::CAX => AX!(OR!(attach_end, Box::new(CTL::Pred(Predicate::AfterNode)))),
                            Connector::NIL => OR!(attach_end, Box::new(CTL::Pred(Predicate::AfterNode))),
                            Connector::CEX => EX!(OR!(attach_end, Box::new(CTL::Pred(Predicate::AfterNode)))),
                            Connector::_CAG => todo!(),
                        };

                        let nextctl = AND!(tmpp, connector);

                        Box::new(CTL::Exists(
                            false,
                            MetavarName::new(format!("l{}", *ln + 1)),
                            nextctl,
                        ))
                    } else {
                        let connector = match connector {
                            Connector::CAX => AX!(attach_end),
                            Connector::NIL => attach_end,
                            Connector::CEX => EX!(attach_end),
                            Connector::_CAG => todo!(),
                        };

                        let nextctl = AND!(tmpp, connector);
                        nextctl
                    }
                } else {
                    tmpp
                };

                //if there was a lparan this adds the exists lx term

                if snode.wrapper.metavar.ismeta() && snode.wrapper.freevars.contains(&snode.wrapper.metavar) {
                    Box::new(CTL::Exists(
                        true,
                        snode.wrapper.metavar.getminfo().0.clone(),
                        nextctl,
                    ))
                } else {
                    nextctl
                }
            } else {
                handle_dots(snode, attach_end, prev_is_mvar, ln)
            }
        } else if snode.children.len() == 1 {
            // eprintln!("{:?}:{:?}", snode.children, snode.children[0].kinds());
            
            // No specific checks like for IF ann Binexpr have been put here
            // because only artifical nodes like fake and dots can be single
            // children
            let ctl = aux!(&snode.children[0], attach_end, false, ln);
            get_kind_pred(ctl, snode.kinds(), prev_is_mvar)
        } else if snode.has_kind(&SyntaxKind::IF_EXPR) {
            let parent_kinds = snode.kinds();
            let mut rev_iter = snode.children.iter().rev().peekable();
            let mut snode = rev_iter.next().unwrap();
            let prev_node = rev_iter.peek().unwrap();

            let ifexprctl = if prev_node.has_kind(&SyntaxKind::ELSE_KW) {
                //has else part
                let mut spb =
                    prev_node.wrapper.metavar.ismeta() || (prev_node.is_dots && dots_has_mv(&prev_node));
                let ctl = aux!(snode, attach_end.clone(), spb, ln);

                snode = rev_iter.next().unwrap();
                // ^ else keyword
                spb = rev_iter.peek().map_or(false, |x| {
                    x.wrapper.metavar.ismeta() || (x.is_dots && dots_has_mv(&x))
                });
                let falsebranch = aux!(snode, Some(ctl), spb, ln);
                // ^ this ctl is the else branch
                let mut ctl: Box<CTL>;

                snode = rev_iter.next().unwrap();
                spb = rev_iter.peek().map_or(false, |x| {
                    x.wrapper.metavar.ismeta() || (x.is_dots && dots_has_mv(&x))
                });
                let truebranch = aux!(snode, attach_end, spb, ln);
                // ^ true block

                let suffix = AND!(EX!(truebranch), EX!(falsebranch));

                snode = rev_iter.next().unwrap();
                spb = rev_iter.peek().map_or(false, |x| {
                    x.wrapper.metavar.ismeta() || (x.is_dots && dots_has_mv(&x))
                });
                ctl = aux!(snode, Some(suffix), spb, ln, Connector::NIL, WrapperOptions::None);
                // ^ condition

                snode = rev_iter.next().unwrap();
                spb = rev_iter.peek().map_or(false, |x| {
                    x.wrapper.metavar.ismeta() || (x.is_dots && dots_has_mv(&x))
                });
                ctl = aux!(snode, Some(ctl), spb, ln);
                // ^ if keyword

                while rev_iter.len() != 0 {
                    //takes care of the attributes
                    // let p = CTL::AX(Direction::Forward, Strict::Strict, ctl);
                    // ctl = Box::new(CTL::And(Strict::Strict, aux(snode), Box::new(p)));

                    snode = rev_iter.next().unwrap();
                    spb = rev_iter.peek().map_or(false, |x| {
                        x.wrapper.metavar.ismeta() || (x.is_dots && dots_has_mv(&x))
                    });
                    ctl = aux!(snode, Some(ctl), spb, ln);
                }

                ctl
            } else {
                //no else part
                let mut spb =
                    prev_node.wrapper.metavar.ismeta() || (prev_node.is_dots && dots_has_mv(&prev_node));
                let mut ctl = aux!(snode, attach_end, spb, ln);

                snode = rev_iter.next().unwrap();
                // ^ condition
                spb = rev_iter.peek().map_or(false, |x| {
                    x.wrapper.metavar.ismeta() || (x.is_dots && dots_has_mv(&x))
                });

                let truebranch = aux!(snode, Some(ctl), spb, ln, Connector::CEX, WrapperOptions::None);

                snode = rev_iter.next().unwrap();
                spb = rev_iter.peek().map_or(false, |x| {
                    x.wrapper.metavar.ismeta() || (x.is_dots && dots_has_mv(&x))
                });
                ctl = aux!(snode, Some(truebranch), spb, ln);
                // ^ if keyword

                while rev_iter.len() != 0 {
                    //takes care of the attributes
                    // let p = CTL::AX(Direction::Forward, Strict::Strict, ctl);
                    // ctl = Box::new(CTL::And(Strict::Strict, aux(snode), Box::new(p)));

                    snode = rev_iter.next().unwrap();
                    spb = rev_iter.peek().map_or(false, |x| {
                        x.wrapper.metavar.ismeta() || (x.is_dots && dots_has_mv(&x))
                    });
                    ctl = aux!(snode, Some(ctl), spb, ln);
                }
                ctl
            };

            get_kind_pred(ifexprctl, parent_kinds, prev_is_mvar)
        } else if snode.has_kind(&SyntaxKind::BIN_EXPR) {
            let parent_kinds = snode.kinds();
            let mut rev_iter = snode.children.iter().rev().peekable();
            let mut snode = rev_iter.next().unwrap();
            let prev_node = rev_iter.peek().unwrap();

            let mut spb =
                prev_node.wrapper.metavar.ismeta() || (prev_node.is_dots && dots_has_mv(&prev_node));
            let mut ctl = aux!(snode, attach_end, spb, ln, connector, WrapperOptions::None);

            snode = rev_iter.next().unwrap();
            spb = rev_iter.peek().map_or(false, |x| x.wrapper.metavar.ismeta());
            ctl = aux!(
                snode,
                Some(ctl),
                spb,
                ln,
                Connector::CAX,
                WrapperOptions::NoParenMvar
            );
            //So that '<' or '>' are not classified as a paren

            snode = rev_iter.next().unwrap();
            spb = rev_iter.peek().map_or(false, |x| x.wrapper.metavar.ismeta());
            ctl = aux!(snode, Some(ctl), spb, ln);

            get_kind_pred(ctl, parent_kinds, prev_is_mvar)
        } else {
            let parent_kinds = snode.kinds();
            let mut rev_iter = snode.children.iter().rev().peekable();
            let mut snode = rev_iter.next().unwrap();
            let prev_node = rev_iter.peek().unwrap();

            //Except at the top and bottom of the file
            //All comments are preceded and succeeded by other nodes
            //on the same level. I know it sounds weird.

            let mut spb =
                prev_node.wrapper.metavar.ismeta() || (prev_node.is_dots && dots_has_mv(&prev_node));
            let mut ctl = aux!(snode, attach_end, spb, ln, connector, WrapperOptions::None);
            // let mut spb: bool;

            while rev_iter.len() != 0 {
                // let p = CTL::AX(Direction::Forward, Strict::Strict, ctl);
                // ctl = Box::new(CTL::And(Strict::Strict, aux(snode), Box::new(p)));

                snode = rev_iter.next().unwrap();
                spb = rev_iter.peek().map_or(false, |x| x.wrapper.metavar.ismeta());
                ctl = aux!(snode, Some(ctl), spb, ln);
            }
            get_kind_pred(ctl, parent_kinds, prev_is_mvar)
        }
    }

    // snode.print_tree();
    let ctl = aux!(snode, None, false, &mut 0);
    match *ctl {
        CTL::And(_, _, b) => match *b {
            CTL::AX(_, _, b) => *b,
            _ => panic!("Should not be anything but an AX"),
        },
        _ => {
            panic!("Should not be as of now, other than AND")
        }
    }
    // *ctl
}
