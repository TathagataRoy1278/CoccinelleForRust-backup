use ra_parser::SyntaxKind;

use crate::{
    commons::info::{L_BROS, R_BROS},
    ctl::ctl_ast::{Direction, Strict},
    engine::ctl_cocci::{BoundValue, Predicate},
    parsing_cocci::{
        ast0::{MetavarName, Snode},
        parse_cocci::Patch,
    },
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
    <GenericSubst<MetavarName, BoundValue> as Subs>::Mvar,
    Vec<String>,
>;

impl CTL {
    pub fn add_paren(self, name: String) -> Box<Self> {
        let p = Box::new(CTL::Pred(Predicate::Paren(MetavarName::new(name), false)));
        Box::new(CTL::And(Strict::Strict, Box::new(self), p))
    }
}

type Tag = SyntaxKind;

fn dots_has_mv(dots: &Snode) -> bool {
    dots.children[1].wrapper.metavar.ismeta()
}

pub fn make_ctl_simple(snode: &Snode, _prev_is_mvar: bool) -> CTL {
    fn get_kind_pred(ctl: Box<CTL>, kind: &Vec<SyntaxKind>, prev_is_mvar: bool) -> Box<CTL> {
        let kind_pred = Box::new(CTL::Pred(Predicate::Kind(kind.clone(), prev_is_mvar)));
        let fctl = CTL::And(
            Strict::Strict,
            kind_pred,
            Box::new(CTL::AX(Direction::Forward, Strict::Strict, ctl)),
        );
        Box::new(fctl)
    }

    fn handle_dots(
        dots: &Snode,
        attach_end: Option<Box<CTL>>,
        pim: bool,
        ln: &mut usize,
    ) -> Box<CTL> {
        if dots.children[0].has_kind(&Tag::L_CURLY) && dots.children[1].has_kind(&Tag::R_CURLY) {
            let a2 = aux(&dots.children[1], attach_end, false, ln); // }
            let tmp = Box::new(CTL::And(
                Strict::Strict,
                Box::new(CTL::Pred(Predicate::AfterNode)),
                Box::new(CTL::AX(Direction::Forward, Strict::Strict, a2)),
            )); // After & AX(})
            let tmp = Box::new(CTL::EX(Direction::Forward, tmp)); // Ex (After & AX (}))
                                                                  // eprintln!("ln - {}", ln);
            let a1 = aux(&dots.children[0], None, pim, ln);
            // eprintln!("ln2 - {}", ln);
            let a1 = Box::new(CTL::And(Strict::Strict, a1, tmp));
            return Box::new(CTL::Exists(false, MetavarName::new(format!("l{}", (*ln + 1))), a1));
        }

        let s1 = &dots.children[0];
        let s2 = &dots.children[1];

        let mut a1 = aux(s1, None, false, &mut (ln.clone()));

        let mut b1 = aux(s2, None, false, &mut (ln.clone()));
        let b2 = aux(s2, attach_end, false, ln);

        let mut f = |ctl: &mut CTL| match ctl {
            CTL::Pred(p) => p.set_unmodif(),
            CTL::Exists(_keep, _, _) => {}
            _ => {}
        };

        CTL::do_ctl(&mut b1, &mut f);
        CTL::do_ctl(&mut a1, &mut f);

        let tmp1 = CTL::Not(Box::new(CTL::Or(a1, b1)));
        let tmp2 = CTL::AU(Direction::Forward, Strict::Strict, Box::new(tmp1), b2);

        aux(&dots.children[0], Some(Box::new(tmp2)), pim, ln)
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
    ) -> Box<CTL> {
        if snode.children.is_empty() || snode.wrapper.metavar.ismeta() || snode.is_dots {
            if !snode.is_dots {
                //Sets the modif
                let tmpp = if snode.wrapper.is_modded {
                    Box::new(CTL::Pred(Predicate::Match(snode.clone(), Modif::Modif, prev_is_mvar)))
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

                {
                    //if the node is one of the braces, add a label to it
                    let kind = snode.kinds().last().unwrap();
                    let lname;
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
                        let nextctl = Box::new(CTL::And(
                            Strict::Strict,
                            tmpp,
                            Box::new(CTL::AX(
                                Direction::Forward,
                                Strict::Strict,
                                Box::new(CTL::Or(
                                    attach_end,
                                    Box::new(CTL::Pred(Predicate::AfterNode)),
                                )),
                            )),
                        ));

                        Box::new(CTL::Exists(
                            false,
                            MetavarName::new(format!("l{}", *ln + 1)),
                            nextctl,
                        ))
                    } else {
                        let nextctl = Box::new(CTL::And(
                            Strict::Strict,
                            tmpp,
                            Box::new(CTL::AX(Direction::Forward, Strict::Strict, attach_end)),
                        ));

                        nextctl
                    }
                } else {
                    tmpp
                };

                //if there was a lparan this adds the exists lx term

                if snode.wrapper.metavar.ismeta()
                    && snode.wrapper.freevars.contains(&snode.wrapper.metavar)
                {
                    Box::new(CTL::Exists(true, snode.wrapper.metavar.getminfo().0.clone(), nextctl))
                } else {
                    nextctl
                }
            } else {
                handle_dots(snode, attach_end, prev_is_mvar, ln)
            }
        } else if snode.children.len() == 1 {
            let ctl = aux(&snode.children[0], attach_end, false, ln);
            get_kind_pred(ctl, snode.kinds(), prev_is_mvar)
        } else {
            let skind = snode.kinds();
            let mut rev_iter = snode.children.iter().rev().peekable();
            let mut snode = rev_iter.next().unwrap();
            let prev_node = rev_iter.peek().unwrap();

            //Except at the top and bottom of the file
            //All comments are preceded and succeeded by other nodes
            //on the same level. I know it sounds weird.

            let mut spb = prev_node.wrapper.metavar.ismeta()
                || (prev_node.is_dots && dots_has_mv(&prev_node));
            let mut ctl = aux(snode, attach_end, spb, ln);
            // let mut spb: bool;

            while rev_iter.len() != 0 {
                // let p = CTL::AX(Direction::Forward, Strict::Strict, ctl);
                // ctl = Box::new(CTL::And(Strict::Strict, aux(snode), Box::new(p)));

                snode = rev_iter.next().unwrap();
                spb = rev_iter.peek().map_or(false, |x| x.wrapper.metavar.ismeta());
                ctl = aux(snode, Some(ctl), spb, ln);
            }
            get_kind_pred(ctl, skind, prev_is_mvar)
        }
    }

    let ctl = aux(snode, None, false, &mut 0);
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

pub fn make_ctl(
    _patch: &Patch,
) -> GenericCtl<
    <Predicate as Pred>::ty,
    <GenericSubst<MetavarName, BoundValue> as Subs>::Mvar,
    Vec<String>,
> {
    // todo!()
    GenericCtl::True
}
