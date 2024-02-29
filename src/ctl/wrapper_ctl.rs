use std::rc::Rc;

use ra_parser::SyntaxKind;

use crate::{
    ctl::ctl_ast::{Direction, Strict},
    engine::ctl_cocci::{Predicate, SubOrMod},
    parsing_cocci::{
        ast0::{MetavarName, Snode},
        parse_cocci::Patch,
    },
    parsing_rs::ast_rs::Rnode,
};

use super::{
    ctl_ast::{GenericCtl, GenericSubst, Modif},
    ctl_engine::{Graph, Pred, Subs, CTL_ENGINE},
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
    <GenericSubst<MetavarName, SubOrMod> as Subs>::Mvar,
    Vec<String>,
>;

fn dots_has_mv(dots: &Snode) -> bool {
    dots.children[1].wrapper.metavar.ismeta()
}

pub fn make_ctl_simple(mut snode: &Snode, prev_is_mvar: bool) -> CTL {
    fn get_kind_pred(ctl: Box<CTL>, kind: SyntaxKind, prev_is_mvar: bool) -> Box<CTL> {
        let kind_pred = Box::new(CTL::Pred(Predicate::Kind(kind, prev_is_mvar)));
        let fctl = CTL::And(
            Strict::Strict,
            kind_pred,
            Box::new(CTL::AX(Direction::Forward, Strict::Strict, ctl)),
        );
        Box::new(fctl)
    }

    fn handle_dots(dots: &Snode, attach_end: Option<Box<CTL>>, pim: bool) -> Box<CTL> {
        let mut a1 = aux(&dots.children[0], None, false);
        let a2 = a1.clone();
        let mut b1 = aux(&dots.children[1], None, false);
        let b2 = aux(&dots.children[1], attach_end, false);

        let mut f = |ctl: &mut CTL| match ctl {
            CTL::Pred(p) => p.set_unmodif(),
            CTL::Exists(keep, _, _) => {}
            _ => {}
        };

        CTL::do_ctl(&mut b1, &mut f);
        CTL::do_ctl(&mut a1, &mut f);

        let tmp1 = CTL::Not(Box::new(CTL::Or(a1, b1)));
        let tmp2 = CTL::AU(Direction::Forward, Strict::Strict, Box::new(tmp1), b2);
        // let res = CTL::And(
        //     Strict::Strict,
        //     a2,
        //     Box::new(CTL::AX(Direction::Forward, Strict::Strict, Box::new(tmp2))),
        // );

        aux(&dots.children[0], Some(Box::new(tmp2)), pim)
    }

    fn aux(snode: &Snode, attach_end: Option<Box<CTL>>, prev_is_mvar: bool) -> Box<CTL> {
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

        if snode.children.is_empty() || snode.wrapper.metavar.ismeta() || snode.is_dots {
            if !snode.is_dots {
                let tmpp = if snode.wrapper.is_modded {
                    Box::new(CTL::Pred(Predicate::Match(snode.clone(), Modif::Modif, prev_is_mvar)))
                } else {
                    Box::new(CTL::Pred(Predicate::Match(
                        snode.clone(),
                        Modif::Unmodif,
                        prev_is_mvar,
                    )))
                };

                let tmpp = if snode.wrapper.is_modded {
                    //is minused or has pluses attached to it
                    Box::new(CTL::Exists(true, MetavarName::create_v(), tmpp))
                } else {
                    tmpp
                };

                let nextctl = if let Some(mut attach_end) = attach_end {
                    if snode.wrapper.metavar.ismeta() {
                        set_pm_true(&mut attach_end);
                    }

                    Box::new(CTL::And(
                        Strict::Strict,
                        tmpp,
                        Box::new(CTL::AX(Direction::Forward, Strict::Strict, attach_end)),
                    ))
                } else {
                    tmpp
                };

                if snode.wrapper.metavar.ismeta() {
                    Box::new(CTL::Exists(true, snode.wrapper.metavar.getminfo().0.clone(), nextctl))
                } else {
                    nextctl
                }
            } else {
                handle_dots(snode, attach_end, prev_is_mvar)
            }
        } else if snode.children.len() == 1 {
            let ctl = aux(&snode.children[0], attach_end, false);
            get_kind_pred(ctl, snode.kind(), prev_is_mvar)
        } else {
            let skind = snode.kind();
            let mut rev_iter = snode.children.iter().rev().peekable();
            let mut snode = rev_iter.next().unwrap();
            let prev_node = rev_iter.peek().unwrap();

            //Except at the top and bottom of the file
            //All comments are preceded and succeeded by other nodes
            //on the same level. I know it sounds weird.

            let mut spb = prev_node.wrapper.metavar.ismeta()
                || (prev_node.is_dots && dots_has_mv(&prev_node));
            let mut ctl = aux(snode, attach_end, spb);
            // let mut spb: bool;

            while rev_iter.len() != 0 {
                // let p = CTL::AX(Direction::Forward, Strict::Strict, ctl);
                // ctl = Box::new(CTL::And(Strict::Strict, aux(snode), Box::new(p)));

                snode = rev_iter.next().unwrap();
                spb = rev_iter.peek().map_or(false, |x| x.wrapper.metavar.ismeta());
                ctl = aux(snode, Some(ctl), spb);
            }
            get_kind_pred(ctl, skind, prev_is_mvar)
        }
    }

    let ctl = aux(snode, None, false);
    match *ctl {
        CTL::And(_, _, b) => match *b {
            CTL::AX(_, _, b) => *b,
            _ => panic!("Should not be anything but an AX"),
        },
        _ => {
            panic!("Should not be as of now, other than AND")
        }
    }
}

pub fn make_ctl(
    patch: &Patch,
) -> GenericCtl<
    <Predicate as Pred>::ty,
    <GenericSubst<MetavarName, SubOrMod> as Subs>::Mvar,
    Vec<String>,
> {
    // todo!()
    GenericCtl::True
}
