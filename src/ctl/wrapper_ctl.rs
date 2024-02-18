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

    fn aux(snode: &Snode, attach_end: Option<Box<CTL>>, prev_is_mvar: bool) -> Box<CTL> {
        if snode.children.is_empty() {
            eprintln!("snode - {}", snode.getstring());
            let c = if snode.wrapper.is_modded {
                //is minused or has pluses attached to it
                Box::new(CTL::Exists(
                    true,
                    MetavarName::create_v(),
                    Box::new(CTL::Pred(Predicate::Match(snode.clone(), Modif::Modif, prev_is_mvar))),
                ))
            } else {
                Box::new(CTL::Pred(Predicate::Match(snode.clone(), Modif::Unmodif, prev_is_mvar)))
            };

            if let Some(attach_end) = attach_end {
                Box::new(CTL::And(
                    Strict::Strict,
                    c,
                    Box::new(CTL::AX(Direction::Forward, Strict::Strict, attach_end)),
                ))
            } else {
                c
            }
        } else if snode.children.len() == 1 {
            let ctl = aux(&snode.children[0], attach_end, false);
            get_kind_pred(ctl, snode.kind(), prev_is_mvar)
        } else {
            let skind = snode.kind();
            let mut rev_iter = snode.children.iter().rev().peekable();
            let mut snode = rev_iter.next().unwrap();
            let mut spb = rev_iter.peek().unwrap().wrapper.metavar.ismeta();
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

    // let f = snodes.remove(snodes.len() - 1);
    // let ctl = aux(&f, None);
    // *snodes.iter().rev().fold(ctl, |ctl, snode| {
    //     todo!();
    //     let p = CTL::AX(Direction::Forward, Strict::Strict, ctl);
    //     Box::new(CTL::And(Strict::Strict, aux(snode, None), Box::new(p)))
    // })

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
