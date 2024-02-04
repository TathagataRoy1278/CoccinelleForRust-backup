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
pub enum WrappedBinding<Pred, Value> {
    ClassicVal(Value),
    PredVal(Modif<Pred>),
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

pub fn make_ctl_simple(mut snodes: Vec<Snode>) -> CTL {
    if snodes.len() == 0 {
        return CTL::True;
    }
    // fn aux(snode: &Snode) -> Box<CTL> {
    //     if snode.children.is_empty() {
    //         return Box::new(CTL::Pred(Predicate::Match(
    //             snode.clone(),
    //             Modif::Unmodif(snode.clone()),
    //         )));
    //     } else if snode.children.len() == 1 {
    //         return aux(&snode.children[0]);
    //     } else {
    //         let mut rev_iter = snode.children.iter().rev();
    //         let mut ctl = aux(rev_iter.next().unwrap());

    //         for (i, snode) in rev_iter.enumerate() {
    //             let p = CTL::AX(Direction::Forward, Strict::Strict, ctl);
    //             ctl = Box::new(CTL::And(Strict::Strict, aux(snode), Box::new(p)));
    //         }
    //         ctl
    //     }
    // }

    fn get_kind_pred(ctl: Box<CTL>, kind: SyntaxKind) -> Box<CTL> {
        let kind_pred = Box::new(CTL::Pred(Predicate::Kind(kind)));
        let fctl = CTL::And(
            Strict::Strict,
            kind_pred,
            Box::new(CTL::AX(Direction::Forward, Strict::Strict, ctl)),
        );
        Box::new(fctl)
    }

    fn aux(snode: &Snode, attach_end: Option<Box<CTL>>) -> Box<CTL> {
        if snode.children.is_empty() {
            let c =
                Box::new(CTL::Pred(Predicate::Match(snode.clone(), Modif::Unmodif(snode.clone()))));
            if let Some(attach_end) = attach_end {
                Box::new(CTL::And(
                    Strict::Strict,
                    c,
                    Box::new(CTL::AX(Direction::Forward, Strict::Strict, attach_end)),
                ))
            }
            else {
                c
            }
            
        } else if snode.children.len() == 1 {
            let ctl = aux(&snode.children[0], attach_end);
            get_kind_pred(ctl, snode.kind())
        } else {
            let skind = snode.kind();
            let mut rev_iter = snode.children.iter().rev();
            let snode = rev_iter.next().unwrap();
            let mut ctl = aux(snode, attach_end);

            for snode in rev_iter {
                // let p = CTL::AX(Direction::Forward, Strict::Strict, ctl);
                // ctl = Box::new(CTL::And(Strict::Strict, aux(snode), Box::new(p)));
                ctl = aux(snode, Some(ctl));
            }
            get_kind_pred(ctl, skind)
        }
    }

    let f = snodes.remove(snodes.len() - 1);
    let ctl = aux(&f, None);
    *snodes.iter().rev().fold(ctl, |ctl, snode| {
        todo!();
        let p = CTL::AX(Direction::Forward, Strict::Strict, ctl);
        Box::new(CTL::And(Strict::Strict, aux(snode, None), Box::new(p)))
    })
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
