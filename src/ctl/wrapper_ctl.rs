use std::rc::Rc;

use crate::{
    engine::ctl_cocci::Predicate, parsing_cocci::{ast0::{MetavarName, Snode}, parse_cocci::Patch}, parsing_rs::ast_rs::Rnode
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

pub fn make_ctl(patch: &Patch) -> GenericCtl<<Predicate as Pred>::ty, <GenericSubst<MetavarName, Rc<Rnode>> as Subs>::Mvar, Vec<String>> {
    GenericCtl::True
}

