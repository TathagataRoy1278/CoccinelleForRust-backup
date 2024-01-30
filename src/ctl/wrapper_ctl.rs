use std::rc::Rc;

use crate::{
    engine::ctl_cocci::{Predicate, SubOrMod}, parsing_cocci::{ast0::{MetavarName, Snode}, parse_cocci::Patch}, parsing_rs::ast_rs::Rnode
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

//For A...B patches
pub fn make_ctl_simple(s1: &Vec<Snode>, s2: Vec<Snode>) -> GenericCtl<<Predicate as Pred>::ty, <GenericSubst<MetavarName, SubOrMod> as Subs>::Mvar, Vec<String>> {
    
    todo!()
}

pub fn make_ctl(patch: &Patch) -> GenericCtl<<Predicate as Pred>::ty, <GenericSubst<MetavarName, SubOrMod> as Subs>::Mvar, Vec<String>> {
    // todo!()
    GenericCtl::True
}

