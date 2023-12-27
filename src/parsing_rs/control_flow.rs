use std::marker::PhantomData;

use itertools::Itertools;
use ra_parser::SyntaxKind;
use ra_syntax::ast::IfExpr;

use crate::children_kind;

use super::ast_rs::Rnode;

type Tag = SyntaxKind;

pub struct Node<'a> {
    rnode: &'a Rnode,
}

pub struct CFG<'a> {
    pub next_nodes: Vec<CFG<'a>>,
    pub prev_nodes: Vec<&'a CFG<'a>>, //Is Vec the best thing we can use for this?
    pub rnode: Node<'a>,
}

// impl<'a> CFG<'a> {
//     pub fn attach_node(&'a mut self, rnode: &'a Rnode) -> CFG<'a> {
//         let mut cfg_node = build_cfg_aux(rnode);
//         cfg_node.prev_nodes.push(&self);
//     }
// }

fn build_cfg_aux<'a>(rnode: &'a Rnode, pkind: Option<SyntaxKind>) -> CFG<'a> {
    let mut next_nodes = vec![];
    let mut prev_nodes = vec![];
    let cfg_node = CFG { next_nodes, prev_nodes, rnode: Node { rnode: rnode } };

    match pkind {
        Some(_) => {}
        None => {}
    }

    return cfg_node;
}

pub fn build_cfg<'a>(rnode: &'a Rnode) -> Vec<CFG<'a>> {
    //assume that rnode is a sourcefile
    assert!(rnode.kind() == Tag::SOURCE_FILE);
    let cfgs = vec![];
    for child in &rnode.children {}

    return cfgs;
}
