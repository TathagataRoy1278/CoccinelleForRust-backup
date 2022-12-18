use std::process::Child;

use ide_db::line_index::{LineIndex};
use parser::SyntaxKind;
use syntax::{AstNode};
use crate::wrap::{Rnode, Syntax, fill_wrap, wrap};
use crate::visitor_ast0::ast0::worker;
pub use crate::wrap::visit_keyword;

impl wrap{
    pub fn set_test_exps(&mut self){
        self.true_if_test = true;
        self.true_if_test_exp = true;
    }
}

pub fn process_exp(exp: &mut Rnode){
    exp.wrapper.set_test_exps();
    match exp.astnode.kind(){
        SyntaxKind::PAREN_EXPR => {
            match &mut exp.children[..3]{
                [_lp, exp, _rp] => {
                    process_exp(exp);
                }
                _ => {}
            }
        }
        _ => {}
    }
}


pub fn visit_node<'a>(
    worker: &mut worker<Rnode>,
    lindex: LineIndex,
    node: Box<&dyn AstNode>,
    df: &'a mut dyn FnMut(&mut worker<Rnode>) -> Vec<Rnode>,
) -> Option<Rnode> {
    let mut children = df(worker);//gets node's children by calling befault function

    let mut wrap = fill_wrap(&lindex, node.syntax());//wraps the current node
    match node.syntax().kind(){
        SyntaxKind::IF_EXPR => {
            match &mut children[..3]{
                [_if, cond, _block] => {
                    process_exp(cond);
                }
                _ => {}
            }
        }
        SyntaxKind::WHILE_EXPR => {
            match &mut children[..2]{
                [_while, cond] => {
                    process_exp(cond);
                }
                _ => {}
            }
        }//making necessary changed in the children
        _ => { }
    }
    wrap.set_children(children);//connecting the children to the wrapper
    Some(wrap)
}

pub fn set_test_exps(node: &mut Rnode){
    let children = &mut node.children;
    match node.astnode.kind(){
        SyntaxKind::IF_EXPR => {
            match &mut children[..2]{
                [_if, cond] => {
                    process_exp(cond);
                }
                _ => {}
            }
        }
        SyntaxKind::WHILE_EXPR => {
            match &mut children[..2]{
                [_while, cond] => {
                    process_exp(cond);
                }
                _ => {}
            }
        }//making necessary changed in the children
        _ => { }
    }
    for node in children{
        set_test_exps(node);
    }
}