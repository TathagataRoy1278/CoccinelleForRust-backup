// SPDX-License-Identifier: GPL-2.0

use ra_ide_db::line_index::LineIndex;
use ra_parser::SyntaxKind;
use ra_syntax::SyntaxElement;
use std::vec;

use crate::commons::{info::WILDCARD, util::worksnode};

use super::ast0::{wrap_root, Snode};

type Tag = SyntaxKind;

fn ttree_to_expr_list(tt: String) -> Vec<Snode> {
    let wrapped = format!(
        "fn func() {{
            fcall({})
        }}",
        tt
    );

    let mut rnode = wrap_root(&wrapped, vec![]);
    let mut args = rnode.children[0] //fn
        .children[3] //blockexpr
        .children[0] //stmtlist
        .children[1] //callexpr
        .children
        .remove(1); //arglist

    //removing sorrounding brackets of fcall
    args.children.remove(0);
    args.children.remove(args.children.len() - 1);

    let info = args.children[0].wrapper.info.clone();

    //This makes it as if the expression starts at the start
    //of the file. Later an offset will be added in the calling
    //function
    args.children.iter_mut().for_each(|x| {
        worksnode(x, (), &mut |node, _| {
            node.wrapper.info.pos_info.subtract(info.pos_info.clone());
        })
    });

    return args.children;

    //let exprlist = node.chil;
}

pub fn work_node<'a>(
    lindex: &LineIndex,
    wrap_node: &dyn Fn(
        &LineIndex,
        SyntaxElement,
        Option<String>,
        &dyn Fn(&SyntaxElement) -> Vec<Snode>,
    ) -> Snode,
    node: SyntaxElement,
    modkind: Option<String>,
) -> Snode {
    wrap_node(lindex, node, modkind, &|node| -> Vec<Snode> {
        let mut children = vec![];
        //let mut children = vec![];
        match node {
            SyntaxElement::Node(node) => {
                let mut modkind: Option<String> = None;
                for child in node.children_with_tokens() {
                    match child.kind() {
                        Tag::WHITESPACE => {}
                        Tag::COMMENT => {
                            let commlen: usize = child.text_range().len().into();
                            if commlen == 5 && lindex.line_col(child.text_range().start()).col == 0
                            {
                                //checks for /*?*/ modifiers
                                modkind =
                                    Some(String::from(child.to_string().as_bytes()[2] as char));
                                //in the next iteration the node gets the modkind
                            }
                            else if child.to_string().eq(WILDCARD) {
                                let wc = Snode::make_wildcard();
                                children.push(wc);
                                modkind = None;
                            }
                        }
                        Tag::TOKEN_TREE => {
                            let mut exprlist =
                                ttree_to_expr_list(child.as_node().unwrap().to_string());
                            let info =
                                work_node(lindex, wrap_node, child, modkind.clone()).wrapper.info;

                            //position is fixed only for errors
                            exprlist.iter_mut().for_each(|x| {
                                worksnode(x, (), &mut |node, _| {
                                    node.wrapper.info.pos_info.add(info.pos_info.clone());
                                })
                            });
                            children.extend(exprlist);
                        }
                        // Tag::PATH_EXPR if child.to_string() == WILDCARD => {
                        //     let snode = Snode::make_wildcard();
                        //     children.push(snode);

                        //     modkind = None;
                        // }
                        // Tag::PARAM if child.to_string() == WILDCARD => {
                        //     let snode = Snode::make_wildcard();
                        //     children.push(snode);

                        //     modkind = None;
                        // }
                        _ => {
                            children.push(work_node(lindex, wrap_node, child, modkind.clone()));
                            modkind = None;
                        }
                    }
                }
            }
            SyntaxElement::Token(_token) => {}
        }
        children
    })
}
