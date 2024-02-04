// SPDX-License-Identifier: GPL-2.0

use ra_ide_db::line_index::LineIndex;
use ra_syntax::{SourceFile, SyntaxElement, SyntaxError, SyntaxNode};

use crate::{commons::info::ParseInfo, parsing_cocci::{ast0::Snode, parse_cocci::processcocci}, parsing_rs::visitor_ast::work_node};

use super::ast_rs::{Rnode, Wrap};

pub fn fill_wrap(lindex: &LineIndex, node: &SyntaxElement) -> Wrap {
    let sindex =
        lindex.try_line_col(node.text_range().start()).unwrap_or(lindex.line_col(0.into()));
    let eindex = lindex.try_line_col(node.text_range().end()).unwrap_or(lindex.line_col(0.into()));

    let parse_info = ParseInfo::new(
        String::new(),
        usize::from(node.text_range().start()),
        usize::from(node.text_range().end()),
        sindex.line as usize,
        eindex.line as usize,
        sindex.col as usize,
        String::new(),
    );

    let wrap: Wrap = Wrap::new(parse_info, 0, super::ast_rs::Danger::NoDanger);
    wrap
}

pub fn processrswithsemantics(contents: &str, rnode: SyntaxNode) -> Result<Rnode, String> {
    //TODO put this in ast_rs.rs
    let lindex = LineIndex::new(contents);

    let wrap_node = &|node: SyntaxElement, df: &dyn Fn(&SyntaxElement) -> Vec<Rnode>| -> Rnode {
        let wrapped = fill_wrap(&lindex, &node);
        let kind = node.kind();
        let children = df(&node);
        let rnode = Rnode::new(wrapped, Some(node), kind, children);
        rnode
    };
    Ok(work_node(wrap_node, SyntaxElement::Node(rnode)))
}

fn pretty_print_errors(errors: &[SyntaxError], code: &str, lindex: &LineIndex) -> String {
    let mut ret = String::new();

    for error in errors {
        let linecol = lindex.line_col(error.range().start());
        let line_number = linecol.line as usize;
        let line_char = linecol.col as usize;
        let lines: Vec<&str> = code.lines().collect();
        let start_line = if line_number > 2 { line_number - 2 } else { 0 };
        let end_line =
            if line_number + 2 < lines.len() { line_number + 2 } else { lines.len() - 1 };

        ret.push_str(&format!("Error: {} at char {}\n", error, line_char));
        for (i, line) in lines[start_line..=end_line].iter().enumerate() {
            let line_number = start_line + i + 1;
            ret.push_str(&format!("{:>5}: {}\n", line_number, line));
        }
    }

    return ret;
}

pub fn parse_stmts_snode(contents: &str) -> Vec<Snode> {
    let wrap = format!("@@\n@@\n{}", contents);
    let rule = processcocci(&wrap).0.remove(0);
    let mut node = rule.patch.minus;

    let node =  node.children.remove(0)//Function;
                                .children.remove(3)//BlockExpr
                                .children.remove(0)
                                .children;
    
    return node;

}

pub fn divide_fns(rnode: Rnode) -> Vec<Rnode> {
    return rnode.children;
}

pub fn processrs_old(contents: &str) -> Result<Rnode, String> {
    //TODO put this in ast_rs.rs
    let lindex = LineIndex::new(contents);
    let parse = SourceFile::parse(contents);

    if contents.trim().is_empty() {
        let node = parse.syntax_node();
        let kind = node.kind();
        return Ok(Rnode::new(Wrap::dummy(1), Some(SyntaxElement::Node(node)), kind, vec![]));
    }

    let errors = parse.errors();

    if errors.len() != 0 {
        /*
        let mut errorstr = String::new();
        errorstr.push_str(contents);
        errorstr.push('\n');
        for error in errors {
            let lindex = lindex.line_col(error.range().start());
            errorstr.push_str(&format!(
                "Error : {} at line: {}, col {}\n",
                error.to_string(),
                lindex.line,
                lindex.col
            ));
        }
        */
        return Err(pretty_print_errors(errors, contents, &lindex));
    }
    let root = parse.syntax_node();

    let wrap_node = &|node: SyntaxElement, df: &dyn Fn(&SyntaxElement) -> Vec<Rnode>| -> Rnode {
        let wrapped = fill_wrap(&lindex, &node);
        let children = df(&node);
        let kind = node.kind();
        let node = if children.len() == 0 { Some(node) } else { None };
        let rnode = Rnode::new(
            wrapped, node, //Change this to SyntaxElement
            kind, children,
        );
        rnode
    };

    let rnode = work_node(wrap_node, SyntaxElement::Node(root));
    Ok(rnode)
}


pub fn processrs(contents: &str) -> Result<Vec<Rnode>, String> {
    //TODO put this in ast_rs.rs
    let lindex = LineIndex::new(contents);
    let parse = SourceFile::parse(contents);

    if contents.trim().is_empty() {
        let node = parse.syntax_node();
        let kind = node.kind();
        return Ok(vec![Rnode::new(Wrap::dummy(1), Some(SyntaxElement::Node(node)), kind, vec![])]);
    }

    let errors = parse.errors();

    if errors.len() != 0 {
        /*
        let mut errorstr = String::new();
        errorstr.push_str(contents);
        errorstr.push('\n');
        for error in errors {
            let lindex = lindex.line_col(error.range().start());
            errorstr.push_str(&format!(
                "Error : {} at line: {}, col {}\n",
                error.to_string(),
                lindex.line,
                lindex.col
            ));
        }
        */
        return Err(pretty_print_errors(errors, contents, &lindex));
    }
    let root = parse.syntax_node();

    let wrap_node = &|node: SyntaxElement, df: &dyn Fn(&SyntaxElement) -> Vec<Rnode>| -> Rnode {
        let wrapped = fill_wrap(&lindex, &node);
        let children = df(&node);
        let kind = node.kind();
        let node = if children.len() == 0 { Some(node) } else { None };
        let rnode = Rnode::new(
            wrapped, node, //Change this to SyntaxElement
            kind, children,
        );
        rnode
    };

    let rnode = work_node(wrap_node, SyntaxElement::Node(root));
    Ok(rnode.children)
}
