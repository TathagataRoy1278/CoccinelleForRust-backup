// SPDX-License-Identifier: GPL-2.0

use std::process::Command;

use itertools::Itertools;
use ra_parser::SyntaxKind;
use rand::random;

use crate::{
    ctl::ctl_engine::ENGINE_DOT_FILE,
    parsing_cocci::ast0::{Mcodekind, Snode},
    parsing_rs::{
        ast_rs::{Rcode, Rnode},
        control_flow::Rflow,
    },
};

use regex::Regex;

use super::graphviz::make_graphviz;

static PUNCTUATIONS: [char; 13] = [',', '.', '!', ':', ';', '?', '=', '(', ')', '[', ']', '{', '}'];

#[macro_export]
macro_rules! fail {
    () => {
        return Environment::failed()
    };
}

#[macro_export]
macro_rules! syntaxerror {
    ($lino: expr, $err:expr) => {
        panic!("{} at line:{:?}", $err, $lino)
    };
    ($lino:expr, $err:expr, $name:expr) => {
        panic!("{}: {} at line:{:?}", $name, $err, $lino)
    };
    ($lino: expr, $err:expr) => {
        panic!("{:?}: {}", $lino, $err)
    };
}

#[macro_export]
macro_rules! getnext {
    ($var: expr, $children:expr) => {
        if let Some(child) = $children.next() {
            $var = child;
        } else {
            break;
        }
    };
}

#[macro_export]
macro_rules! debugcocci {
    ($fmt:expr, $($arg:expr),*) => {
        if log::log_enabled!(log::Level::Debug) {
            log::debug!("{}", format!($fmt, $($arg),*));
        }
    };

    ($closure:stmt;) => {
        if log::log_enabled!(log::Level::Debug) {
            $closure
        }
    }
}

#[macro_export]
macro_rules! debugengine {
    ($fmt:expr, $($arg:expr),*) => {
        if log::log_enabled!(log::Level::Debug) {
            log::debug!("{}", format!($fmt, $($arg),*));
        }
    };
}

#[macro_export]
macro_rules! C {
    [$id:ident] => {
        GenericCtl::$id
    };
    [$id:ident, $e:expr] => {
        GenericCtl::$id(Box::new($e))
    };
    [$id:ident, $e1:expr, $e2:expr] => {
        GenericCtl::$id(Box::new($e1), Box::new($e2))
    };
    [$id:ident, $e1:expr, $e2:expr, $e3: expr] => {
        GenericCtl::$id(Box::new($e1), Box::new($e2), Box::new(e3))
    };
    [$id:ident, $e1:expr, $e2:expr, $e3: expr, $e4: expr] => {
        GenericCtl::$id($e1, $e2, Box::new($e3), Box::new($e4))
    };

}

#[macro_export]
macro_rules! satvs {
    ($self:expr, $unchecked:expr, $required:expr, $required_states:expr, $phi:expr, $env:expr, $annot: expr) => {
        $self.sat_verbose_loop(
            $unchecked,
            $required,
            $required_states,
            $annot,
            maxlvl,
            lvl + 1,
            m,
            $phi,
            $env,
        )
    };
}

#[macro_export]
macro_rules! deprecated {
    () => {
        panic!("This code is no longer used.")
    };
}

pub fn tuple_of_2<T>(v: &mut Vec<T>) -> [&mut T; 2] {
    match &mut v[..2] {
        [a, b] => [a, b],
        _ => {
            panic!("Does not have two elements")
        }
    }
}

pub fn tuple_of_3<T>(v: &mut Vec<T>) -> [&mut T; 3] {
    if v.len() != 3 {
        panic!("Should never occur. Length is - {:?}", v.len())
    }
    match &mut v[..3] {
        [a, b, c] => [a, b, c],
        _ => {
            panic!("Does not have three elements")
        }
    }
}

pub fn tuple_of_maybe_3<T>(v: &mut Vec<T>) -> [&mut T; 3] {
    match &mut v[..3] {
        [a, b, c] => [a, b, c],
        _ => {
            panic!("Does not have three elements")
        }
    }
}

pub fn collecttree(node: &Snode, f: &mut dyn FnMut(&Snode)) {
    //use async function to wrap the for loop
    //for other cases TODO
    f(node);
    for child in &node.children {
        collecttree(child, f);
    }
}

pub fn worktree(mut node: &mut Snode, f: &mut dyn FnMut(&mut Snode)) {
    //use async function to wrap the for loop
    //for other cases TODO
    f(&mut node);
    for child in &mut node.children {
        worktree(child, f);
    }
}

pub fn worktree_pure<'a>(node: &'a Snode, f: &mut impl FnMut(&'a Snode)) {
    //use async function to wrap the for loop
    //for other cases TODO
    f(node);
    for child in &node.children {
        worktree_pure(child, f);
    }
}

pub fn worktreernode(mut node: &mut Rnode, f: &mut dyn FnMut(&mut Rnode)) {
    //use async function to wrap the for loop
    //for other cases TODO
    f(&mut node);
    for child in &mut node.children {
        worktreernode(child, f);
    }
}

pub fn worksnode<T>(mut node: &mut Snode, t: T, f: &mut dyn FnMut(&mut Snode, T) -> T) -> T {
    //use async function to wrap the for loop
    //for other cases TODO
    let mut t = f(&mut node, t);
    for child in &mut node.children {
        t = worksnode(child, t, f);
    }
    t
}

pub fn workrnode(node: &mut Rnode, f: &mut dyn FnMut(&mut Rnode) -> bool) {
    //use async function to wrap the for loop
    //for other cases TODO
    let t = f(node);
    //the bool return type specifies if worknode should go deeper
    if !t {
        return;
    }
    for child in &mut node.children {
        workrnode(child, f);
    }
}

pub fn isexpr(node1: &Snode) -> bool {
    use SyntaxKind::*;

    let c = |c: &SyntaxKind| match c {
        TUPLE_EXPR
        | ARRAY_EXPR
        | PAREN_EXPR
        | PATH_EXPR
        | CLOSURE_EXPR
        | IF_EXPR
        | WHILE_EXPR
        | LOOP_EXPR
        | FOR_EXPR
        | CONTINUE_EXPR
        | BREAK_EXPR
        | BLOCK_EXPR
        | RETURN_EXPR
        | YIELD_EXPR
        | LET_EXPR
        | UNDERSCORE_EXPR
        | MACRO_EXPR
        | MATCH_EXPR
        | RECORD_EXPR
        | RECORD_EXPR_FIELD_LIST
        | RECORD_EXPR_FIELD
        | BOX_EXPR
        | CALL_EXPR
        | INDEX_EXPR
        | METHOD_CALL_EXPR
        | FIELD_EXPR
        | AWAIT_EXPR
        | TRY_EXPR
        | CAST_EXPR
        | REF_EXPR
        | PREFIX_EXPR
        | RANGE_EXPR
        | BIN_EXPR
        | EXPR_STMT
        | LITERAL => true,
        _ => false,
    };

    node1.kinds().iter().any(c)
}

pub fn removestmtbraces<'a>(node: &'a mut Snode) {
    //since the patch is wrapped in a function to be parsed
    //this function extracts the stmtlist inside it and removes the curly
    //braces from the start and end of the block

    //This also deals with pluses at the end of a patch which are attached to the
    //ending curly brace
    let stmtlist = &mut node.children[0] //function
        .children[3] //blockexpr
        .children[0]; //stmtlist
    stmtlist.children.remove(0);
    let _tmp = stmtlist.children.remove(stmtlist.children.len() - 1); //right brace

    //I am not sure about the next part of the code
    //will keep it just in case
    //let len = stmtlist.children.len();
    //if len != 0
    //for skipping empty patches
    //{
    //attachback(&mut stmtlist.children[len - 1], tmp.wrapper.plusesbef);
    //}
}

pub fn getstmtlist<'a>(node: &'a Snode) -> &'a Snode {
    //since the patch is wrapped in a function to be parsed
    //this function extracts the stmtlist inside it and removes the curly
    //braces from the start and end of the block
    let stmtlist = &node.children[0] //function
        .children[3] //blockexpr
        .children[0]; //stmtlist
    return stmtlist;
}

// /// Get NameRef from PathType
// pub fn getnrfrompt<'a>(node1: &'a Snode) -> &'a Snode {
//     //This part removes the qualifier from the path
//     let node1 = &node1.children[0]; //Gets path
//     let psegment = match &node1.children[..] {
//         [_qualifier, psegment] => psegment,
//         [psegment] => psegment,
//         _ => {
//             panic!("Path should have 1 or 2 children: qualifier? Pathsegment")
//         }
//     };
//     //Gets rid of the generic args list
//     //For non-type inferenced checks, generic args are skipped
//     let name_ref1 = match &psegment.children.iter().map(|x| x.kinds()).collect_vec()[..] {
//         [Tag::COLON2, Tag::NAME_REF] => &psegment.children[1],
//         [Tag::NAME_REF] | [Tag::NAME_REF, _] | [Tag::NAME_REF, _, _] => &psegment.children[0],
//         _ => {
//             println!(
//                 "{:#?}, {}",
//                 &psegment.children.iter().map(|x| x.kinds()).collect_vec()[..],
//                 psegment.getstring()
//             );
//             panic!("PathSegment not fully implented in exceptional_workon");
//         } //There is one missing branch here: '<' PathType ('as' PathType)? '>'
//           //I am not sure how to handle that branch
//     };

//     return name_ref1;
// }

/// Get NameRef from PathType
// pub fn getnrfrompt_r<'a>(node1: &'a Rnode) -> &'a Rnode {
//     //This part removes the qualifier from the path
//     let node1 = &node1.children[0]; //Gets path
//     let psegment = match &node1.children[..] {
//         [_qualifier, psegment] => psegment,
//         [psegment] => psegment,
//         _ => {
//             panic!("Path should have 1 or 2 children: qualifier? Pathsegment")
//         }
//     };
//     //Gets rid of the generic args list
//     //For non-type inferenced checks, generic args are skipped
//     let name_ref1 = match &psegment.children.iter().map(|x| x.kinds()).collect_vec()[..] {
//         [Tag::COLON2, Tag::NAME_REF] => &psegment.children[1],
//         [Tag::NAME_REF] | [Tag::NAME_REF, _] | [Tag::NAME_REF, _, _] => &psegment.children[0],
//         _ => {
//             println!(
//                 "{:#?}, {}",
//                 &psegment.children.iter().map(|x| x.kinds()).collect_vec()[..],
//                 psegment.getstring()
//             );
//             panic!("PathSegment not fully implented in exceptional_workon");
//         } //There is one missing branch here: '<' PathType ('as' PathType)? '>'
//           //I am not sure how to handle that branch
//     };

//     return name_ref1;
// }

pub fn get_pluses_back(node: &Snode) -> Vec<Snode> {
    let len = node.children.len();
    if len == 0 || !node.wrapper.metavar.isnotmeta() {
        match &node.wrapper.mcodekind {
            Mcodekind::Minus(a) => {
                return a.clone();
            }
            Mcodekind::Context(_, a) => {
                eprintln!("{:?}", a);
                return a.clone();
            }
            _ => {
                eprintln!("does come?");
                return vec![];
            }
        }
    } else {
        //println!("deeper to {:?}", node.children[len - 1].kind());
        return get_pluses_back(&node.children[len - 1]);
    }
}

pub fn get_pluses_front(node: &Snode) -> Vec<Snode> {
    let len = node.children.len();
    if len == 0 || !node.wrapper.metavar.isnotmeta() {
        match &node.wrapper.mcodekind {
            Mcodekind::Minus(a) => {
                return a.clone();
            }
            Mcodekind::Context(a, _) => {
                return a.clone();
            }
            _ => {
                return vec![];
            }
        }
    } else {
        //println!("deeper to {:?}", node.children[len - 1].kind());
        return get_pluses_front(&node.children[0]);
    }
}

pub fn attach_pluses_front(node: &mut Snode, mut plus: Vec<Snode>) {
    if node.children.len() == 0 || !node.wrapper.metavar.isnotmeta() || node.wrapper.isdisj {
        //attach to a token or a metavar
        //a metavar does not always mean a token like an expr may be
        //a path_expr

        if !plus.is_empty() {
            node.wrapper.is_modded = true;
        }
        if plus.len() != 0 {
            debugcocci!(
                "Plus Statements:- {:#?} attached to front of {}:{:?}",
                plus.iter().map(|x| x.getstring()).collect_vec(),
                node.getstring(),
                node.kinds()
            );
        }
        match &mut node.wrapper.mcodekind {
            Mcodekind::Minus(a) => {
                plus.append(a);
                *a = plus;
            }
            Mcodekind::Context(a, _) => {
                plus.append(a);
                *a = plus;
            }
            _ => {}
        }
    } else {
        attach_pluses_front(&mut node.children[0], plus);
    }
}

pub fn attach_pluses_back(node: &mut Snode, plus: Vec<Snode>) {
    let len = node.children.len();
    if len == 0 || !node.wrapper.metavar.isnotmeta() || node.wrapper.isdisj {
        if !plus.is_empty() {
            node.wrapper.is_modded = true;
        }

        if plus.len() != 0 {
            debugcocci!(
                "Plus Statements:- {:#?} attached to back of {}:{:?}",
                plus.iter().map(|x| x.getstring()).collect_vec(),
                node.getstring(),
                node.kinds()
            );
        }
        match &mut node.wrapper.mcodekind {
            Mcodekind::Minus(a) => {
                a.extend(plus);
            }
            Mcodekind::Context(_, a) => {
                a.extend(plus);
            }
            _ => {}
        }
    } else {
        //println!("deeper to {:?}", node.children[len - 1].kind());
        attach_pluses_back(&mut node.children[len - 1], plus);
    }
}

pub fn attach_spaces_left(node: &mut Rnode, mut estring: String) {
    let len = node.children.len();
    if len == 0 {
        //eprintln!("{} LEFT \"{}\"", node.getunformatted(), estring);
        estring.push_str(&node.wrapper.wspaces.0);
        node.wrapper.wspaces.0 = estring;
    } else {
        //println!("deeper to {:?}", node.children[len - 1].kind());
        attach_spaces_left(&mut node.children[0], estring);
    }
}

pub fn attach_spaces_right(node: &mut Rnode, estring: String) {
    let len = node.children.len();
    if len == 0 {
        //eprintln!("{} RIGHT \"{}\"", node.getunformatted(), estring);
        node.wrapper.wspaces.1 = estring;
    } else {
        //println!("deeper to {:?}", node.children[len - 1].kind());
        attach_spaces_right(&mut node.children[len - 1], estring);
    }
}

#[allow(unused)]
pub fn debug_spaces(node: &mut Rnode) {
    workrnode(node, &mut |node: &mut Rnode| {
        println!("{:?} => {:?}", node.getstring(), node.wrapper.wspaces);
        true
    });
}

pub fn remexspaces_(mut s: String) -> String {
    for punctuation in PUNCTUATIONS {
        let old = format!(" *\\{} *", punctuation);
        let new = format!("{}", punctuation);
        let re = Regex::new(&old).unwrap();
        s = re.replace_all(&s, new.as_str()).to_string();
    }

    return s;
}

pub fn is_punc(s: &str) -> bool {
    if s.len() > 1 {
        return false;
    }
    match s.chars().into_iter().next().unwrap() {
        ',' | '.' | '!' | ':' | ';' | '?' | '=' | '(' | ')' | '[' | ']' => true,
        _ => false,
    }
}

pub fn get_rcode(rnodes: &Rcode) -> String {
    rnodes.0.iter().fold(String::new(), |mut acc, rnode| {
        acc.push_str(&rnode.getstring());
        acc
    })
}

pub fn show_cfg(flow: &Rflow) {
    let ra: usize = random();
    let fname_dot = format!("/tmp/.cfg{}.dot", ra);
    let fname_jpg = format!("/tmp/.cfg{}.jpg", ra);

    make_graphviz(flow, &fname_dot);

    Command::new("dot")
        .arg("-Tjpg")
        .arg("-o")
        .arg(&fname_jpg)
        .arg(&fname_dot)
        .status()
        .expect("Could not run dot");

    Command::new("xdg-open").arg(&fname_jpg).spawn().expect("Could not run image-viewer.");

    // let _ = fs::remove_file(fname_dot);
    // let _ = fs::remove_file(fname_jpg);
}

pub fn show_ctl_graph() {
    let ra: usize = random();
    let fname_dot = ENGINE_DOT_FILE;
    let fname_jpg = format!("/tmp/.enginedot{}.jpg", ra);

    Command::new("dot")
        .arg("-Tjpg")
        .arg("-o")
        .arg(&fname_jpg)
        .arg(&fname_dot)
        .status()
        .expect("Could not run dot");

    Command::new("xdg-open").arg(&fname_jpg).spawn().expect("Could not run image-viewer.");

    // let _ = fs::remove_file(fname_dot);
    // let _ = fs::remove_file(fname_jpg);
}
