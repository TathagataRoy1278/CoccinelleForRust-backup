// SPDX-License-Identifier: GPL-2.0

use std::fmt::Debug;
use std::hash::{Hash, Hasher};

use itertools::izip;
use ra_parser::SyntaxKind;
use ra_syntax::{SyntaxElement, SyntaxNode};
use std::io::Write;
use tempfile::NamedTempFile;
use SyntaxKind::*;

use crate::commons::info;

type VirtualPosition = (info::ParseInfo, usize);

#[derive(Clone, PartialEq)]
pub enum ParseInfo {
    /* Present both in ast and list of tokens */
    OriginTok(info::ParseInfo),
    /* Present only in ast and generated after parsing. Used mainly
     * by Julia, to add stuff at virtual places, beginning of func or decl */
    FakeTok(String, VirtualPosition),
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Danger {
    DangerStart,
    DangerEnd,
    Danger,
    NoDanger,
}

#[derive(Eq, PartialEq, Clone)]
pub struct Wrap {
    pub info: info::ParseInfo,
    index: usize,
    //cocci_tag: Option<Vec<Mcodekind>>,
    danger: Danger,
    pub wspaces: (String, String),
    pub isremoved: bool,
    pub plussed: (Vec<Rnode>, Vec<Rnode>),
    pub(crate) exp_ty: Option<String>,
}

impl Hash for Wrap {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.info.hash(state);
        self.index.hash(state);
        self.danger.hash(state);
        self.wspaces.hash(state);
        self.plussed.hash(state)
    }
}

impl Wrap {
    pub fn new(
        info: info::ParseInfo,
        index: usize,
        //cocci_tag: Option<Vec<Mcodekind>>,
        danger: Danger,
    ) -> Wrap {
        Wrap {
            info: info,
            index: index,
            //cocci_tag: cocci_tag,
            danger: danger,
            wspaces: (String::new(), String::new()),
            isremoved: false,
            plussed: (vec![], vec![]),
            exp_ty: None,
        }
    }

    pub fn set_type(&mut self, ty: Option<String>) {
        self.exp_ty = ty;
    }

    pub fn get_type(&self) -> Option<&String> {
        return self.exp_ty.as_ref();
    }

    pub fn dummy(nc: usize) -> Wrap {
        let wp = if nc == 0 {
            (String::from(" "), String::from(""))
        } else {
            (String::new(), String::new())
        };
        Wrap {
            info: info::ParseInfo::new(String::new(), 0, 0, 0, 0, 0, String::new()),
            index: 0,
            //cocci_tag: None,
            danger: Danger::NoDanger,
            wspaces: wp,
            isremoved: false,
            plussed: (vec![], vec![]),
            exp_ty: None,
        }
    }
}

#[derive(Eq, Hash, Clone)]
pub struct Rnode {
    pub wrapper: Wrap,
    astnode: Option<SyntaxElement>, //Not SyntaxNode because we need to take
    pub kind: SyntaxKind,
    //care of the whitespaces
    pub children: Vec<Rnode>,
}

impl PartialEq for Rnode {
    fn eq(&self, other: &Self) -> bool {
        other.equals(other)
    }
}

impl Rnode {
    pub fn new(
        wrapper: Wrap,
        astnode: Option<SyntaxElement>,
        kind: SyntaxKind,
        children: Vec<Rnode>,
    ) -> Rnode {
        return Rnode { wrapper, astnode, kind, children };
    }

    pub fn astnode(&self) -> Option<&SyntaxNode> {
        return self.astnode.as_ref().and_then(|x| x.as_node());
    }

    pub fn totoken(&self) -> String {
        self.astnode.as_ref().unwrap().to_string()
    }

    pub fn kind(&self) -> SyntaxKind {
        self.kind
    }

    pub fn unwrap(&self) -> (SyntaxKind, &[Rnode]) {
        (self.kind(), &self.children[..])
    }

    fn print_tree_aux(&self, pref: &String) {
        println!("{}{:?}", pref, self.kind());
        let mut newbuf = String::from(pref);
        newbuf.push_str(&String::from("--"));
        for child in &self.children {
            child.print_tree_aux(&newbuf)
        }
    }

    pub fn print_tree(&self) {
        //stticly debug function
        self.print_tree_aux(&String::from("--"));
    }

    pub fn getstring(&self) -> String {
        let mut data = String::new();

        //pluses before current node
        for plusbef in &self.wrapper.plussed.0 {
            data.push_str(&plusbef.getstring());
            data.push(' ');
        }

        // Spaces before the node
        if self.wrapper.wspaces.0.contains("/*COCCIVAR*/") {
            data.push_str(" ");
        } else {
            if !self.wrapper.isremoved {
                data.push_str(&format!("{}", self.wrapper.wspaces.0));
            }
        }

        //Main node
        if self.children.len() == 0 && !self.wrapper.isremoved {
            data.push_str(&format!("{}", self.totoken()));
        } else {
            for i in &self.children {
                data.push_str(&i.getstring());
            }
        }

        // Spaces after the node
        if !self.wrapper.isremoved {
            data.push_str(&format!("{}", self.wrapper.wspaces.1));
        }

        //plusses after current node
        for plusaft in &self.wrapper.plussed.1 {
            //    println!("plusaft - {:?}", self.astnode.to_string());
            data.push_str(&plusaft.getstring());
        }

        return data;
    }

    pub fn getunformatted(&self) -> String {
        // Note
        // All consecuting pluses are printed in one line
        // seperated by only spaces

        let mut data = String::new();

        // Pluses before current node
        if self.wrapper.plussed.0.len() != 0 {
            data.push_str("/*COCCIVAR*/");
            for plusbef in &self.wrapper.plussed.0 {
                data.push_str(&plusbef.getunformatted());
                data.push(' ');
            }
        }

        // Spaces before curent node
        if !self.wrapper.isremoved {
            //eprintln!("{:?} \"{}\"", data, self.wrapper.wspaces.0);
            data.push_str(&format!("{}", self.wrapper.wspaces.0));
        }

        // Main node
        if self.children.len() == 0 && !self.wrapper.isremoved {
            data.push_str(&format!("{}", self.totoken()));
        } else {
            for i in &self.children {
                data.push_str(&i.getunformatted());
            }
        }

        // Spaces after node
        if !self.wrapper.isremoved {
            //eprintln!("{:?} \"{}\"", data, self.wrapper.wspaces.1 );
            data.push_str(&format!("{}", self.wrapper.wspaces.1));
        }

        // Plusses after current node
        if self.wrapper.plussed.1.len() != 0 {
            data.push_str("/*COCCIVAR*/");
            for plusaft in &self.wrapper.plussed.1 {
                //    println!("plusaft - {:?}", self.astnode.to_string());
                data.push_str(&plusaft.getunformatted());
            }
        }

        //println!("returning - {}", data);
        return data;
    }

    pub fn writetotmpnamedfile(&self, randfile: &NamedTempFile) {
        let data = self.getstring();
        randfile.as_file().write_all(data.as_bytes()).expect("The project directory must be writable by cfr");
        //write!(randfile, "{}", &data).expect("The project directory must be writable by cfr.");
    }

    pub fn writeunformatted(&self, randfile: &NamedTempFile) {
        let data = self.getunformatted();
        randfile.as_file().write_all(data.as_bytes()).expect("The project directory must be writable by cfr");
        //write!(randfile, "{}", &data).expect("The project directory must be writable by cfr.");
    }

    pub fn isid(&self) -> bool {
        match self.kind() {
            PATH | PATH_SEGMENT | NAME | NAME_REF => return true,
            _ => {
                return self.ispat();
            }
        }
    }

    pub fn islifetime(&self) -> bool {
        return self.kind() == LIFETIME_ARG;
    }

    pub fn isitem(&self) -> bool {
        use SyntaxKind::*;

        match self.kind() {
            CONST | ENUM | EXTERN_BLOCK | EXTERN_CRATE | FN | IMPL | MACRO_CALL | MACRO_RULES
            | MACRO_DEF | MODULE | STATIC | STRUCT | TRAIT | TRAIT_ALIAS | TYPE_ALIAS | UNION
            | USE => true,
            _ => false,
        }
    }

    pub fn isparam(&self) -> bool {
        match self.kind() {
            PARAM | SELF_PARAM => true,
            _ => false,
        }
    }

    pub fn ispat(&self) -> bool {
        match self.kind() {
            IDENT_PAT | BOX_PAT | REST_PAT | LITERAL_PAT | MACRO_PAT | OR_PAT | PAREN_PAT
            | PATH_PAT | WILDCARD_PAT | RANGE_PAT | RECORD_PAT | REF_PAT | SLICE_PAT
            | TUPLE_PAT | TUPLE_STRUCT_PAT | CONST_BLOCK_PAT => true,
            _ => false,
        }
    }

    pub fn istype(&self) -> bool {
        use SyntaxKind::*;

        match self.kind() {
            ARRAY_TYPE | DYN_TRAIT_TYPE | FN_PTR_TYPE | FOR_TYPE | IMPL_TRAIT_TYPE | INFER_TYPE
            | MACRO_TYPE | NEVER_TYPE | PAREN_TYPE | PATH_TYPE | PTR_TYPE | REF_TYPE
            | SLICE_TYPE | TUPLE_TYPE => true,
            //NAME is not a type but, since we want to alter struct/enum
            //definitions too we include that
            _ => false,
        }
    }

    pub fn isexpr(&self) -> bool {
        match self.kind() {
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
            | LITERAL
            | NAME_REF => true,
            _ => false,
        }
    }

    pub fn equals(&self, node: &Rnode) -> bool {
        if self.children.len() != node.children.len() {
            return false;
        } else if self.children.len() == 0 && node.children.len() == 0 {
            return self.totoken() == node.totoken();
        } else {
            for (a, b) in izip!(&self.children, &node.children) {
                if !a.equals(b) {
                    return false;
                }
            }
            return true;
        }
    }

    pub fn getpos(&self) -> (usize, usize) {
        (self.wrapper.info.charstart, self.wrapper.info.charend)
    }

    pub fn get_spaces_right(&self) -> String {
        let len = self.children.len();
        if len == 0 {
            //eprintln!("{} RIGHT \"{}\"", node.getunformatted(), estring);
            return self.wrapper.wspaces.1.clone();
        } else {
            //println!("deeper to {:?}", node.children[len - 1].kind());
            return self.children[len - 1].get_spaces_right();
        }
    }
    
}

impl Debug for Rnode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Rnode")
            .field("astnode", &self.getunformatted())
            .field("children", &self.children)
            .finish()
    }
}
