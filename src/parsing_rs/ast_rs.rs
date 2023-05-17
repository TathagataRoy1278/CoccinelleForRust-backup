use std::fmt::Debug;

use parser::SyntaxKind;
use syntax::SyntaxElement;

use crate::commons::info;
use crate::parsing_cocci::ast0::Mcodekind;
type VirtualPosition = (info::ParseInfo, usize);

#[derive(Clone)]
pub enum ParseInfo {
    /* Present both in ast and list of tokens */
    OriginTok(info::ParseInfo),
    /* Present only in ast and generated after parsing. Used mainly
    * by Julia, to add stuff at virtual places, beginning of func or decl */
    FakeTok(String, VirtualPosition)
}

#[derive(Clone)]
pub enum Danger {
    DangerStart,
    DangerEnd,
    Danger,
    NoDanger
}

pub struct Wrap<'a> {
    pub info: ParseInfo,
    index: usize,
    cocci_tag: Option<Vec<Mcodekind<'a>>>,
    danger: Danger,
}

impl<'a> Wrap<'a> {
    pub fn new(
        info: ParseInfo,
        index: usize,
        cocci_tag: Option<Vec<Mcodekind>>,
        danger: Danger
    ) -> Wrap {
        Wrap {
            info: info,
            index: index,
            cocci_tag: cocci_tag,
            danger: danger
        }
    }

}


pub struct Rnode<'a> {
    pub wrapper: Wrap<'a>,
    pub astnode: SyntaxElement,//Not SyntaxNode because we need to take
                           //care of the whitespaces
    pub children: Vec<Rnode<'a>>
}

impl<'a> Rnode<'a> {

    pub fn kind(&self) -> SyntaxKind {
        self.astnode.kind()
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

    pub fn isexpr(&self) -> bool {
        use SyntaxKind::{*};

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
            | LITERAL => { true }
            _ => { false }
        }
    }
}

impl<'a> Debug for Rnode<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Rnode").field("astnode", &self.astnode.to_string()).field("children", &self.children).finish()
    }
}