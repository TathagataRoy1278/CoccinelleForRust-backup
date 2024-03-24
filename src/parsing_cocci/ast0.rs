// SPDX-License-Identifier: GPL-2.0

use std::collections::HashSet;
use std::fmt::{Debug, Display};
use std::hash::{Hash, Hasher};
use std::process::exit;

use crate::commons::util::collecttree;

use super::visitor_ast0::work_node;
use itertools::Itertools;
use ra_ide_db::line_index::{LineCol, LineIndex};
use ra_parser::SyntaxKind;
use ra_syntax::{SourceFile, SyntaxElement, SyntaxNode};

#[derive(PartialEq, Eq, Clone)]
/// Semantic Path Node
pub struct Snode {
    pub wrapper: Wrap,
    pub is_dots: bool,
    pub asttoken: Option<SyntaxElement>,
    kind: SyntaxKind,
    pub children: Vec<Snode>,
}

impl PartialOrd for Snode {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.getstring().partial_cmp(&other.getstring())
    }
}

impl Ord for Snode {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.getstring().cmp(&other.getstring())
    }
}

impl Hash for Snode {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.wrapper.info.pos_info.cstart.hash(state);
        self.wrapper.info.pos_info.cend.hash(state);
    }
}

pub type Pluses = (Vec<Snode>, Vec<Snode>);

impl Debug for Snode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.getstring())
    }
}

impl<'a> Snode {
    //pub fn new_rloot(wrapper: Wrap, syntax: SyntaxElement, children: Vec<Snode>) -> Snode {
    //    Snode { wrapper: wrapper, astnode: Some(syntax), kind: , children: children }
    //}

    pub fn make_wildcard() -> Snode {
        Snode {
            wrapper: Wrap::make_dummy(),
            is_dots: true,
            asttoken: None,
            kind: SyntaxKind::EXPR_STMT, //No meaning
            children: vec![],
        }
    }

    pub fn set_children(&mut self, children: Vec<Snode>) {
        self.children = children
    }

    pub fn tonode(self) -> SyntaxNode {
        self.asttoken.unwrap().into_node().unwrap()
    }

    pub fn totoken(&self) -> String {
        //panics is element is node
        self.asttoken.as_ref().unwrap().to_string()
    }

    pub fn totokenrec(&self) -> &str {
        fn aux(node: &Snode) -> &str {
            if node.children.len() == 0 {
                return node.asttoken.as_ref().unwrap().as_token().unwrap().text();
            } else {
                return aux(&node.children[0]);
            }
        }

        return aux(self);
    }

    pub fn kind(&self) -> SyntaxKind {
        self.kind
    }

    pub fn getstring(&self) -> String {
        if self.children.len() == 0 {
            if self.asttoken.is_none() {
                return String::new();
            }
            return self.totoken();
        } else if self.children.len() == 1 {
            return String::from(self.children[0].getstring());
        } else {
            let mut tokens: String = String::new();

            for i in &self.children {
                tokens = format!("{} {}", tokens, i.getstring());
            }
            return String::from(tokens.trim());
        }
    }

    fn print_tree_aux(&self, pref: &String) {
        println!(
            "{}{:?}, {:?}: {:?}",
            pref,
            self.kind(),
            self.wrapper.mcodekind,
            self.wrapper.metavar
        );
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

    pub fn istype(&self) -> bool {
        use SyntaxKind::*;

        match self.kind() {
            ARRAY_TYPE | DYN_TRAIT_TYPE | FN_PTR_TYPE | FOR_TYPE | IMPL_TRAIT_TYPE | INFER_TYPE
            | MACRO_TYPE | NEVER_TYPE | PAREN_TYPE | PATH_TYPE | PTR_TYPE | REF_TYPE
            | SLICE_TYPE | TUPLE_TYPE => true,
            _ => false,
        }
    }

    pub fn islifetime(&self) -> bool {
        //NOTE: TYPE_ARG is used because we use the lifetime metavariables
        //may not have a '(quote) so for the semantic patch A<a, b>, a and b
        //can be lifetimes if defined so in the metavar declaration
        match self.kind() {
            SyntaxKind::LIFETIME_ARG | SyntaxKind::TYPE_ARG => true,
            _ => false,
        }
    }

    pub fn isparam(&self) -> bool {
        match self.kind() {
            SyntaxKind::PARAM | SyntaxKind::SELF_PARAM => true,
            _ => false,
        }
    }

    pub fn isid(&self) -> bool {
        use SyntaxKind::*;
        return self.kind() == PATH
            || self.kind() == NAME
            || self.kind() == NAME_REF
            || self.ispat();
    }

    pub fn ispat(&self) -> bool {
        use SyntaxKind::*;
        match self.kind() {
            IDENT_PAT | BOX_PAT | REST_PAT | LITERAL_PAT | MACRO_PAT | OR_PAT | PAREN_PAT
            | PATH_PAT | WILDCARD_PAT | RANGE_PAT | RECORD_PAT | REF_PAT | SLICE_PAT
            | TUPLE_PAT | TUPLE_STRUCT_PAT | CONST_BLOCK_PAT => true,
            _ => false,
        }
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

    pub fn isexpr(&self) -> bool {
        use SyntaxKind::*;

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

    pub fn getdisjs(&'a self) -> (Vec<&'a Snode>, Pluses) {
        if !self.wrapper.isdisj {
            return (vec![], (vec![], vec![]));
        }
        fn collectdisjs<'b>(node: &'b Snode) -> Vec<&'b Snode> {
            //this function also returns the plus at the end of a disjunction
            let mut disjs: Vec<&Snode> = vec![];
            if node.wrapper.isdisj {
                disjs.push(&node.children[2].children[0]); //stmtlist is pushed
                match &node.children[..] {
                    [_ifkw, _cond, _block, _elsekw, ifblock] => {
                        disjs.append(&mut collectdisjs(ifblock));
                    }
                    _ => {}
                }
            }
            return disjs;
        }
        let disjs = collectdisjs(&self);
        return (disjs, self.wrapper.mcodekind.getpluses());
    }

    pub fn get_constants(&self) -> Vec<String> {
        let mut constants: HashSet<String> = HashSet::new();

        let mut f = |node: &Snode| {
            if node.kind().is_keyword() {
                constants.insert(node.totoken());
            }
        };

        collecttree(self, &mut f);

        constants.into_iter().collect_vec()
    }

    pub fn get_pluses(&self) -> Pluses {
        match &self.wrapper.mcodekind {
            Mcodekind::Minus(pluses) => (pluses.clone(), vec![]),
            Mcodekind::Plus => (vec![], vec![]),
            Mcodekind::Context(p1, p2) => (p1.clone(), p2.clone()),
            Mcodekind::Star => todo!(),
        }
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct MetavarName {
    pub rulename: String,
    pub varname: String,
}

impl MetavarName {
    pub fn create_v() -> MetavarName {
        MetavarName { rulename: String::from(""), varname: String::from("_v") }
    }

    pub fn is_v(&self) -> bool {
        self.rulename == "NONE" && self.varname == "_v"
    }    
}

impl Display for MetavarName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", format!("{}.{}", self.rulename, self.varname))
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct Dummy {}

#[derive(PartialEq, Debug, Clone, Copy)]
pub enum MODKIND {
    PLUS,
    MINUS,
    STAR,
}

#[derive(Clone, PartialEq)]
pub struct TokenInfo {
    tline_start: usize,
    tline_end: usize,
    left_offset: usize,
    right_offset: usize,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct PositionInfo {
    pub line_start: usize,
    pub line_end: usize,
    pub logical_start: usize,
    pub logical_end: usize,

    pub column: usize,
    pub cstart: usize,
    pub cend: usize,
    pub offset: usize,
}

impl PositionInfo {
    pub fn new(
        line_start: usize,
        line_end: usize,
        logical_start: usize,
        logical_end: usize,
        column: usize,
        cstart: usize,
        cend: usize,
        offset: usize,
    ) -> PositionInfo {
        PositionInfo {
            line_start: line_start,
            line_end: line_end,
            logical_start: logical_start,
            logical_end: logical_end,
            column: column,
            cstart: cstart,
            cend: cend,
            offset: offset,
        }
    }

    pub fn subtract(&mut self, info: Self) {
        self.line_start -= info.line_start;
        self.line_end -= info.line_start;
    }

    pub fn add(&mut self, info: Self) {
        self.line_start += info.line_start;
        self.line_end += info.line_start;
    }
}

#[derive(PartialEq, Eq, Clone)]
pub struct Info {
    pub pos_info: PositionInfo,
    attachable_start: bool,
    attachable_end: bool,
    strings_before: Vec<(Dummy, PositionInfo)>,
    strings_after: Vec<(Dummy, PositionInfo)>,
    is_symbol_ident: bool,
}

impl Info {
    pub fn new(
        pos_info: PositionInfo,
        attachable_start: bool,
        attachable_end: bool,
        strings_before: Vec<(Dummy, PositionInfo)>,
        strings_after: Vec<(Dummy, PositionInfo)>,
        is_symbol_ident: bool,
    ) -> Info {
        Info {
            pos_info: pos_info,
            attachable_start: attachable_start,
            attachable_end: attachable_end,
            strings_before: strings_before,
            strings_after: strings_after,
            is_symbol_ident,
        }
    }
}

#[derive(Clone, Hash, Debug, PartialEq, Eq)]
pub enum KeepBinding {
    UNITARY,    //Need no info
    NONUNITARY, //Need an env entry
    SAVED,      //Need a witness
}

type Minfo = (MetavarName, KeepBinding, bool); //rulename, metavar name, keepbinding, is_inherited

#[derive(Clone, Hash, Debug, PartialEq, Eq)]
pub enum Mcodekind {
    Minus(Vec<Snode>), //Argument is the replacement
    Plus,
    Context(Vec<Snode>, Vec<Snode>), //pluses before and after context
    Star,
}

impl<'a> Mcodekind {
    pub fn is_context(&self) -> bool {
        match self {
            Mcodekind::Context(_, _) => true,
            _ => false,
        }
    }

    pub fn get_plusesbef_ref_mut(&'a mut self) -> &'a mut Vec<Snode> {
        match self {
            Mcodekind::Context(a, _) => a,
            Mcodekind::Minus(a) => a,
            _ => panic!("No pluses should be attached to Plus or star nodes"),
        }
    }

    pub fn get_plusesaft_ref_mut(&'a mut self) -> &'a mut Vec<Snode> {
        match self {
            Mcodekind::Context(_, a) => a,
            Mcodekind::Minus(a) => a,
            _ => panic!("No pluses should be attached to Plus or star nodes"),
        }
    }

    pub fn get_plusesbef_ref(&'a self) -> &'a Vec<Snode> {
        match self {
            Mcodekind::Context(a, _) => &a,
            Mcodekind::Minus(a) => &a,
            _ => panic!("No pluses should be attached to Plus or star nodes"),
        }
    }

    pub fn get_plusesaft_ref(&'a self) -> &'a Vec<Snode> {
        match self {
            Mcodekind::Context(_, a) => &a,
            Mcodekind::Minus(a) => &a,
            _ => panic!("No pluses should be attached to Plus or star nodes"),
        }
    }

    //Warning: Clones plussed nodes
    pub fn getpluses(&self) -> (Vec<Snode>, Vec<Snode>) {
        match self {
            Mcodekind::Context(a, b) => (a.clone(), b.clone()),
            Mcodekind::Minus(a) => (a.clone(), vec![]),
            _ => panic!("No pluses should be attached to Plus or star nodes"),
        }
    }

    pub fn push_pluses_front(&mut self, pluses: Vec<Snode>) {
        match self {
            Mcodekind::Context(a, _) => {
                a.extend(pluses);
            }
            Mcodekind::Minus(a) => a.extend(pluses),
            _ => {
                panic!("Cannot attach plus to Plus or Star nodes");
            }
        }
    }

    //This function is only invoked on a disjunction node
    pub fn push_pluses_back(&mut self, pluses: Vec<Snode>) {
        match self {
            Mcodekind::Context(_, a) => {
                a.extend(pluses);
            }
            Mcodekind::Minus(a) => a.extend(pluses),
            _ => {
                panic!("Cannot attach plus to Plus or Star nodes");
            }
        }
    }
}

#[derive(Clone, Hash, Debug, Eq)]
pub enum MetaVar {
    NoMeta,
    Exp(Minfo),
    Id(Minfo),
    Type(Minfo),
    Lifetime(Minfo),
    Parameter(Minfo),

    Adt(String, Minfo), //typename, minfo
                        //Adt stands for A DataType as used in RA for
                        //Struct, enum and union
                        //I have not yet added primtiive support
                        //But it should not be hard
}

impl MetaVar {
    pub fn getname(&self) -> &str {
        match self {
            Self::NoMeta => {
                panic!("Should never happen");
            }
            Self::Id(minfo)
            | Self::Exp(minfo)
            | Self::Lifetime(minfo)
            | Self::Type(minfo)
            | Self::Parameter(minfo)
            | Self::Adt(_, minfo) => minfo.0.varname.as_str(),
        }
    }

    pub fn gettype(&self) -> &str {
        match self {
            Self::NoMeta => "None",
            Self::Id(_minfo) => "identifier",
            Self::Exp(_minfo) => "expression",
            Self::Lifetime(_minfo) => "lifetime",
            Self::Type(_minfo) => "type",
            Self::Parameter(_minfo) => "parameter",
            Self::Adt(_, _minfo) => "adt",
        }
    }

    pub fn setbinding(&mut self, binding: KeepBinding) {
        match self {
            Self::NoMeta => {
                panic!("Should not occur.");
            }
            Self::Exp(minfo)
            | Self::Id(minfo)
            | Self::Type(minfo)
            | Self::Lifetime(minfo)
            | Self::Parameter(minfo) => {
                minfo.1 = binding;
            }
            Self::Adt(_, minfo) => {
                minfo.1 = binding;
            }
        }
    }

    pub fn getminfo(&self) -> &Minfo {
        match self {
            Self::NoMeta => {
                panic!("Should not occur.");
            }
            Self::Exp(minfo)
            | Self::Id(minfo)
            | Self::Type(minfo)
            | Self::Lifetime(minfo)
            | Self::Parameter(minfo) => &minfo,
            Self::Adt(_, minfo) => &minfo,
        }
    }

    pub fn getrulename(&self) -> &str {
        match self {
            Self::NoMeta => {
                panic!("Should not occur.");
            }
            Self::Exp(minfo)
            | Self::Id(minfo)
            | Self::Type(minfo)
            | Self::Lifetime(minfo)
            | Self::Parameter(minfo) => &minfo.0.rulename.as_str(),
            Self::Adt(_, minfo) => &minfo.0.rulename.as_str(),
        }
    }

    pub fn new(rulename: &str, name: &str, ty: &MetavarType, isinherited: bool) -> Option<MetaVar> {
        let minfo = (
            MetavarName { rulename: rulename.to_string(), varname: name.to_string() },
            KeepBinding::UNITARY,
            isinherited,
        );
        match ty {
            MetavarType::Expression => Some(Self::Exp(minfo)),
            MetavarType::Identifier => Some(Self::Id(minfo)),
            MetavarType::Type => Some(Self::Type(minfo)),
            MetavarType::Lifetime => Some(Self::Lifetime(minfo)),
            MetavarType::Parameter => Some(Self::Parameter(minfo)),
            MetavarType::Adt(tyname) => Some(Self::Adt(tyname.clone(), minfo)),
        }
    }

    pub fn isnotmeta(&self) -> bool {
        match self {
            MetaVar::NoMeta => true,
            _ => false,
        }
    }

    pub fn ismeta(&self) -> bool {
        match self {
            MetaVar::NoMeta => false,
            _ => true,
        }
    }

    pub fn makeinherited(&self) -> MetaVar {
        let mut inhertited = self.clone();
        match &mut inhertited {
            MetaVar::NoMeta => {}
            MetaVar::Exp(minfo)
            | MetaVar::Id(minfo)
            | MetaVar::Type(minfo)
            | MetaVar::Lifetime(minfo)
            | MetaVar::Parameter(minfo) => {
                minfo.2 = true;
            }
            MetaVar::Adt(_, minfo) => {
                minfo.2 = true;
            }
        }

        return inhertited;
    }

    pub fn isinherited(&self) -> bool {
        match self {
            MetaVar::NoMeta => false,
            MetaVar::Exp(minfo)
            | MetaVar::Id(minfo)
            | MetaVar::Type(minfo)
            | MetaVar::Lifetime(minfo)
            | MetaVar::Parameter(minfo) => minfo.2,
            MetaVar::Adt(_, minfo) => minfo.2,
        }
    }
}

impl PartialEq for MetaVar {
    fn eq(&self, other: &Self) -> bool {
        if self.isnotmeta() && other.isnotmeta() {
            return true;
        } else if self.isnotmeta() ^ other.isnotmeta() {
            return false;
        }
        self.getname() == other.getname() && self.getrulename() == other.getrulename()
    }
}

#[derive(Debug)]
pub enum MetavarType {
    Expression,
    Identifier,
    Type,
    Lifetime,
    Parameter,
    Adt(String),
}

impl MetavarType {
    pub fn build(ty: &str) -> MetavarType {
        //VERY IMP
        //this match should have a string for each MetavarType variant
        match ty {
            //TODO add spellchecks
            //It is common to misspell one of these
            //And then it will be treated as a type
            "expression" => MetavarType::Expression,
            "identifier" => MetavarType::Identifier,
            "type" => MetavarType::Type,
            "lifetime" => MetavarType::Lifetime,
            "parameter" => MetavarType::Parameter,
            datatype => MetavarType::Adt(datatype.to_string()),
        }
    }

    pub fn is_adt(&self) -> bool {
        match self {
            Self::Adt(_) => true,
            _ => false,
        }
    }
}

#[derive(PartialEq, Eq, Clone)]
pub struct Wrap {
    pub info: Info,
    index: usize,
    exp_ty: Option<String>,
    pub metavar: MetaVar,
    true_if_arg: bool,
    pub true_if_test: bool,
    pub true_if_test_exp: bool,
    iso_info: Vec<(String, Dummy)>,
    pub isdisj: bool,
    pub mcodekind: Mcodekind, //McodeKind contains the plusses if any
    pub is_modded: bool,
    pub freevars: Vec<MetaVar>
}

impl Wrap {
    pub fn new(
        info: Info,
        index: usize,
        exp_ty: Option<String>,
        metavar: MetaVar,
        true_if_arg: bool,
        true_if_test: bool,
        true_if_test_exp: bool,
        iso_info: Vec<(String, Dummy)>,
        isdisj: bool,
    ) -> Wrap {
        Wrap {
            info: info,
            index: index,
            exp_ty: exp_ty,
            metavar: metavar,
            true_if_arg: true_if_arg,
            true_if_test: true_if_test,
            true_if_test_exp: true_if_test_exp,
            iso_info: iso_info,
            isdisj: isdisj,
            mcodekind: Mcodekind::Context(vec![], vec![]), //All tokens start out as context
            //before being modified accordingly
            is_modded: false,
            freevars: vec![]
        }
    }

    pub fn make_dummy() -> Wrap {
        let pos_info: PositionInfo = PositionInfo::new(
            //all casted to usize because linecol returns u32
            0, 0, 0, 0, 0, 0, 0, 0,
        );

        let info = Info::new(pos_info, false, false, vec![], vec![], false);
        let wrap: Wrap = Wrap::new(
            info,
            0,
            None, //will be filled later with type inference
            MetaVar::NoMeta,
            false,
            false,
            false,
            vec![],
            false,
        );
        wrap
    }

    pub fn is_ident(&self) -> bool {
        self.info.is_symbol_ident
    }

    pub fn getlinenos(&self) -> (usize, usize) {
        (self.info.pos_info.line_start, self.info.pos_info.line_end)
    }

    pub fn set_logilines_start(&mut self, lino: usize) {
        self.info.pos_info.logical_start = lino;
    }

    pub fn set_logilines_end(&mut self, lino: usize) {
        self.info.pos_info.logical_end = lino;
    }

    pub fn getlogilinenos(&self) -> (usize, usize) {
        (self.info.pos_info.logical_start, self.info.pos_info.logical_end)
    }

    pub fn setmodkind(&mut self, modkind: String) {
        match modkind.as_str() {
            "+" => self.mcodekind = Mcodekind::Plus,
            "-" => self.mcodekind = Mcodekind::Minus(vec![]),
            "*" => self.mcodekind = Mcodekind::Star,
            _ => self.mcodekind = Mcodekind::Context(vec![], vec![]),
        }
    }
}

pub fn fill_wrap(lindex: &LineIndex, node: &SyntaxElement) -> Wrap {
    let cstart = node.text_range().start();
    let cend = node.text_range().end();
    let sindex: LineCol = lindex.line_col(cstart);
    let eindex: LineCol = lindex.line_col(cend);
    let pos_info: PositionInfo = PositionInfo::new(
        //all casted to usize because linecol returns u32
        sindex.line as usize,
        eindex.line as usize,
        0,
        0,
        sindex.col as usize,
        cstart.into(),
        cend.into(),
        node.text_range().start().into(),
    );

    let info = Info::new(pos_info, false, false, vec![], vec![], false);
    let wrap: Wrap = Wrap::new(
        info,
        0,
        None, //will be filled later with type inference
        MetaVar::NoMeta,
        false,
        false,
        false,
        vec![],
        false,
    );
    wrap
}

pub fn parsedisjs<'a>(node: &mut Snode) {
    //for later
    if node.kind() == SyntaxKind::IF_EXPR {
        //println!("does it come here");
        //let ifexpr: IfExpr = IfExpr::cast(node.astnode.into_node().unwrap()).unwrap();//Just checked above
        let cond = &node.children[1]; //this gets the node for condition
        if cond.kind() == SyntaxKind::PATH_EXPR && cond.getstring() == "COCCIVAR" {
            let block = &mut node.children[2].children[0].children;
            //println!("{:?}", block[0].kind());
            block.remove(0);
            block.remove(block.len() - 1);
            node.wrapper.isdisj = true;
            //println!("december slowly creeps into my eptember heart");
        }
    }
}

pub fn wrap_root(contents: &str) -> Snode {
    let lindex = LineIndex::new(contents);

    let parse = SourceFile::parse(contents);
    let errors = parse.errors();

    if errors.len() > 0 {
        for error in errors {
            let lindex = lindex.line_col(error.range().start());

            // To Note:
            // Skipping the next error is a hack to be able to parse
            // fn func(param) { ... } as the compiler needs param to have
            // type specified but the [Rust CFG] https://github.com/rust-lang/rust-analyzer/blob/master/crates/syntax/rust.ungram
            // for param without type. This is for accomodating the parameter
            // metavariable in the semantic patch. This will cause problems
            // when someone actually makes this mistake and param is not a metavar
            // Have to find a more elegant solution to this

            if error.to_string().contains("missing type for function parameter") {
                break;
            }
            eprintln!("Error : {} at line: {}, col {}", error.to_string(), lindex.line, lindex.col);
            eprintln!("{}", parse.syntax_node().to_string());
            exit(1);
        }
    }

    let root = SourceFile::parse(contents).syntax_node();
    let wrap_node = &|lindex: &LineIndex,
                      node: SyntaxElement,
                      modkind: Option<String>,
                      df: &dyn Fn(&SyntaxElement) -> Vec<Snode>|
     -> Snode {
        let mut wrapped = fill_wrap(&lindex, &node);
        wrapped.setmodkind(modkind.unwrap_or(String::new()));
        let kind = node.kind();
        let children = df(&node);
        let node = if children.len() == 0 { Some(node) } else { None };
        let mut snode = Snode {
            wrapper: wrapped,
            is_dots: false,
            asttoken: node, //Change this to SyntaxElement
            kind: kind,
            children: children,
        };
        parsedisjs(&mut snode);

        // DEPRECATED
        // if snode.kind() == SyntaxKind::EXPR_STMT && snode.children.len() == 1 {
        //     // this means there is an expression statement without a ; at the ens
        //     //the reason these are removed because rust-analyzer seems to alter between
        //     //assigning ExprStmt and IfExprs(maybe others too)
        //     return snode.children.into_iter().next().unwrap();
        // }

        snode
    };
    let snode = work_node(&lindex, wrap_node, SyntaxElement::Node(root), None);
    snode
}
