use crate::parsing_rs::ast_rs::Rnode;

enum node1<'a> {
    TopNode,
    EndNode,
    Item(&'a Rnode), //For nodes under SourceFile
    //Each item should be disjoint
    SeqStart(&'a Rnode), // {
    SeqEnd(&'a Rnode),   // }

    ExprStmt(&'a Rnode),

    IfHeader(&'a Rnode),
    Else(&'a Rnode),
    WhileHeader(&'a Rnode),
    ForHeader(&'a Rnode),
    LoopHeader(&'a Rnode),
    MatchHeader(&'a Rnode),
}

struct nodeinfo {
    labels: Vec<usize>,
    bclabels: Vec<usize>,
    is_loop: bool,
    is_fake: bool,
}

type node<'a> = (node1<'a>, nodeinfo);
