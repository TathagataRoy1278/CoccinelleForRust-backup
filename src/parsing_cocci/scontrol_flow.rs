use std::rc::Rc;

use itertools::Itertools;

use crate::commons::ograph_extended::{Graph, NodeIndex, EdgeType, NodeData};
use crate::parsing_rs::ast_rs::Rnode;

// enum Node1<'a> {
//     TopNode,
//     EndNode,
//     Item(&'a Rnode), //For nodes under SourceFile
//     //Each item should be disjoint
//     SeqStart(&'a Rnode), // {
//     SeqEnd(&'a Rnode),   // }

//     ExprStmt(&'a Rnode),

//     IfHeader(&'a Rnode),
//     Else(&'a Rnode),
//     WhileHeader(&'a Rnode),
//     ForHeader(&'a Rnode),
//     LoopHeader(&'a Rnode),
//     MatchHeader(&'a Rnode),
// }

pub struct NodeWrap<'a> {
    rnode: &'a Rnode,
    info: NodeInfo,
}

impl<'a> NodeWrap<'a> {
    pub fn rnode(&self) -> &'a Rnode {
        return self.rnode;
    }

    pub fn info(&self) -> NodeInfo {
        return self.info.clone();
    }
}

#[derive(Clone)]
struct NodeInfo {
    labels: usize,
    bclabels: Vec<usize>,
    is_loop: bool,
    is_fake: bool,
}

type Rflow<'a> = Graph<NodeWrap<'a>>;

impl NodeInfo {
    pub fn new(labels: usize) -> NodeInfo {
        return NodeInfo { labels, bclabels: vec![], is_loop: false, is_fake: false };
    }
}

pub fn ast_to_flow<'a>(rnodes: &'a Vec<Rnode>) {
    fn make_graph<'b, 'a: 'b>(graph: &'b mut Graph<NodeWrap<'a>>, rnodes: &'a Vec<Rnode>, label: usize) -> NodeIndex {
        let mut node_indices = vec![];
        for rnode in rnodes {
            let label = label;
            let info = NodeInfo::new(label);
            let node = NodeWrap { rnode, info };

            node_indices.push(graph.add_node(node));
        }

        let fni = node_indices[0];
        for (ni, nni) in node_indices.into_iter().tuples() {
            let node: &NodeData<NodeWrap<'a>> = graph.get_node(ni);
            let nodew: &NodeWrap<'a> = node.data();
            let rnode: &'a Rnode = nodew.rnode;
            match rnode.kind() {
                _ => {
                    let cni = make_graph(graph, &rnode.children, label<<1);
                    graph.add_edge(ni, cni, EdgeType::Children);
                }
            }
            graph.add_edge(ni, nni, EdgeType::Default);
        }

        return fni;
    }

    let mut graph: Graph<NodeWrap<'a>> = Graph::new();
    make_graph(&mut graph, rnodes, 0);
}
