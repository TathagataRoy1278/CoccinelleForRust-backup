#[derive(Clone, Copy)]
pub struct EdgeIndex(usize);
#[derive(Clone, Copy)]
pub struct NodeIndex(usize);

impl NodeIndex {
    pub fn to_usize(&self) -> usize {
        self.0
    }
}

impl EdgeIndex {
    pub fn to_usize(&self) -> usize {
        self.0
    }
}

#[derive(Clone, Copy)]
pub enum EdgeType {
    Default,
    Children,
}

// impl Into<usize> for EdgeIndex {
//     fn into(self) -> usize {
//         self.0
//     }
// }

// impl Into<usize> for NodeIndex {
//     fn into(self) -> usize {
//         self.0
//     }
// }

pub struct NodeData<K> {
    pub id: usize,
    data: K,
    first_out_edge: Option<EdgeIndex>,
    first_in_edge: Option<EdgeIndex>,
}

impl<K> NodeData<K> {
    pub fn data(&self) -> &K {
        return &self.data;
    }
}

pub struct EdgeData {
    origin: NodeIndex,
    target: NodeIndex,
    edgetype: EdgeType,
    next_edge: Option<EdgeIndex>,
}

impl EdgeData {
    pub fn origin(&self) -> NodeIndex {
        return self.origin;
    }

    pub fn target(&self) -> NodeIndex {
        return self.target;
    }

    pub fn ty(&self) -> EdgeType {
        return self.edgetype;
    }
}

#[derive(Default)]
pub struct Graph<K> {
    pub nodes: Vec<NodeData<K>>,
    pub edges: Vec<EdgeData>,
}

impl<K> Graph<K> {
    pub fn new() -> Graph<K> {
        return Graph { nodes: vec![], edges: vec![] };
    }

    pub fn last_edge_index(&self, x: EdgeIndex) -> EdgeIndex {
        let edge = &self.edges[x.to_usize()];
        match edge.next_edge {
            None => x,
            Some(ei) => self.last_edge_index(ei),
        }
    }

    pub fn add_node(&mut self, data: K) -> NodeIndex {
        let n = self.nodes.len();
        let nd = NodeData { id: n, data: data, first_out_edge: None, first_in_edge: None };
        self.nodes.push(nd);
        NodeIndex(n)
    }

    pub fn get_node(&self, ind: NodeIndex) -> &NodeData<K> {
        return &self.nodes[ind.to_usize()];
    }

    pub fn get_node_mut(&mut self, ind: NodeIndex) -> &mut NodeData<K> {
        return &mut self.nodes[ind.to_usize()];
    }

    pub fn add_edge(&mut self, nodei: NodeIndex, succ: NodeIndex, edgetype: EdgeType) -> EdgeIndex {
        let edge = EdgeData { origin: nodei, target: succ, edgetype: edgetype, next_edge: None };
        let nei = self.edges.len();
        self.edges.push(edge);
        let nodei = nodei.to_usize();

        match self.nodes[nodei].first_out_edge {
            None => {
                self.nodes[nodei].first_out_edge = Some(EdgeIndex(nei));
            }
            Some(ei) => {
                let lastindex = self.last_edge_index(ei).to_usize();
                self.edges[lastindex].next_edge = Some(EdgeIndex(nei));
            }
        }

        match self.nodes[nodei].first_in_edge {
            None => {
                self.nodes[nodei].first_in_edge = Some(EdgeIndex(nei));
            }
            Some(ei) => {
                let lastindex = self.last_edge_index(ei).to_usize();
                self.edges[lastindex].next_edge = Some(EdgeIndex(nei));
            }
        }

        EdgeIndex(nei)
    }

    pub fn add_edges(&mut self, nodei: NodeIndex, succs: Vec<(NodeIndex, EdgeType)>) {
        if succs.is_empty() {
            return;
        }

        let mut liei = None;
        let mut loei = None;
        let mut nei = self.edges.len();
        let nodei = nodei.to_usize();

        for (succ, edgetype) in succs {
            let edge = EdgeData {
                origin: NodeIndex(nodei),
                target: succ,
                edgetype: edgetype,
                next_edge: None,
            };
            self.edges.push(edge);

            match self.nodes[nodei].first_out_edge {
                None => {
                    self.nodes[nodei].first_out_edge = Some(EdgeIndex(nei));
                }
                Some(ei) => {
                    let lastindex = loei.unwrap_or(self.last_edge_index(ei)).to_usize();
                    self.edges[lastindex].next_edge = Some(EdgeIndex(nei));
                }
            }

            loei = Some(EdgeIndex(nei));
            match self.nodes[nodei].first_in_edge {
                None => {
                    self.nodes[nodei].first_in_edge = Some(EdgeIndex(nei));
                }
                Some(ei) => {
                    let lastindex = liei.unwrap_or(self.last_edge_index(ei)).to_usize();
                    self.edges[lastindex].next_edge = Some(EdgeIndex(nei));
                }
            }
            liei = Some(EdgeIndex(nei));

            nei += 1;
        }
    }
}
