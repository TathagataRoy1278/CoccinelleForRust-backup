pub struct Graph<K> {
    keys: Vec<K>,
    preds: Vec<Vec<usize>>,
    succs: Vec<Vec<usize>>,
}

impl<K> Graph<K> {
    pub fn add_node(&mut self, node: K) {
        self.keys.push(node);
    }
}
