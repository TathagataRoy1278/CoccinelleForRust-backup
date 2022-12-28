use std::vec;
use syntax;
use syntax::SyntaxElement;

pub fn work_node<'a, D>(
    do_stuff: &dyn Fn(SyntaxElement, &dyn Fn(&SyntaxElement) -> Vec<D>) -> D,
    node: SyntaxElement,
) -> D {
    do_stuff(node, &|node| -> Vec<D> {
        let mut children_with_tokens = vec![];
        match node {
            SyntaxElement::Node(node) => {
                for child in node.children_with_tokens() {
                    children_with_tokens.push(work_node(do_stuff, child));
                }
            }
            SyntaxElement::Token(token) => {
                children_with_tokens.push(do_stuff(
                    SyntaxElement::Token(token.clone()),
                    &|_token| vec![],
                ));
            }
        }
        children_with_tokens
    })
}
