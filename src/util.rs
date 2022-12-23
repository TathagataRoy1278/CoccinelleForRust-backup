use syntax::SyntaxNode;

#[macro_export]
macro_rules! syntaxerror {
    ($lino: expr, $err:literal) => {
        panic!("{:?} at line:{:?}",
                 $err,
                 $lino)
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
    match &mut v[..3] {
        [a, b, c] => [a, b, c],
        _ => {
            panic!("Does not have three elements")
        }
    }
}
