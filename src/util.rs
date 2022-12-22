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

pub fn syntaxerror(lino: usize, err: &str) {
    let errmsg = if err == "" {
        "SyntaxError"
    } else {
        err
    };
    panic!("{errmsg} at line:{lino}");
}
