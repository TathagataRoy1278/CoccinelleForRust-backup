#![allow(dead_code)]
use super::transformationtest::TransformTest;

static MINUSTEST: TransformTest = TransformTest { prefix: "./src/tests/minuses/" };

#[test]
pub fn test1() {
    assert!(MINUSTEST.testtransformation("test1.cocci", "test1.rs", "expected1.rs"))
}

#[test]
pub fn test2() {
    assert!(MINUSTEST.testtransformation("test2.cocci", "test2.rs", "expected2.rs"))
}

#[test]
pub fn test3() {
    assert!(MINUSTEST.testtransformation("test3.cocci", "test3.rs", "expected3.rs"))
}

#[test]
pub fn test4() {
    assert!(MINUSTEST.testtransformation("test4.cocci", "test4.rs", "expected4.rs"))
}

#[test]
pub fn test5() {
    assert!(MINUSTEST.testtransformation("test5.cocci", "test5.rs", "expected5.rs"))
}
