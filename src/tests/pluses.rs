#![allow(dead_code)]
use super::transformationtest::TransformTest;

static PLUSTEST: TransformTest = TransformTest { prefix: "./src/tests/pluses/" };

#[test]
pub fn test1() {
    assert!(PLUSTEST.testtransformation("test1.cocci", "test1.rs", "expected1.rs"))
}

#[test]
pub fn test2() {
    assert!(PLUSTEST.testtransformation("test2.cocci", "test2.rs", "expected2.rs"))
}

#[test]
pub fn test3() {
    assert!(PLUSTEST.testtransformation("test3.cocci", "test3.rs", "expected3.rs"))
}

#[test]
pub fn test4() {
    assert!(PLUSTEST.testtransformation("test4.cocci", "test4.rs", "expected4.rs"))
}
