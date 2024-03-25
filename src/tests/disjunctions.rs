#![allow(dead_code)]
use super::transformationtest::TransformTest;

static DISJTESTS: TransformTest = TransformTest { prefix: "./src/tests/disjunctions/" };

#[test]
pub fn test1() {
    assert!(DISJTESTS.testtransformation("test1.cocci", "test1.rs", "expected1.rs"))
}

#[test]
pub fn test2() {
    assert!(DISJTESTS.testtransformation("test2.cocci", "test2.rs", "expected2.rs"))
}

#[test]
pub fn test3() {
    assert!(DISJTESTS.testtransformation("test3.cocci", "test3.rs", "expected3.rs"))
}

#[test]
pub fn test4() {
    assert!(DISJTESTS.testtransformation("test4.cocci", "test4.rs", "expected4.rs"))
}
