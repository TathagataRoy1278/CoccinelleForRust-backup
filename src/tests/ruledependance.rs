#![allow(dead_code)]
use super::transformationtest::TransformTest;

static RULETEST: TransformTest = TransformTest { prefix: "./src/tests/ruledependance/" };

#[test]
pub fn test1() {
    assert!(RULETEST.testtransformation("test1.cocci", "test1.rs", "expected1.rs"))
}

#[test]
pub fn test2() {
    assert!(RULETEST.testtransformation("test2.cocci", "test2.rs", "expected2.rs"))
}

#[test]
pub fn test3() {
    assert!(RULETEST.testtransformation("test3.cocci", "test3.rs", "expected3.rs"))
}

#[test]
pub fn test4() {
    assert!(RULETEST.testtransformation("test4.cocci", "test4.rs", "expected4.rs"))
}

#[test]
pub fn test5() {
    assert!(RULETEST.testtransformation("test5.cocci", "test5.rs", "expected5.rs"))
}
