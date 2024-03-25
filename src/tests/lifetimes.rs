#![allow(dead_code)]
use super::transformationtest::TransformTest;

static RULETEST: TransformTest = TransformTest { prefix: "./src/tests/lifetimes/" };

#[test]
pub fn test1() {
    assert!(RULETEST.testtransformation("test1.cocci", "test1.rs", "expected1.rs"))
}
