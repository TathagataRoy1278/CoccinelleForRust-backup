// SPDX-License-Identifier: GPL-2.0

use crate::parsing_cocci::ast0::Snode;
use itertools::izip;

#[allow(dead_code)]
fn matcher(a: &Snode, b: &Snode) -> bool {
    match (a.kinds(), b.kinds()) {
        _ => {
            for (e1, e2) in izip!(&a.children, &b.children) {
                if !matcher(e1, e2) {
                    return false;
                }
            }
            true
        }
    }
}
