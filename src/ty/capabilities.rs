use std::fmt;
use std::fmt::{Display, Formatter};

use crate::typecheck::{Identifiable, Name};

/// Declaration of a capability
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Clone)]
pub struct CapabilityDeclaration {
    pub(crate) name: Name,
}

impl CapabilityDeclaration {
    pub fn new(name: Name) -> CapabilityDeclaration {
        CapabilityDeclaration { name }
    }
}

impl Display for CapabilityDeclaration {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl Identifiable<Name> for CapabilityDeclaration {
    fn get_id(&self) -> Name {
        self.name
    }
}

/// either a capability itself, or the intersection/union of two capabilities, recursively.
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Copy, Clone)]
pub enum CapabilityExpr<'tc> {
    Cap(&'tc CapabilityDeclaration),
    And(&'tc CapabilityExpr<'tc>, &'tc CapabilityExpr<'tc>),
    Or(&'tc CapabilityExpr<'tc>, &'tc CapabilityExpr<'tc>),
}

impl Display for CapabilityExpr<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        use CapabilityExpr::*;
        match self {
            Cap(decl) => write!(f, "{}", decl)?,
            And(lhs, rhs) => write!(f, "({}) & ({})", lhs, rhs)?,
            Or(lhs, rhs) => write!(f, "({}) | ({})", lhs, rhs)?,
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::ty::capabilities::CapabilityDeclaration;
    use crate::typecheck::assignable::*;
    use crate::typecheck::test_utils::*;
    use crate::typecheck::{Arenas, TypeContext};

    use super::*;

    macro_rules! with_fixture {
        ($fix:ident, $body:block) => {
            let arenas = Arenas::default();
            let tc = TypeContext::new(&arenas);
            let $fix = Fixture::new(&tc);
            $body
        };
    }

    struct Fixture<'tc> {
        tc: &'tc TypeContext<'tc>,
        cap_a: &'tc CapabilityDeclaration,
        cap_b: &'tc CapabilityDeclaration,
        expr_a: &'tc CapabilityExpr<'tc>,
        expr_b: &'tc CapabilityExpr<'tc>,
        expr_or: &'tc CapabilityExpr<'tc>,
        expr_and: &'tc CapabilityExpr<'tc>,
    }

    impl<'tc> Fixture<'tc> {
        fn new(tc: &'tc TypeContext<'tc>) -> Fixture<'tc> {
            let cap_a = tc.intern_cap_decl(CapabilityDeclaration::new("A"));
            let cap_b = tc.intern_cap_decl(CapabilityDeclaration::new("B"));
            let expr_a = tc.intern_cap_expr(CapabilityExpr::Cap(cap_a));
            let expr_b = tc.intern_cap_expr(CapabilityExpr::Cap(cap_b));
            Fixture {
                tc,
                cap_a,
                cap_b,
                expr_a,
                expr_b,
                expr_or: tc.intern_cap_expr(CapabilityExpr::Or(expr_a, expr_b)),
                expr_and: tc.intern_cap_expr(CapabilityExpr::And(expr_a, expr_b)),
            }
        }
    }

    #[test]
    fn cap_assignable_to_self() {
        with_fixture!(fix, {
            assert!(fix.cap_a.assignable_to(&fix.cap_a).is_assignable());
        });
    }

    #[test]
    fn cap_not_assignable_to_other() {
        with_fixture!(fix, {
            assert!(!fix.cap_a.assignable_to(&fix.cap_b).is_assignable());
        });
    }

    #[test]
    fn cap_assignable_to_or_including_it() {
        with_fixture!(fix, {
            assert_assignable_to(fix.expr_a, fix.expr_or);
            assert_assignable_to(fix.expr_b, fix.expr_or);
        });
    }

    #[test]
    fn or_assignable_to_or() {
        with_fixture!(fix, {
            assert_assignable_to(fix.expr_or, fix.expr_or);
            let reverse = fix
                .tc
                .intern_cap_expr(CapabilityExpr::Or(fix.expr_b, fix.expr_a));
            assert_assignable_to(reverse, fix.expr_or);
            assert_assignable_to(fix.expr_or, reverse);
        });
    }

    #[test]
    fn and_assignable_to_and() {
        with_fixture!(fix, {
            assert_assignable_to(fix.expr_and, fix.expr_and);
            let reverse = fix
                .tc
                .intern_cap_expr(CapabilityExpr::And(fix.expr_b, fix.expr_a));
            assert_assignable_to(reverse, fix.expr_and);
            assert_assignable_to(fix.expr_and, &reverse);
        });
    }

    #[test]
    fn or_not_assignable_to_and() {
        with_fixture!(fix, { assert_not_assignable_to(fix.expr_or, fix.expr_and) });
    }

    #[test]
    fn and_assignable_to_or() {
        with_fixture!(fix, { assert_assignable_to(fix.expr_and, fix.expr_or) });
    }
}
