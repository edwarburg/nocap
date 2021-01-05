use std::fmt;
use std::fmt::{Display, Formatter};

use crate::type_check::{AssignabilityJudgment, Assignable, Identifiable, Name};

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

impl Assignable for CapabilityDeclaration {
    fn assignable(from: &Self, to: &Self) -> AssignabilityJudgment {
        if from == to {
            return AssignabilityJudgment::Assignable;
        }

        AssignabilityJudgment::not_assignable(format!("{} != {}", from, to))
    }
}

impl Assignable for CapabilityExpr<'_> {
    fn assignable(from: &Self, to: &Self) -> AssignabilityJudgment {
        use CapabilityExpr::*;
        if from == to {
            return AssignabilityJudgment::Assignable;
        }
        use crate::type_check;
        match (from, to) {
            (Cap(from_cd), Cap(to_cd)) => from_cd.assignable_to(to_cd),
            (Cap(from_cd), And(lhs, rhs)) => AssignabilityJudgment::not_assignable(format!(
                "{} can't be both {} and {}",
                from_cd, lhs, rhs
            )),
            (And(from_lhs, from_rhs), And(to_lhs, to_rhs)) => {
                type_check::check_assign_and(*from_lhs, *to_lhs, *from_rhs, *to_rhs, |_| {
                    AssignabilityJudgment::not_assignable("".to_owned())
                })
                .or(|| {
                    type_check::check_assign_and(*from_lhs, *to_rhs, *from_rhs, *to_lhs, |reason| {
                        reason.to_owned()
                    })
                })
            }
            (And(lhs, rhs), _) => {
                type_check::check_assign_or(*lhs, to, *rhs, to, |lhs_reason, rhs_reason| {
                    AssignabilityJudgment::not_assignable(format!(
                        "{} is not assignable to {}, because {} and {}",
                        from, to, lhs_reason, rhs_reason
                    ))
                })
            }
            (Or(lhs, rhs), _) => type_check::check_assign_and(*lhs, to, *rhs, to, |reason| {
                AssignabilityJudgment::not_assignable(format!(
                    "{} is not assignable to {}, because {}",
                    from, to, reason
                ))
            }),
            (_, Or(lhs, rhs)) => {
                type_check::check_assign_or(from, lhs, from, rhs, |lhs_reason, rhs_reason| {
                    AssignabilityJudgment::not_assignable(format!(
                        "{} is not assignable to {} | {}; not assignable because {} and {}",
                        from, lhs, rhs, lhs_reason, rhs_reason
                    ))
                })
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::capabilities::CapabilityDeclaration;

    use super::*;
    use crate::type_check::test_utils::*;
    use crate::type_check::{Arenas, TypeContext};

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
