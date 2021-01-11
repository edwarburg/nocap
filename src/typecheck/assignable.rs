use crate::ty::*;
use bumpalo::core_alloc::fmt;
use bumpalo::core_alloc::fmt::{Display, Formatter};

pub(crate) trait CheckAssignable
where
    Self: Display,
{
    // TODO some type context parameter probably needs to be threaded through here
    fn assignable(from: &Self, to: &Self) -> AssignabilityJudgment;

    fn assignable_to(&self, to: &Self) -> AssignabilityJudgment {
        CheckAssignable::assignable(self, to)
    }
}

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Clone)]
pub(crate) enum AssignabilityJudgment {
    Assignable,
    NotAssignable { reason: String },
}

impl AssignabilityJudgment {
    pub(crate) fn and<F>(&self, next: F) -> AssignabilityJudgment
    where
        F: Fn() -> AssignabilityJudgment,
    {
        use AssignabilityJudgment::*;
        match self {
            Assignable => next(),
            not_assignable => not_assignable.to_owned(),
        }
    }

    pub(crate) fn or<F>(&self, next: F) -> AssignabilityJudgment
    where
        F: Fn() -> AssignabilityJudgment,
    {
        use AssignabilityJudgment::*;
        match self {
            Assignable => Assignable,
            _ => next(),
        }
    }
}

impl Display for AssignabilityJudgment {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        use AssignabilityJudgment::*;
        write!(
            f,
            "{}",
            match self {
                Assignable => "assignable",
                NotAssignable { reason } => reason.as_str(),
            }
        )
    }
}

impl AssignabilityJudgment {
    pub(crate) fn not_assignable(reason: String) -> AssignabilityJudgment {
        AssignabilityJudgment::NotAssignable { reason }
    }

    pub(crate) fn is_assignable(&self) -> bool {
        match self {
            AssignabilityJudgment::Assignable => true,
            _ => false,
        }
    }
}

pub(crate) fn check_assign_or<A, F>(
    from1: &A,
    to1: &A,
    from2: &A,
    to2: &A,
    on_fail: F,
) -> AssignabilityJudgment
where
    A: CheckAssignable,
    F: Fn(&AssignabilityJudgment, &AssignabilityJudgment) -> AssignabilityJudgment,
{
    use AssignabilityJudgment::*;
    match from1.assignable_to(to1) {
        Assignable => Assignable,
        lhs_not_assn => match from2.assignable_to(to2) {
            Assignable => Assignable,
            rhs_not_assn => on_fail(&lhs_not_assn, &rhs_not_assn),
        },
    }
}

pub(crate) fn check_assign_and<A, F>(
    from1: &A,
    to1: &A,
    from2: &A,
    to2: &A,
    on_fail: F,
) -> AssignabilityJudgment
where
    A: CheckAssignable,
    F: Fn(&AssignabilityJudgment) -> AssignabilityJudgment,
{
    use AssignabilityJudgment::*;
    match from1.assignable_to(to1) {
        Assignable => match from2.assignable_to(to2) {
            Assignable => Assignable,
            not_assignable => on_fail(&not_assignable),
        },
        not_assignable => on_fail(&not_assignable),
    }
}

impl CheckAssignable for Ty<'_> {
    fn assignable(from: &Self, to: &Self) -> AssignabilityJudgment {
        use AssignabilityJudgment::*;
        match (from, to) {
            (Ty::Unit, Ty::Unit) => Assignable,
            (Ty::Bottom, _) => Assignable,
            (Ty::Variable(_from_name), Ty::Variable(_to_name)) => {
                unimplemented!("type variable assignability");
            }
            (Ty::TyConInv(from_tci), Ty::TyConInv(to_tci)) => from_tci.assignable_to(to_tci),
            // TODO assignability of function types
            _ => {
                AssignabilityJudgment::not_assignable(format!("{} not assignable to {}", from, to))
            }
        }
    }
}

impl CheckAssignable for CapabilityDeclaration {
    fn assignable(from: &Self, to: &Self) -> AssignabilityJudgment {
        if from == to {
            return AssignabilityJudgment::Assignable;
        }

        AssignabilityJudgment::not_assignable(format!("{} != {}", from, to))
    }
}

impl CheckAssignable for CapabilityExpr<'_> {
    fn assignable(from: &Self, to: &Self) -> AssignabilityJudgment {
        use CapabilityExpr::*;
        if from == to {
            return AssignabilityJudgment::Assignable;
        }
        match (from, to) {
            (Cap(from_cd), Cap(to_cd)) => from_cd.assignable_to(to_cd),
            (Cap(from_cd), And(lhs, rhs)) => AssignabilityJudgment::not_assignable(format!(
                "{} can't be both {} and {}",
                from_cd, lhs, rhs
            )),
            (And(from_lhs, from_rhs), And(to_lhs, to_rhs)) => {
                check_assign_and(*from_lhs, *to_lhs, *from_rhs, *to_rhs, |_| {
                    AssignabilityJudgment::not_assignable("".to_owned())
                })
                .or(|| {
                    check_assign_and(*from_lhs, *to_rhs, *from_rhs, *to_lhs, |reason| {
                        reason.to_owned()
                    })
                })
            }
            (And(lhs, rhs), _) => check_assign_or(*lhs, to, *rhs, to, |lhs_reason, rhs_reason| {
                AssignabilityJudgment::not_assignable(format!(
                    "{} is not assignable to {}, because {} and {}",
                    from, to, lhs_reason, rhs_reason
                ))
            }),
            (Or(lhs, rhs), _) => check_assign_and(*lhs, to, *rhs, to, |reason| {
                AssignabilityJudgment::not_assignable(format!(
                    "{} is not assignable to {}, because {}",
                    from, to, reason
                ))
            }),
            (_, Or(lhs, rhs)) => check_assign_or(from, lhs, from, rhs, |lhs_reason, rhs_reason| {
                AssignabilityJudgment::not_assignable(format!(
                    "{} is not assignable to {} | {}; not assignable because {} and {}",
                    from, lhs, rhs, lhs_reason, rhs_reason
                ))
            }),
        }
    }
}

impl CheckAssignable for TypeConstructorInvocation<'_> {
    fn assignable(from: &Self, to: &Self) -> AssignabilityJudgment {
        use crate::typecheck::assignable::AssignabilityJudgment::*;
        if from == to {
            return Assignable;
        }
        match (from, to) {
            (
                TypeConstructorInvocation {
                    constructor: from_const,
                    ..
                },
                TypeConstructorInvocation {
                    constructor: to_const,
                    ..
                },
            ) => {
                if from_const == to_const {
                    match (from.capabilities, to.capabilities) {
                        (None, None) => Assignable,
                        (Some(_), None) => Assignable,
                        (None, Some(to_caps)) => AssignabilityJudgment::not_assignable(format!(
                            "{} does not have capability {}",
                            from, to_caps
                        )),
                        (Some(from_caps), Some(to_caps)) => from_caps.assignable_to(to_caps),
                    }
                } else {
                    AssignabilityJudgment::not_assignable(format!(
                        "{} is not assignable to {}",
                        from_const, to_const
                    ))
                }
            }
        }
    }
}
