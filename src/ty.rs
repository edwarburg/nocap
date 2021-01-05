use crate::ast;
use crate::ast::TypeExpr;
use crate::type_check::{AssignabilityJudgment, Assignable, Name, TypeContext, TypeError};
use crate::type_constructors::TypeConstructorInvocation;
use core::fmt;
use core::fmt::{Display, Formatter};
use core::option::Option::None;
use core::result::Result;
use core::result::Result::Ok;

/// The type checker's view of a type. Interned in TypeContext.
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Clone)]
pub enum Ty<'tc> {
    Variable(Name),
    TyConInv(TypeConstructorInvocation<'tc>),
}

impl<'tc> Ty<'tc> {
    pub fn from_type_expr(
        expr: &ast::TypeExpr,
        type_context: &'tc TypeContext<'tc>,
    ) -> Result<&'tc Ty<'tc>, TypeError> {
        match expr {
            TypeExpr::Variable(v) => Ok(type_context.intern_ty(Ty::Variable(v.name))),
            TypeExpr::TyConstInv(tci) => {
                let constructor = type_context
                    .lookup_type_constructor(tci.constructor.name)
                    .ok_or_else(|| format!("No type constructor named {}", tci.constructor.name))?;
                // TODO do type parameters and capabilities
                let type_parameter_bindings = Vec::new();
                let capabilities = None;
                let new_tci = TypeConstructorInvocation {
                    constructor,
                    type_parameter_bindings,
                    capabilities,
                };
                Ok(type_context.intern_ty(Ty::TyConInv(new_tci)))
            }
        }
    }
}

impl Assignable for Ty<'_> {
    fn assignable(from: &Self, to: &Self) -> AssignabilityJudgment {
        match (from, to) {
            (Ty::Variable(_from_name), Ty::Variable(_to_name)) => {
                unimplemented!("type variable assignability");
            }
            (Ty::TyConInv(from_tci), Ty::TyConInv(to_tci)) => from_tci.assignable_to(to_tci),
            _ => {
                AssignabilityJudgment::not_assignable(format!("{} not assignable to {}", from, to))
            }
        }
    }
}

impl Display for Ty<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        use Ty::*;
        match self {
            Variable(name) => write!(f, "{}", name)?,
            TyConInv(tci) => write!(f, "{}", tci)?,
        }
        Ok(())
    }
}
