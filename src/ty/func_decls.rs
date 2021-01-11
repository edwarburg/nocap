use std::fmt;
use std::fmt::Display;

use crate::ty::CapabilityExpr;
use crate::ty::Ty;
use crate::typecheck::{Identifiable, Name};

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Clone)]
pub struct FunctionType<'tc> {
    pub formal_args: Vec<FunctionFormalArg<'tc>>,
    pub return_type: &'tc Ty<'tc>,
    pub output_capability_constraints: Vec<ArgCapConstraint<'tc>>,
}

impl Display for FunctionType<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<TODO some func type>")
    }
}

#[derive(Debug, Ord, PartialOrd, Eq, PartialEq, Clone)]
pub struct FunctionDeclaration<'tc> {
    pub name: Name,
    pub ty: FunctionType<'tc>,
}

impl<'tc> Identifiable<Name> for FunctionDeclaration<'tc> {
    fn get_id(&self) -> Name {
        self.name
    }
}

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Copy, Clone)]
pub struct FunctionFormalArg<'tc> {
    pub name: Name,
    pub ty: &'tc Ty<'tc>,
}

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Clone)]
pub struct ArgCapConstraint<'tc> {
    pub name: Name,
    pub constraints: Vec<CapConstraint<'tc>>,
}

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Copy, Clone)]
pub enum CapConstraint<'tc> {
    Add(&'tc CapabilityExpr<'tc>),
    Sub(&'tc CapabilityExpr<'tc>),
}
