use std::fmt;
use std::fmt::Debug;
use std::ops::Deref;

use bumpalo::core_alloc::fmt::Formatter;

use crate::type_check::Name;

////////////////////////////////////////////////
//                  Shared                    //
////////////////////////////////////////////////

/// An owned pointer to an AstNode
pub struct R<N: AstNode> {
    ptr: Box<N>,
}

impl<N: AstNode> R<N> {
    fn new(node: N) -> Self {
        R {
            ptr: Box::new(node),
        }
    }
}

impl<N: AstNode> Deref for R<N> {
    type Target = N;

    fn deref(&self) -> &Self::Target {
        &self.ptr
    }
}

impl<N: AstNode> Debug for R<N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "R(")?;
        Debug::fmt(&self.ptr, f)?;
        write!(f, ")")
    }
}

/// Provides common implementations for node sub-types (Item, Expr, Ty, Cap, etc).
macro_rules! node_impls {
    ($n:ident, $k:ident) => {
        impl AstNode for $n {
            type Kind = $k;

            fn from_header_and_kind(header: AstHeader, kind: Self::Kind) -> Self {
                // TODO one day this may not be sufficient, if various sub-nodes get more fields...
                $n { header, kind }
            }

            fn header(&self) -> &AstHeader {
                &self.header
            }
            fn kind(&self) -> &Self::Kind {
                &self.kind
            }
        }

        // node into kind
        impl Into<$n> for $k {
            fn into(self) -> $n {
                $n::from_kind(self)
            }
        }

        // node into R
        impl Into<R<$n>> for $n {
            fn into(self) -> R<$n> {
                R::new(self)
            }
        }

        // kind into R
        impl Into<R<$n>> for $k {
            fn into(self) -> R<$n> {
                R::new($n::from_kind(self))
            }
        }

        impl Debug for $n {
            fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
                write!(f, stringify!($n))?;
                write!(f, "(")?;
                Debug::fmt(&self.kind, f)?;
                write!(f, ")")
            }
        }
    };
}

/// Contains shared stuff every AstNode tracks. Span, type, resolved fqn, etc.
#[derive(Debug, Default)]
pub struct AstHeader {
    // TODO span, nodeid, type, etc
}

/// Generally, the interesting parts of a node are stored in the `kind` field. That's where we distinguish
/// between the different types of nodes and store the various references to children etc.
///
/// This wrapper allows us to generalize over any node of a particular type (expr, stmt, etc), as well
/// as track metadata on the node in a header. This header contains things like the span the node
/// represents, as well as any data that's been populated about the node through the various passes
/// - for example, the type checker tags the node with its resolved type (if it's an expression), etc.
pub trait AstNode: Debug + Sized {
    type Kind;

    fn from_header_and_kind(header: AstHeader, kind: Self::Kind) -> Self;
    fn from_kind(kind: Self::Kind) -> Self {
        Self::from_header_and_kind(AstHeader::default(), kind)
    }

    fn header(&self) -> &AstHeader;
    fn kind(&self) -> &Self::Kind;
}

////////////////////////////////////////////////
//                  Units                     //
////////////////////////////////////////////////

/// A compilation unit, eg, a file.
pub struct Unit {
    header: AstHeader,
    kind: UnitKind,
}

#[derive(Debug)]
pub enum UnitKind {
    File(Vec<R<Item>>),
}

node_impls!(Unit, UnitKind);

////////////////////////////////////////////////
//                  Items                     //
////////////////////////////////////////////////

pub struct Item {
    header: AstHeader,
    kind: ItemKind,
}

#[derive(Debug)]
pub enum ItemKind {
    FuncDecl(FunctionSignature),
    FuncDeclWithImpl(FunctionSignature, FunctionImplementation),
}

#[derive(Debug)]
pub struct FunctionSignature {
    // TODO function signature
}

node_impls!(Item, ItemKind);

#[derive(Debug)]
pub struct FunctionImplementation {
    pub body: R<Expr>,
}

pub struct Stmt {
    header: AstHeader,
    kind: StmtKind,
}

#[derive(Debug)]
pub enum StmtKind {
    /// Variable definitions. `let lval: type = rval`
    VarDecl(Ident, Ty, R<Expr>),
    /// assign to an lval. `a = foo`, `foo.a = b`, `foo[i] = c`, etc
    Assign(LVal, R<Expr>),
    /// An expression that appears on a line by itself; typically this is a function invoked for its
    /// side effect.
    Expr(R<Expr>),
}

node_impls!(Stmt, StmtKind);

////////////////////////////////////////////////
//               Expressions                  //
////////////////////////////////////////////////

/// An expression node in the AST.
pub struct Expr {
    pub header: AstHeader,
    pub kind: ExprKind,
}

impl Expr {
    fn new(kind: ExprKind) -> Self {
        Expr {
            header: AstHeader {},
            kind,
        }
    }
}

node_impls!(Expr, ExprKind);

#[derive(Debug)]
pub enum ExprKind {
    /// Identifiers. `Foo`, `bar`, etc
    Ident(Ident),
    /// Variable reference. `foo`, `bar`, etc
    VarRef(Ident),
    /// Blocks of statements, followed by a resulting expression
    /// {
    ///     let a = b;
    ///     a = c;
    ///     a
    /// }
    Block(Vec<R<Stmt>>, R<Expr>),
    /// function invocation. `foo()`, `foo<A>(a, b)`, etc
    Invoke(Ident, Vec<R<Expr>>, Vec<R<Ty>>),
}

#[derive(Debug)]
pub struct Ident {
    pub name: Name,
}

impl Ident {
    fn new(name: Name) -> Ident {
        Ident { name }
    }
}

impl Into<Ident> for Name {
    fn into(self) -> Ident {
        Ident::new(self)
    }
}

#[derive(Debug)]
pub enum LVal {
    Variable(Ident),
}

////////////////////////////////////////////////
//                  Types                     //
////////////////////////////////////////////////

/// The AST's view of a type. Can't perform type analysis using it, but can be converted to type_constructors::Ty with a TypeContext
pub struct Ty {
    header: AstHeader,
    kind: TyKind,
}

#[derive(Debug)]
pub enum TyKind {
    TyVar(Ident),
    TyConstInv(TypeConstructorInvocation),
}

node_impls!(Ty, TyKind);

#[derive(Debug)]
pub struct TypeConstructorInvocation {
    pub constructor: Ident,
    pub actual_type_parameters: Vec<R<Ty>>,
    pub capabilities: Vec<R<Cap>>,
}

impl TypeConstructorInvocation {
    fn noarg_nocap(constructor: Ident) -> Self {
        TypeConstructorInvocation {
            constructor,
            actual_type_parameters: Vec::new(),
            capabilities: Vec::new(),
        }
    }
}

////////////////////////////////////////////////
//              Capabilities                  //
////////////////////////////////////////////////

/// The ast's view of capability expressions
pub struct Cap {
    header: AstHeader,
    kind: CapKind,
}

#[derive(Debug)]
pub enum CapKind {
    CapRef(Ident),
    And(R<Cap>, R<Cap>),
    Or(R<Cap>, R<Cap>),
}

node_impls!(Cap, CapKind);

#[macro_use]
#[cfg(test)]
pub(crate) mod test_utils {
    /// Macro that turns an s-exp DSL into AstNodes or references (R<>) to the same. The caller must
    /// provide the type somehow, as this macro leaves it up to `Into` to wrap up an `AstNode::Kind`
    /// into either a node or a reference to a node.
    ///
    /// Why? https://en.wikipedia.org/wiki/Greenspun%27s_tenth_rule, and also because it makes it easy
    /// to write tests for phases of the compiler after parsing without invoking the parser itself.
    macro_rules! ast {
    ((let $lhs:ident [$ty:tt] $rhs:tt)) => {{
        use crate::ast;
        ast::StmtKind::VarDecl(
            stringify!($lhs).into(),
            ast!([$ty]),
            ast!($rhs),
        ).into()
    }};
    ($var:ident) => {{
        use crate::ast;
        ast::ExprKind::VarRef(stringify!($var).into()).into()
    }};
    ((block [$($body:tt)*] $expr:tt)) => {{
        use crate::ast;
        ast::ExprKind::Block(vec![$(ast!($body)),*], ast!($expr)).into()
    }};
    ([$ty:ident]) => {{
        use crate::ast;
        // TODO more complex type expressions, distinguish constructors vs variables
        ast::TyKind::TyConstInv(ast::TypeConstructorInvocation::noarg_nocap(
            stringify!($ty).into(),
        )).into()
    }};
    ((invoke $fun:ident $($args:tt)*)) => {{
        use crate::ast;
        ast::ExprKind::Invoke(stringify!($fun).into(), vec![$(ast!($args)),*], vec![]).into()
    }};
}
}

#[cfg(test)]
mod tests {
    use crate::ast::*;

    #[test]
    fn test_macro() {
        let node: R<Expr> = ast! {
            (block
                [(let a [Foo] b)
                 (let c [Bar] d)]
                (invoke foo a c))
        };
        println!("{:#?}", node);
    }
}
