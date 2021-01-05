use crate::type_check::Name;
use bumpalo::core_alloc::fmt::Formatter;
use std::fmt;
use std::fmt::Display;
use std::ops::Deref;

/// An owned pointer to an AstNode
#[derive(Debug)]
pub struct AstRef {
    ptr: Box<AstNode>,
}

impl AstRef {
    fn new(node: AstNode) -> Self {
        AstRef {
            ptr: Box::new(node),
        }
    }
}

impl Deref for AstRef {
    type Target = AstNode;

    fn deref(&self) -> &Self::Target {
        &self.ptr
    }
}

/// A node in the AST.
///
/// Generally, the interesting parts of an AstNode are stored in the AstNodeKind. That's where we distinguish
/// between the different types of nodes and store the various references to children etc.
///
/// This wrapper allows us to generalize over any AstNode, as well as track metadata on the node in a
/// header. This header contains things like the span the node represents, as well as any data that's
/// been populated about the node through the various passes - for example, the type checker tags the
/// node with its resolved type (if it's an expression), etc. That allows accumulating
#[derive(Debug)]
pub struct AstNode {
    pub header: AstNodeHeader,
    pub kind: AstNodeKind,
}

impl AstNode {
    fn new(kind: AstNodeKind) -> Self {
        AstNode {
            header: AstNodeHeader {},
            kind,
        }
    }
}

impl Display for AstNode {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.kind.fmt(f)
    }
}

impl Into<AstRef> for AstNode {
    fn into(self) -> AstRef {
        AstRef::new(self)
    }
}

/// Contains shared stuff every AstNode tracks. Span, type, resolved fqn, etc.
#[derive(Debug)]
pub struct AstNodeHeader {
    // TODO span, nodeid, type, etc
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
pub enum AstNodeKind {
    /// Identifiers. `Foo`, `bar`, etc
    Ident(Ident),
    /// Variable reference. `foo`, `bar`, etc
    VarRef(Ident),
    /// Variable definitions. `let lval: type = rval`
    VarDecl(Ident, TypeExpr, AstRef),
    /// Expressions valid on the left hand side of an assignment. `a`, `foo.a`, `foo[i]`, etc.
    LVal(LVal),
    /// Blocks of statements
    /// {
    ///     // ...
    /// }
    Block(Vec<AstRef>),
    /// function invocation. `foo()`, `foo<A>(a, b)`, etc
    Invoke(Ident, Vec<AstRef>),
    /// Type expressions. `Int`, `Foo<A>[C]`, etc
    TypeExpr(TypeExpr),
}

impl AstNodeKind {
    fn into_ast_ref(self) -> AstRef {
        self.into()
    }
}

impl Into<AstNode> for AstNodeKind {
    fn into(self) -> AstNode {
        AstNode::new(self)
    }
}

impl Into<AstRef> for AstNodeKind {
    fn into(self) -> AstRef {
        let node: AstNode = self.into();
        node.into()
    }
}

impl Display for AstNodeKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // TODO display AST nodes
        write!(f, "node")
    }
}

#[derive(Debug)]
pub enum LVal {
    Variable(Ident),
}

/// The AST's view of a type. Can't perform type analysis using it, but can be converted to type_constructors::Ty with a TypeContext
#[derive(Debug)]
pub enum TypeExpr {
    Variable(Ident),
    TyConstInv(TypeConstructorInvocation),
}

#[derive(Debug)]
pub struct TypeConstructorInvocation {
    pub constructor: Ident,
    pub actual_type_parameters: Vec<AstRef>,
    pub capabilities: Vec<AstRef>,
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

#[derive(Debug)]
pub struct FunctionImplementation {
    pub body: AstRef,
}

/// Macro that turns an s-exp DSL to AstNodes.
/// Why? https://en.wikipedia.org/wiki/Greenspun%27s_tenth_rule
macro_rules! ast {
    ((let $lhs:ident [$ty:tt] $rhs:tt)) => {
        AstNodeKind::VarDecl(
            stringify!($lhs).into(),
            ast!([$ty]),
            ast!($rhs),
        ).into_ast_ref()
    };
    ($var:ident) => {
        AstNodeKind::VarRef(stringify!($var).into()).into_ast_ref()
    };
    ((block $($body:tt)*)) => {
        AstNodeKind::Block(vec![$(ast!($body)),*]).into_ast_ref()
    };
    ([$ty:ident]) => {
        // TODO more complex type expressions, distinguish constructors vs variables
        TypeExpr::TyConstInv(TypeConstructorInvocation::noarg_nocap(
            stringify!($ty).into(),
        ))
    };
    ((invoke $fun:ident $($args:tt)*)) => {
        AstNodeKind::Invoke(stringify!($fun).into(), vec![$(ast!($args)),*]).into_ast_ref()
    };
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_macro() {
        use crate::ast::*;
        let node = ast! {
            (block
                (let a [Foo] b)
                (let c [Bar] d)
                (invoke foo a c))
        };
        println!("{:#?}", node);
    }
}
