//! The typed ast.

trait MlOp {
    fn display(&self) -> &'static str;
}

/// A binary arithmetic operator.
#[derive(Debug, PartialEq)]
pub enum ArithOp {
    Plus,
    Minus,
    Times,
    Div,
    Mod,
    Expt,
}

impl From<ArithOp> for Binop {
    fn from(o: ArithOp) -> Self {
        Self::Arith(o)
    }
}

impl MlOp for ArithOp {
    fn display(&self) -> &'static str {
        match self {
            Self::Plus => "+",
            Self::Minus => "-",
            Self::Times => "*",
            Self::Div => "/",
            Self::Mod => "%",
            Self::Expt => "**",
        }
    }
}

/// A logic operator.
#[derive(Debug, PartialEq)]
pub enum LogicOp {
    And,
    Or,
}

impl From<LogicOp> for Binop {
    fn from(o: LogicOp) -> Self {
        Self::Logic(o)
    }
}

impl MlOp for LogicOp {
    fn display(&self) -> &'static str {
        match self {
            Self::And => "andalso",
            Self::Or => "orelse",
        }
    }
}

/// A comparison operator.
#[derive(Debug, PartialEq)]
pub enum OrderOp {
    Lt,
    Gt,
    Leq,
    Geq,
    Eq,
}

impl From<OrderOp> for Binop {
    fn from(o: OrderOp) -> Self {
        Self::Order(o)
    }
}

impl MlOp for OrderOp {
    fn display(&self) -> &'static str {
        match self {
            Self::Lt => "<",
            Self::Gt => ">",
            Self::Leq => "<=",
            Self::Geq => ">=",
            Self::Eq => "==",
        }
    }
}

/// A binary operator.
#[derive(Debug, PartialEq)]
pub enum Binop {
    Arith(ArithOp),
    Logic(LogicOp),
    Order(OrderOp),
    Appl,
}

impl MlOp for Binop {
    fn display(&self) -> &'static str {
        match self {
            Self::Arith(o) => o.display(),
            Self::Logic(o) => o.display(),
            Self::Order(o) => o.display(),
            Self::Appl => "",
        }
    }
}

/// A unary operator.
#[derive(Debug, PartialEq)]
pub enum Unop {
    /// Arithmetic negation.
    Neg,

    /// Logical negation.
    Not,
}

impl MlOp for Unop {
    fn display(&self) -> &'static str {
        match self {
            Self::Neg => "~",
            Self::Not => "!",
        }
    }
}

/// A macro to implement `Display` for `MlOp`. Can't be implemented generically because of orphan
/// rules.
macro_rules! display_op { ($($type:ident),*)  => {
    $(
        impl std::fmt::Display for $type {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}", self.display())
            }
        }
    )*
}}

display_op!(ArithOp, LogicOp, OrderOp, Binop, Unop);

/// A literal value.
#[derive(Debug, PartialEq)]
pub enum Value<'a> {
    Unit,
    Num(usize),
    Bool(bool),
    Str(&'a str),
    Lookup(&'a str),
    Fn(&'a str, Box<Expn<'a>>),
}

impl<'a> From<Value<'a>> for Expn<'a> {
    fn from(v: Value<'a>) -> Self {
        Self::Value(v)
    }
}

macro_rules! into_value { ($($variant:ident, $type:ty)*) => {
    $(
        impl<'a> From<$type> for Value<'a> {
            fn from(val: $type) -> Self {
                Self::$variant(val)
            }
        }

        impl<'a> From<$type> for Expn<'a> {
            fn from(val: $type) -> Self {
                Into::<Value<'a>>::into(val).into()
            }
        }
    )*
}}

into_value! {
    Num, usize
    Bool, bool
    Str, &'a str
}

impl std::fmt::Display for Value<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unit => write!(f, "()"),
            Self::Num(i) => write!(f, "{}", i),
            Self::Bool(b) => write!(f, "{}", b),
            Self::Str(s) => write!(f, "{}", s),
            Self::Lookup(x) => write!(f, "{}", x),
            Self::Fn(x, r) => write!(f, "fn {x} => {r}", x = x, r = r),
        }
    }
}

/// The kinds of `let` expressions.
#[derive(Debug, PartialEq)]
pub enum Let {
    Fun,
    Val,
}

impl std::fmt::Display for Let {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let message = match self {
            Self::Fun => "fun",
            Self::Val => "val",
        };
        write!(f, "{}", message)
    }
}

/// A miniml expression.
#[derive(Debug, PartialEq)]
pub enum Expn<'a> {
    If {
        cond: Box<Expn<'a>>,
        then_exp: Box<Expn<'a>>,
        else_exp: Box<Expn<'a>>,
    },
    Let {
        kind: Let,
        ident: &'a str,
        defn: Box<Expn<'a>>,
        body: Box<Expn<'a>>,
    },
    Binop {
        op: Binop,
        left: Box<Expn<'a>>,
        right: Box<Expn<'a>>,
    },
    Unop {
        op: Unop,
        on: Box<Expn<'a>>,
    },
    Value(Value<'a>),
    Pair(Box<Expn<'a>>, Box<Expn<'a>>),
}

impl std::fmt::Display for Expn<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let message = match self {
            Self::If {
                cond,
                then_exp,
                else_exp,
            } => format!(
                "if {cond} then {then_exp} else {else_exp} end",
                cond = cond,
                then_exp = then_exp,
                else_exp = else_exp
            ),
            Self::Let {
                kind,
                ident,
                defn,
                body,
            } => format!(
                "let {kind} {ident} = {defn} in {body} end",
                kind = kind,
                ident = ident,
                defn = defn,
                body = body
            ),
            Self::Binop { op, left, right } => {
                format!("{left} {op} {right}", left = left, op = op, right = right)
            }
            Self::Unop { op, on } => format!("{op}{on}", op = op, on = on),
            Self::Value(v) => format!("{}", v),
            Self::Pair(left, right) => format!("({left}, {right})", left = left, right = right),
        };
        write!(f, "{}", message)
    }
}
