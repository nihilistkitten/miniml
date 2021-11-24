//! Parse an ast from a str.
use pest::prec_climber::{Assoc, Operator, PrecClimber};
use pest_consume::{match_nodes, Error, Parser};

use crate::ast::Value::{Bool, Fn, Lookup, Num, Str, Unit};
use crate::ast::{
    ArithOp::{Div, Expt, Minus, Mod, Plus, Times},
    Binop::{Appl, Arith, Logic, Order},
    Expn,
};
use crate::ast::{
    Let::{Fun, Val},
    LogicOp::{And, Or},
    OrderOp::{Eq, Geq, Gt, Leq, Lt},
    Unop::{Neg, Not},
};
use Expn::{Binop, If, Let, Pair, Unop, Value};

#[derive(Parser)]
#[grammar = "miniml.pest"]
pub struct MiniMlParser;

/// Generate a left-associative set of operators with equal precedence.
macro_rules! left_assoc { ($($rule:ident),*) => {
    $(
    Operator::new(Rule::$rule, Assoc::Left)
    )|*
}}

lazy_static::lazy_static! {
    static ref CLIMBER: PrecClimber<Rule> = PrecClimber::new(
        vec![
            left_assoc!(or),
            left_assoc!(and),
            left_assoc!(eq, lt, gt, leq, geq),
            left_assoc!(plus, minus),
            left_assoc!(times, div, modulus),
            Operator::new(Rule::expt, Assoc::Right),
            left_assoc!(appl)
        ]
    );
}

/// A Result alias for Pest parsing errors.
pub type ParserResult<T> = std::result::Result<T, Error<Rule>>;

type Node<'a> = pest_consume::Node<'a, Rule, ()>;

#[pest_consume::parser]
impl MiniMlParser {
    /// Parse an EOI.
    fn EOI(input: Node) -> ParserResult<()> {
        Ok(())
    }

    /// Parse an ident to a `String`.
    fn ident(input: Node) -> ParserResult<&str> {
        Ok(input.as_str())
    }

    /// Parse to a unit.
    fn unit(input: Node) -> ParserResult<()> {
        Ok(())
    }

    /// Parse to an num.
    fn num(input: Node) -> ParserResult<usize> {
        Ok(input.as_str().trim().parse().unwrap())
    }

    fn t(input: Node) -> ParserResult<()> {
        Ok(())
    }

    fn f(input: Node) -> ParserResult<()> {
        Ok(())
    }

    /// Parse to a bool.
    fn bool(input: Node) -> ParserResult<bool> {
        Ok(match_nodes!(input.into_children();
            [t(_)] => true,
            [f(_)] => false,
        ))
    }

    /// Parse to a str.
    fn str(input: Node) -> ParserResult<&str> {
        Ok(input.as_str())
    }

    /// Parse to a lookup.
    fn lookup(input: Node) -> ParserResult<crate::ast::Value> {
        Ok(match_nodes!(input.into_children();
            [ident(x)] => Lookup(x)
        ))
    }

    /// Parse to an arrow.
    fn arrow(input: Node) -> ParserResult<crate::ast::Value> {
        Ok(match_nodes!(input.into_children();
            [ident(x), expn(r)] => Fn(x, box r)
        ))
    }

    /// Parse to a value.
    ///
    /// value = { unit | int | bool | str | lookup | arrow }
    fn value(input: Node) -> ParserResult<Expn> {
        Ok(match_nodes!(input.into_children();
            [unit(_)] => Value(Unit),
            [num(n)] => n.into(),
            [bool(b)] => b.into(),
            [str(s)] => s.into(),
            [lookup(x)] => x.into(),
            [arrow(f)] => f.into(),
        ))
    }

    /// Parse to a cond.
    ///
    /// cond = { "if" ~ expn ~ "then" ~ expn ~ "else" ~ expn ~ "end" }
    fn cond(input: Node) -> ParserResult<Expn> {
        Ok(match_nodes!(input.into_children();
            [expn(cond), expn(then_exp), expn(else_exp)] => If{ cond: box cond, then_exp: box then_exp, else_exp: box else_exp }
        ))
    }

    /// Parse a fun.
    fn fun(input: Node) -> ParserResult<()> {
        Ok(())
    }

    /// Parse a val.
    fn val(input: Node) -> ParserResult<()> {
        Ok(())
    }

    /// Parse to a bind.
    ///
    /// bind = { "let" ~ (fun | val) ~ ident ~ "=" ~ expn ~ "in" ~ expn ~ "end" }
    fn bind(input: Node) -> ParserResult<Expn> {
        Ok(match_nodes!(input.into_children();
            [fun(_), ident(ident), expn(defn), expn(body)] => Let{ kind: Fun, ident, defn: box defn, body: box body },
            [val(_), ident(ident), expn(defn), expn(body)] => Let{ kind: Val, ident, defn: box defn, body: box body },
        ))
    }

    /// Parse to a binop.
    #[prec_climb(atom, CLIMBER)]
    #[allow(
        unused_variables,
        dead_code,
        clippy::needless_pass_by_value,
        clippy::unnecessary_wraps
    )] // these lints get confused by the macro
    fn binop<'a>(left: Expn<'a>, op: Node<'a>, right: Expn<'a>) -> ParserResult<Expn<'a>> {
        let op_ast = match op.as_rule() {
            Rule::or => Logic(Or),
            Rule::and => Logic(And),
            Rule::eq => Order(Eq),
            Rule::lt => Order(Lt),
            Rule::gt => Order(Gt),
            Rule::leq => Order(Leq),
            Rule::geq => Order(Geq),
            Rule::plus => Arith(Plus),
            Rule::minus => Arith(Minus),
            Rule::times => Arith(Times),
            Rule::div => Arith(Div),
            Rule::modulus => Arith(Mod),
            Rule::expt => Arith(Expt),
            Rule::appl => Appl,
            r => return Err(op.error(format!("Rule {:?} isn't an operator", r))),
        };
        Ok(Binop {
            left: box left,
            op: op_ast,
            right: box right,
        })
    }

    /// Parse a not.
    fn not(input: Node) -> ParserResult<()> {
        Ok(())
    }

    /// Parse a neg.
    fn neg(input: Node) -> ParserResult<()> {
        Ok(())
    }

    /// Parse to a unop.
    fn unop(input: Node) -> ParserResult<Expn> {
        Ok(match_nodes!(input.into_children();
            [not(_), unop(on)] => Unop{op: Not, on: box on},
            [neg(_), unop(on)] => Unop{op: Neg, on: box on},
            [not(_), atom(on)] => Unop{op: Not, on: box on},
            [neg(_), atom(on)] => Unop{op: Neg, on: box on}
        ))
    }

    /// Parse to an atom.
    ///
    /// atom = { pair | paren | value }
    fn atom(input: Node) -> ParserResult<Expn> {
        Ok(match_nodes!(input.into_children();
            [pair(p)] => p,
            [paren(p)] => p,
            [value(v)] => v,
        ))
    }

    /// Parse to a pair.
    ///
    /// pair = { "(" ~ expn ~ "," ~ expn ~ ")" }
    fn pair(input: Node) -> ParserResult<Expn> {
        Ok(match_nodes!(input.into_children();
            [expn(left), expn(right)] => Pair(box left, box right)
        ))
    }

    /// Parse to a paren.
    ///
    /// paren = { "(" ~ expn ~ ")" }
    fn paren(input: Node) -> ParserResult<Expn> {
        Ok(match_nodes!(input.into_children();
            [expn(inner)] => inner
        ))
    }
    /// Parse to an expn.
    ///
    /// expn = { cond ~ bind ~ binop ~ unop ~ atom }
    fn expn(input: Node) -> ParserResult<Expn> {
        Ok(match_nodes!(input.into_children();
            [cond(c)] => c,
            [bind(b)] => b,
            [binop(b)] => b,
            [unop(u)] => u,
            [atom(a)] => a,
        ))
    }

    /// Parse a file to a `Expn`.
    fn file(input: Node) -> ParserResult<Expn> {
        Ok(match_nodes!(input.into_children();
            [expn(e), EOI(_)] => e
        ))
    }
}

/// Parse a &str to an expn.
pub fn to_expn(s: &str) -> ParserResult<Expn> {
    MiniMlParser::file(MiniMlParser::parse(Rule::file, s)?.single()?)
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! parser_tests { ($($name:ident: $input:expr, $expected:expr)*) => {
        $(
            #[test]
            fn $name() -> ParserResult<()> {
                assert_eq!(to_expn($input)?, $expected);
                Ok(())
            }
        )*
    }}

    parser_tests!(
        num: "3", Value(Num(3))
        simple_fn: "fn x => 5", Value(Fn("x", box 5.into()))
        appl: "(fn y => x) 3", Binop{
            left: box Value(Fn("y", box Value(Lookup("x")))), op: Appl, right: box 3.into()
        }
        precedence: "3 + 4 * 5", Binop{
            left: box 3.into(), op: Plus.into(), right: box Binop{
                left: box 4.into(), op: Times.into(), right: box 5.into()
            }
        }
        assoc: "3 * 4 * 5", Binop{
            left: box Binop {
                left: box 3.into(),
                op: Times.into(),
                right: box 4.into()
            },
            op: Times.into(),
            right: box 5.into(),
        }
    );
}
