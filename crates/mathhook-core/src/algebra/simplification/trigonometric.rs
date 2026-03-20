//! Trigonometric Function Simplification Strategies
//!
//! Implements algebraic rewrite rules for trigonometric functions (sin, cos, tan, etc.).

use super::strategy::SimplificationStrategy;
use crate::core::{Expression, Number};
use crate::simplify::Simplify;
use num_bigint::BigInt;
use num_traits::Signed;

fn is_negative_number(num: &Number) -> bool {
    match num {
        Number::Integer(value) => *value < 0,
        Number::Float(value) => *value < 0.0,
        Number::BigInteger(value) => value.is_negative(),
        Number::Rational(value) => value.is_negative(),
    }
}

fn abs_number(num: &Number) -> Number {
    match num {
        Number::Integer(value) => value
            .checked_abs()
            .map(Number::Integer)
            .unwrap_or_else(|| Number::BigInteger(Box::new(BigInt::from(*value).abs()))),
        Number::Float(value) => Number::Float(value.abs()),
        Number::BigInteger(value) => Number::BigInteger(Box::new(value.abs())),
        Number::Rational(value) => Number::Rational(Box::new(value.abs())),
    }
}

fn extract_negative_argument(arg: &Expression) -> Option<Expression> {
    match arg {
        Expression::Number(num) if is_negative_number(num) => {
            Some(Expression::Number(abs_number(num)))
        }
        Expression::Mul(factors)
            if matches!(factors.first(), Some(Expression::Number(num)) if is_negative_number(num)) =>
        {
            let mut positive_factors = factors.to_vec();
            if let Expression::Number(num) = &factors[0] {
                positive_factors[0] = Expression::Number(abs_number(num));
            }
            Some(Expression::mul(positive_factors).simplify())
        }
        _ => None,
    }
}

/// Sine function simplification strategy
pub struct SinSimplificationStrategy;

impl SimplificationStrategy for SinSimplificationStrategy {
    fn simplify(&self, args: &[Expression]) -> Expression {
        if args.len() == 1 {
            let arg = &args[0];

            if arg.is_zero() {
                Expression::integer(0)
            } else if let Some(positive_arg) = extract_negative_argument(arg) {
                Expression::mul(vec![
                    Expression::integer(-1),
                    Expression::function("sin", vec![positive_arg]),
                ])
                .simplify()
            } else if let Expression::Function {
                name: inner_name,
                args: inner_args,
            } = arg
            {
                if inner_name.as_ref() == "asin" && inner_args.len() == 1 {
                    inner_args[0].clone()
                } else {
                    Expression::function("sin", args.to_vec())
                }
            } else {
                Expression::function("sin", args.to_vec())
            }
        } else {
            Expression::function("sin", args.to_vec())
        }
    }

    fn applies_to(&self, args: &[Expression]) -> bool {
        args.len() == 1
    }

    fn name(&self) -> &str {
        "SinSimplificationStrategy"
    }
}

/// Cosine function simplification strategy
pub struct CosSimplificationStrategy;

impl SimplificationStrategy for CosSimplificationStrategy {
    fn simplify(&self, args: &[Expression]) -> Expression {
        if args.len() == 1 {
            let arg = &args[0];

            if arg.is_zero() {
                Expression::integer(1)
            } else if let Some(positive_arg) = extract_negative_argument(arg) {
                Expression::function("cos", vec![positive_arg]).simplify()
            } else if let Expression::Function {
                name: inner_name,
                args: inner_args,
            } = arg
            {
                if inner_name.as_ref() == "acos" && inner_args.len() == 1 {
                    inner_args[0].clone()
                } else {
                    Expression::function("cos", args.to_vec())
                }
            } else {
                Expression::function("cos", args.to_vec())
            }
        } else {
            Expression::function("cos", args.to_vec())
        }
    }

    fn applies_to(&self, args: &[Expression]) -> bool {
        args.len() == 1
    }

    fn name(&self) -> &str {
        "CosSimplificationStrategy"
    }
}

/// Tangent function simplification strategy
pub struct TanSimplificationStrategy;

impl SimplificationStrategy for TanSimplificationStrategy {
    fn simplify(&self, args: &[Expression]) -> Expression {
        if args.len() == 1 {
            let arg = &args[0];

            if arg.is_zero() {
                Expression::integer(0)
            } else if let Some(positive_arg) = extract_negative_argument(arg) {
                Expression::mul(vec![
                    Expression::integer(-1),
                    Expression::function("tan", vec![positive_arg]),
                ])
                .simplify()
            } else if let Expression::Function {
                name: inner_name,
                args: inner_args,
            } = arg
            {
                if inner_name.as_ref() == "atan" && inner_args.len() == 1 {
                    inner_args[0].clone()
                } else {
                    Expression::function("tan", args.to_vec())
                }
            } else {
                Expression::function("tan", args.to_vec())
            }
        } else {
            Expression::function("tan", args.to_vec())
        }
    }

    fn applies_to(&self, args: &[Expression]) -> bool {
        args.len() == 1
    }

    fn name(&self) -> &str {
        "TanSimplificationStrategy"
    }
}

/// Generic trigonometric simplification strategy
///
/// Handles csc, sec, cot, asin, acos, atan, sinh, cosh, tanh
pub struct GenericTrigSimplificationStrategy {
    function_name: String,
}

impl GenericTrigSimplificationStrategy {
    pub fn new(function_name: &str) -> Self {
        Self {
            function_name: function_name.to_owned(),
        }
    }
}

impl SimplificationStrategy for GenericTrigSimplificationStrategy {
    fn simplify(&self, args: &[Expression]) -> Expression {
        Expression::function(&self.function_name, args.to_vec())
    }

    fn applies_to(&self, args: &[Expression]) -> bool {
        args.len() == 1
    }

    fn name(&self) -> &str {
        &self.function_name
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{expr, symbol};

    #[test]
    fn test_sin_of_zero() {
        let strategy = SinSimplificationStrategy;
        let result = strategy.simplify(&[expr!(0)]);
        assert_eq!(result, expr!(0));
    }

    #[test]
    fn test_sin_of_x() {
        let strategy = SinSimplificationStrategy;
        let x = symbol!(x);
        let result = strategy.simplify(&[x.clone().into()]);

        if let Expression::Function { name, args } = result {
            assert_eq!(name.as_ref(), "sin");
            assert_eq!(args.len(), 1);
            assert_eq!(args[0], x.into());
        } else {
            panic!("Expected function call");
        }
    }

    #[test]
    fn test_cos_of_zero() {
        let strategy = CosSimplificationStrategy;
        let result = strategy.simplify(&[expr!(0)]);
        assert_eq!(result, expr!(1));
    }

    #[test]
    fn test_cos_of_x() {
        let strategy = CosSimplificationStrategy;
        let x = symbol!(x);
        let result = strategy.simplify(&[x.clone().into()]);

        if let Expression::Function { name, args } = result {
            assert_eq!(name.as_ref(), "cos");
            assert_eq!(args.len(), 1);
            assert_eq!(args[0], x.into());
        } else {
            panic!("Expected function call");
        }
    }

    #[test]
    fn test_tan_of_zero() {
        let strategy = TanSimplificationStrategy;
        let result = strategy.simplify(&[expr!(0)]);
        assert_eq!(result, expr!(0));
    }

    #[test]
    fn test_tan_of_x() {
        let strategy = TanSimplificationStrategy;
        let x = symbol!(x);
        let result = strategy.simplify(&[x.clone().into()]);

        if let Expression::Function { name, args } = result {
            assert_eq!(name.as_ref(), "tan");
            assert_eq!(args.len(), 1);
            assert_eq!(args[0], x.into());
        } else {
            panic!("Expected function call");
        }
    }

    #[test]
    fn test_generic_trig() {
        let strategy = GenericTrigSimplificationStrategy::new("sinh");
        let x = symbol!(x);
        let result = strategy.simplify(&[x.clone().into()]);

        if let Expression::Function { name, args } = result {
            assert_eq!(name.as_ref(), "sinh");
            assert_eq!(args.len(), 1);
            assert_eq!(args[0], x.into());
        } else {
            panic!("Expected function call");
        }
    }

    #[test]
    fn test_sin_negative_argument() {
        let strategy = SinSimplificationStrategy;
        let x = symbol!(x);
        let result = strategy.simplify(&[Expression::mul(vec![
            Expression::integer(-1),
            Expression::symbol(x.clone()),
        ])]);

        assert_eq!(result, expr!(-(sin(x))));
    }

    #[test]
    fn test_cos_negative_argument() {
        let strategy = CosSimplificationStrategy;
        let x = symbol!(x);
        let result = strategy.simplify(&[Expression::mul(vec![
            Expression::integer(-1),
            Expression::symbol(x.clone()),
        ])]);

        assert_eq!(result, expr!(cos(x)));
    }

    #[test]
    fn test_tan_negative_argument() {
        let strategy = TanSimplificationStrategy;
        let x = symbol!(x);
        let result = strategy.simplify(&[Expression::mul(vec![
            Expression::integer(-1),
            Expression::symbol(x.clone()),
        ])]);

        assert_eq!(result, expr!(-(tan(x))));
    }

    #[test]
    fn test_sin_asin_inverse() {
        let strategy = SinSimplificationStrategy;
        let x = symbol!(x);
        let result = strategy.simplify(&[Expression::function(
            "asin",
            vec![Expression::symbol(x.clone())],
        )]);

        assert_eq!(result, expr!(x));
    }

    #[test]
    fn test_cos_acos_inverse() {
        let strategy = CosSimplificationStrategy;
        let x = symbol!(x);
        let result = strategy.simplify(&[Expression::function(
            "acos",
            vec![Expression::symbol(x.clone())],
        )]);

        assert_eq!(result, expr!(x));
    }

    #[test]
    fn test_tan_atan_inverse() {
        let strategy = TanSimplificationStrategy;
        let x = symbol!(x);
        let result = strategy.simplify(&[Expression::function(
            "atan",
            vec![Expression::symbol(x.clone())],
        )]);

        assert_eq!(result, expr!(x));
    }
}
