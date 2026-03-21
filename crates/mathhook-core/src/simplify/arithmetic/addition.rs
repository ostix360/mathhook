//! Addition simplification operations

use super::helpers::{expression_order, extract_arithmetic_coefficient_and_base};
use super::multiplication::simplify_multiplication;
use super::power::simplify_power;
use super::Simplify;
use crate::core::commutativity::Commutativity;
use crate::core::constants::EPSILON;
use crate::core::{Expression, Number};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{ToPrimitive, Zero};
use std::collections::VecDeque;
use std::sync::Arc;

fn extract_trig_squared(expr: &Expression, func: &str) -> Option<Expression> {
    if let Expression::Pow(base, exp) = expr {
        if let Expression::Number(Number::Integer(2)) = exp.as_ref() {
            if let Expression::Function { name, args } = base.as_ref() {
                if name.as_ref() == func && args.len() == 1 {
                    return Some(args[0].clone());
                }
            }
        }
    }
    None
}

fn extract_scaled_trig_squared(expr: &Expression, func: &str) -> Option<(Expression, Expression)> {
    if let Some(arg) = extract_trig_squared(expr, func) {
        return Some((Expression::integer(1), arg));
    }

    if let Expression::Mul(factors) = expr {
        for (index, factor) in factors.iter().enumerate() {
            if let Some(arg) = extract_trig_squared(factor, func) {
                let coeff_factors: Vec<_> = factors
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| *i != index)
                    .map(|(_, factor)| factor.clone())
                    .collect();

                let coeff = match coeff_factors.len() {
                    0 => Expression::integer(1),
                    1 => coeff_factors[0].clone(),
                    _ => simplify_multiplication(&coeff_factors),
                };

                return Some((coeff, arg));
            }
        }
    }

    None
}

fn trig_squared(func: &str, arg: Expression) -> Expression {
    Expression::pow(
        Expression::function(func, vec![arg]),
        Expression::integer(2),
    )
}

fn build_scaled_term(coeff: Expression, base: Expression) -> Expression {
    match coeff {
        Expression::Number(ref num) if num.is_one() => base,
        _ => simplify_multiplication(&[coeff, base]),
    }
}

fn expressions_match(lhs: &Expression, rhs: &Expression) -> bool {
    lhs.simplify() == rhs.simplify()
}

fn negate_expression(expr: &Expression) -> Expression {
    simplify_multiplication(&[Expression::integer(-1), expr.clone()])
}

fn expressions_are_negations(lhs: &Expression, rhs: &Expression) -> bool {
    expressions_match(lhs, &negate_expression(rhs))
}

fn build_expression_from_factors(factors: Vec<Expression>) -> Expression {
    match factors.len() {
        0 => Expression::integer(1),
        1 => factors.into_iter().next().unwrap(),
        _ => simplify_multiplication(&factors),
    }
}

fn extract_commutative_factors(expr: &Expression) -> Option<Vec<Expression>> {
    if !expr.commutativity().can_sort() {
        return None;
    }

    match expr {
        Expression::Mul(factors) => Some(factors.iter().cloned().collect()),
        _ => Some(vec![expr.clone()]),
    }
}

fn extract_common_commutative_factors(
    lhs: &Expression,
    rhs: &Expression,
) -> Option<(Vec<Expression>, Expression, Expression)> {
    let mut lhs_factors = extract_commutative_factors(lhs)?;
    let rhs_factors = extract_commutative_factors(rhs)?;
    let mut common_factors = Vec::new();
    let mut rhs_used = vec![false; rhs_factors.len()];

    for lhs_factor in &lhs_factors {
        if let Some((index, _)) = rhs_factors
            .iter()
            .enumerate()
            .find(|(index, rhs_factor)| !rhs_used[*index] && *rhs_factor == lhs_factor)
        {
            rhs_used[index] = true;
            common_factors.push(lhs_factor.clone());
        }
    }

    if common_factors.is_empty() {
        return None;
    }

    for common_factor in &common_factors {
        if let Some(index) = lhs_factors
            .iter()
            .position(|factor| factor == common_factor)
        {
            lhs_factors.remove(index);
        }
    }

    let rhs_remaining: Vec<_> = rhs_factors
        .into_iter()
        .enumerate()
        .filter(|(index, _)| !rhs_used[*index])
        .map(|(_, factor)| factor)
        .collect();

    Some((
        common_factors,
        build_expression_from_factors(lhs_factors),
        build_expression_from_factors(rhs_remaining),
    ))
}

fn gcd_i64(mut lhs: i64, mut rhs: i64) -> i64 {
    lhs = lhs.abs();
    rhs = rhs.abs();

    while rhs != 0 {
        let remainder = lhs % rhs;
        lhs = rhs;
        rhs = remainder;
    }

    lhs
}

fn extract_factorable_term(expr: &Expression) -> Option<(i64, Vec<Expression>)> {
    if !expr.commutativity().can_sort() {
        return None;
    }

    match expr {
        Expression::Number(Number::Integer(value)) => Some((*value, Vec::new())),
        Expression::Mul(factors)
            if matches!(
                factors.first(),
                Some(Expression::Number(Number::Integer(_)))
            ) =>
        {
            let coeff = match &factors[0] {
                Expression::Number(Number::Integer(value)) => *value,
                _ => unreachable!(),
            };
            Some((coeff, factors[1..].to_vec()))
        }
        Expression::Mul(factors) => Some((1, factors.iter().cloned().collect())),
        _ => Some((1, vec![expr.clone()])),
    }
}

fn intersect_factor_lists(lhs: &[Expression], rhs: &[Expression]) -> Vec<Expression> {
    let mut rhs_used = vec![false; rhs.len()];
    let mut intersection = Vec::new();

    for lhs_factor in lhs {
        if let Some((index, _)) = rhs
            .iter()
            .enumerate()
            .find(|(index, rhs_factor)| !rhs_used[*index] && *rhs_factor == lhs_factor)
        {
            rhs_used[index] = true;
            intersection.push(lhs_factor.clone());
        }
    }

    intersection
}

fn remove_factor_list(mut factors: Vec<Expression>, to_remove: &[Expression]) -> Vec<Expression> {
    for factor in to_remove {
        if let Some(index) = factors.iter().position(|candidate| candidate == factor) {
            factors.remove(index);
        }
    }

    factors
}

fn try_factor_common_terms(terms: &[Expression]) -> Option<Expression> {
    if terms.len() < 2 {
        return None;
    }

    let decomposed_terms: Vec<_> = terms
        .iter()
        .map(extract_factorable_term)
        .collect::<Option<_>>()?;

    let mut common_symbolic_factors = decomposed_terms[0].1.clone();
    for (_, factors) in decomposed_terms.iter().skip(1) {
        common_symbolic_factors = intersect_factor_lists(&common_symbolic_factors, factors);
        if common_symbolic_factors.is_empty() {
            break;
        }
    }

    let numeric_gcd = decomposed_terms
        .iter()
        .map(|(coeff, _)| *coeff)
        .reduce(gcd_i64)
        .unwrap_or(1);
    let has_numeric_common = numeric_gcd > 1;

    if !has_numeric_common && common_symbolic_factors.is_empty() {
        return None;
    }

    let mut common_factor_parts = Vec::new();
    if has_numeric_common {
        common_factor_parts.push(Expression::integer(numeric_gcd));
    }
    common_factor_parts.extend(common_symbolic_factors.iter().cloned());

    let common_factor = build_expression_from_factors(common_factor_parts);
    let remainder_terms: Vec<_> = decomposed_terms
        .into_iter()
        .map(|(coeff, factors)| {
            let reduced_coeff = if has_numeric_common {
                coeff / numeric_gcd
            } else {
                coeff
            };
            let remaining_factors = remove_factor_list(factors, &common_symbolic_factors);

            let mut rebuilt_parts = Vec::new();
            if reduced_coeff != 1 || remaining_factors.is_empty() {
                rebuilt_parts.push(Expression::integer(reduced_coeff));
            }
            rebuilt_parts.extend(remaining_factors);

            build_expression_from_factors(rebuilt_parts)
        })
        .collect();

    let reduced_sum = simplify_addition_with_options(&remainder_terms, true);
    Some(simplify_multiplication(&[common_factor, reduced_sum]))
}

fn try_direct_trig_identity_pair(lhs: &Expression, rhs: &Expression) -> Option<Expression> {
    if let (Some((sin_coeff, sin_arg)), Some((cos_coeff, cos_arg))) = (
        extract_scaled_trig_squared(lhs, "sin"),
        extract_scaled_trig_squared(rhs, "cos"),
    ) {
        if sin_arg == cos_arg && expressions_match(&sin_coeff, &cos_coeff) {
            return Some(sin_coeff);
        }
    }

    if let (Some((cos_coeff, cos_arg)), Some((sin_coeff, sin_arg))) = (
        extract_scaled_trig_squared(lhs, "cos"),
        extract_scaled_trig_squared(rhs, "sin"),
    ) {
        if sin_arg == cos_arg && expressions_match(&sin_coeff, &cos_coeff) {
            return Some(cos_coeff);
        }
    }

    if let Some((tan_coeff, tan_arg)) = extract_scaled_trig_squared(lhs, "tan") {
        if expressions_match(&tan_coeff, rhs) {
            return Some(build_scaled_term(tan_coeff, trig_squared("sec", tan_arg)));
        }
    }

    if let Some((tan_coeff, tan_arg)) = extract_scaled_trig_squared(rhs, "tan") {
        if expressions_match(&tan_coeff, lhs) {
            return Some(build_scaled_term(tan_coeff, trig_squared("sec", tan_arg)));
        }
    }

    if let Some((cot_coeff, cot_arg)) = extract_scaled_trig_squared(lhs, "cot") {
        if expressions_match(&cot_coeff, rhs) {
            return Some(build_scaled_term(cot_coeff, trig_squared("csc", cot_arg)));
        }
    }

    if let Some((cot_coeff, cot_arg)) = extract_scaled_trig_squared(rhs, "cot") {
        if expressions_match(&cot_coeff, lhs) {
            return Some(build_scaled_term(cot_coeff, trig_squared("csc", cot_arg)));
        }
    }

    if let (Some((sec_coeff, sec_arg)), Some((tan_coeff, tan_arg))) = (
        extract_scaled_trig_squared(lhs, "sec"),
        extract_scaled_trig_squared(rhs, "tan"),
    ) {
        if sec_arg == tan_arg && expressions_are_negations(&sec_coeff, &tan_coeff) {
            return Some(sec_coeff);
        }
    }

    if let (Some((tan_coeff, tan_arg)), Some((sec_coeff, sec_arg))) = (
        extract_scaled_trig_squared(lhs, "tan"),
        extract_scaled_trig_squared(rhs, "sec"),
    ) {
        if sec_arg == tan_arg && expressions_are_negations(&sec_coeff, &tan_coeff) {
            return Some(sec_coeff);
        }
    }

    if let (Some((csc_coeff, csc_arg)), Some((cot_coeff, cot_arg))) = (
        extract_scaled_trig_squared(lhs, "csc"),
        extract_scaled_trig_squared(rhs, "cot"),
    ) {
        if csc_arg == cot_arg && expressions_are_negations(&csc_coeff, &cot_coeff) {
            return Some(csc_coeff);
        }
    }

    if let (Some((cot_coeff, cot_arg)), Some((csc_coeff, csc_arg))) = (
        extract_scaled_trig_squared(lhs, "cot"),
        extract_scaled_trig_squared(rhs, "csc"),
    ) {
        if csc_arg == cot_arg && expressions_are_negations(&csc_coeff, &cot_coeff) {
            return Some(csc_coeff);
        }
    }

    if let Some((sec_coeff, sec_arg)) = extract_scaled_trig_squared(lhs, "sec") {
        if expressions_are_negations(&sec_coeff, rhs) {
            return Some(build_scaled_term(sec_coeff, trig_squared("tan", sec_arg)));
        }
    }

    if let Some((sec_coeff, sec_arg)) = extract_scaled_trig_squared(rhs, "sec") {
        if expressions_are_negations(&sec_coeff, lhs) {
            return Some(build_scaled_term(sec_coeff, trig_squared("tan", sec_arg)));
        }
    }

    if let Some((csc_coeff, csc_arg)) = extract_scaled_trig_squared(lhs, "csc") {
        if expressions_are_negations(&csc_coeff, rhs) {
            return Some(build_scaled_term(csc_coeff, trig_squared("cot", csc_arg)));
        }
    }

    if let Some((csc_coeff, csc_arg)) = extract_scaled_trig_squared(rhs, "csc") {
        if expressions_are_negations(&csc_coeff, lhs) {
            return Some(build_scaled_term(csc_coeff, trig_squared("cot", csc_arg)));
        }
    }

    if let Some((sin_coeff, sin_arg)) = extract_scaled_trig_squared(lhs, "sin") {
        if expressions_are_negations(&sin_coeff, rhs) {
            return Some(build_scaled_term(rhs.clone(), trig_squared("cos", sin_arg)));
        }
    }

    if let Some((sin_coeff, sin_arg)) = extract_scaled_trig_squared(rhs, "sin") {
        if expressions_are_negations(&sin_coeff, lhs) {
            return Some(build_scaled_term(lhs.clone(), trig_squared("cos", sin_arg)));
        }
    }

    if let Some((cos_coeff, cos_arg)) = extract_scaled_trig_squared(lhs, "cos") {
        if expressions_are_negations(&cos_coeff, rhs) {
            return Some(build_scaled_term(rhs.clone(), trig_squared("sin", cos_arg)));
        }
    }

    if let Some((cos_coeff, cos_arg)) = extract_scaled_trig_squared(rhs, "cos") {
        if expressions_are_negations(&cos_coeff, lhs) {
            return Some(build_scaled_term(lhs.clone(), trig_squared("sin", cos_arg)));
        }
    }

    None
}

fn try_trig_identity_pair(lhs: &Expression, rhs: &Expression) -> Option<Expression> {
    if let Some(result) = try_direct_trig_identity_pair(lhs, rhs) {
        return Some(result);
    }

    let (common_factors, lhs_remainder, rhs_remainder) =
        extract_common_commutative_factors(lhs, rhs)?;
    if lhs_remainder == Expression::integer(1) && rhs_remainder == Expression::integer(1) {
        return None;
    }
    let reduced = try_trig_identity_pair(&lhs_remainder, &rhs_remainder)?;

    let mut result_factors = common_factors;
    result_factors.push(reduced);
    Some(build_expression_from_factors(result_factors))
}

fn check_pythagorean(terms: &[Expression]) -> Option<Vec<Expression>> {
    for (i, lhs) in terms.iter().enumerate() {
        for (j, rhs) in terms.iter().enumerate() {
            if i >= j {
                continue;
            }

            if let Some(replacement) = try_trig_identity_pair(lhs, rhs) {
                let mut remaining: Vec<_> = terms
                    .iter()
                    .enumerate()
                    .filter(|(k, _)| *k != i && *k != j)
                    .map(|(_, expr)| expr.clone())
                    .collect();
                remaining.push(replacement);
                return Some(remaining);
            }
        }
    }

    None
}

/// Simplify addition expressions with minimal overhead
pub fn simplify_addition_with_options(
    terms: &[Expression],
    factor_common_terms: bool,
) -> Expression {
    if terms.is_empty() {
        return Expression::integer(0);
    }

    let mut flattened_terms: Vec<Expression> = Vec::new();
    let mut to_process: VecDeque<&Expression> = terms.iter().collect();

    while let Some(term) = to_process.pop_front() {
        match term {
            Expression::Add(nested_terms) => {
                for nested_term in nested_terms.iter().rev() {
                    to_process.push_front(nested_term);
                }
            }
            Expression::Mul(factors) if factors.len() == 2 => {
                if let (Expression::Number(coeff), Expression::Add(add_terms)) =
                    (&factors[0], &factors[1])
                {
                    for add_term in add_terms.iter() {
                        let distributed = Expression::mul(vec![
                            Expression::Number(coeff.clone()),
                            add_term.clone(),
                        ]);
                        flattened_terms.push(distributed);
                    }
                } else if let (Expression::Add(add_terms), Expression::Number(coeff)) =
                    (&factors[0], &factors[1])
                {
                    for add_term in add_terms.iter() {
                        let distributed = Expression::mul(vec![
                            Expression::Number(coeff.clone()),
                            add_term.clone(),
                        ]);
                        flattened_terms.push(distributed);
                    }
                } else {
                    flattened_terms.push(term.clone());
                }
            }
            _ => flattened_terms.push(term.clone()),
        }
    }

    let terms = &flattened_terms;

    if terms.len() == 2 {
        if let Some(Ok(result)) = super::matrix_ops::try_matrix_add(&terms[0], &terms[1]) {
            return result;
        }
    }

    let mut int_sum = 0i64;
    let mut float_sum = 0.0;
    let mut has_float = false;
    let mut rational_sum: Option<BigRational> = None;
    let mut non_numeric_count = 0;
    let mut first_non_numeric: Option<Expression> = None;
    let mut numeric_result = None;

    for term in terms {
        let simplified_term = match term {
            Expression::Add(_) => term.clone(),
            Expression::Mul(factors) => simplify_multiplication(factors),
            Expression::Pow(base, exp) => simplify_power(base.as_ref(), exp.as_ref()),
            _ => term.simplify(),
        };
        match simplified_term {
            Expression::Number(Number::Integer(n)) => {
                int_sum = int_sum.saturating_add(n);
            }
            Expression::Number(Number::Float(f)) => {
                float_sum += f;
                has_float = true;
            }
            Expression::Number(Number::Rational(r)) => {
                if let Some(ref mut current_sum) = rational_sum {
                    *current_sum += r.as_ref();
                } else {
                    rational_sum = Some(r.as_ref().clone());
                }
            }
            _ => {
                non_numeric_count += 1;
                if first_non_numeric.is_none() {
                    first_non_numeric = Some(simplified_term);
                }
            }
        }
    }

    if let Some(rational) = rational_sum {
        let mut final_rational = rational;
        if int_sum != 0 {
            final_rational += BigRational::from(BigInt::from(int_sum));
        }
        if has_float {
            let float_val = final_rational.to_f64().unwrap_or(0.0) + float_sum;
            if float_val.abs() >= EPSILON {
                numeric_result = Some(Expression::Number(Number::float(float_val)));
            }
        } else if !final_rational.is_zero() {
            numeric_result = Some(Expression::Number(Number::rational(final_rational)));
        }
    } else if has_float {
        let total = int_sum as f64 + float_sum;
        if total.abs() >= EPSILON {
            numeric_result = Some(Expression::Number(Number::float(total)));
        }
    } else if int_sum != 0 {
        numeric_result = Some(Expression::integer(int_sum));
    }

    match (numeric_result.as_ref(), non_numeric_count) {
        (None, 0) => Expression::integer(0),
        (Some(num), 0) => num.clone(),
        (None, 1) => {
            first_non_numeric.expect("BUG: non_numeric_count is 1 but first_non_numeric is None")
        }
        (Some(num), 1) => {
            let simplified_non_numeric = first_non_numeric
                .expect("BUG: non_numeric_count is 1 but first_non_numeric is None");
            match num {
                Expression::Number(Number::Integer(0)) => simplified_non_numeric,
                Expression::Number(Number::Float(f)) if f.abs() < EPSILON => simplified_non_numeric,
                _ => {
                    let candidate_terms = vec![num.clone(), simplified_non_numeric.clone()];
                    if factor_common_terms {
                        if let Some(factored) = try_factor_common_terms(&candidate_terms) {
                            return factored;
                        }
                    }
                    if let Some(pythagorean_terms) = check_pythagorean(&candidate_terms) {
                        simplify_addition_with_options(&pythagorean_terms, factor_common_terms)
                    } else {
                        Expression::Add(Arc::new(candidate_terms))
                    }
                }
            }
        }
        _ => {
            let mut result_terms = Vec::with_capacity(non_numeric_count + 1);
            if let Some(num) = numeric_result {
                match num {
                    Expression::Number(Number::Integer(0)) => {}
                    Expression::Number(Number::Float(0.0)) => {}
                    _ => result_terms.push(num),
                }
            }

            let mut like_terms: Vec<(String, Expression, Vec<Expression>)> = Vec::new();

            for term in terms {
                if !matches!(term, Expression::Number(_)) {
                    let simplified_term = match term {
                        Expression::Add(_) => term.clone(),
                        Expression::Mul(factors) => simplify_multiplication(factors),
                        Expression::Pow(base, exp) => simplify_power(base.as_ref(), exp.as_ref()),
                        _ => term.simplify(),
                    };
                    match simplified_term {
                        Expression::Number(Number::Integer(0)) => {}
                        Expression::Number(Number::Float(0.0)) => {}
                        _ => {
                            let (coeff, base) =
                                extract_arithmetic_coefficient_and_base(&simplified_term);

                            let base_key = format!("{:?}", base);

                            if let Some(entry) =
                                like_terms.iter_mut().find(|(key, _, _)| key == &base_key)
                            {
                                entry.2.push(coeff);
                            } else {
                                like_terms.push((base_key, base.clone(), vec![coeff]));
                            }
                        }
                    }
                }
            }

            for (_, base, coeffs) in like_terms {
                if coeffs.len() == 1 {
                    let coeff = &coeffs[0];
                    match coeff {
                        Expression::Number(Number::Integer(1)) => {
                            result_terms.push(base);
                        }
                        _ => {
                            result_terms.push(Expression::Mul(Arc::new(vec![coeff.clone(), base])));
                        }
                    }
                } else {
                    let coeff_sum = simplify_addition_with_options(&coeffs, factor_common_terms);
                    match coeff_sum {
                        Expression::Number(Number::Integer(0)) => {}
                        Expression::Number(Number::Float(0.0)) => {}
                        Expression::Number(Number::Integer(1)) => {
                            result_terms.push(base);
                        }
                        _ => {
                            result_terms.push(Expression::Mul(Arc::new(vec![coeff_sum, base])));
                        }
                    }
                }
            }

            if factor_common_terms {
                if let Some(factored) = try_factor_common_terms(&result_terms) {
                    return factored;
                }
            }

            if let Some(pythagorean_terms) = check_pythagorean(&result_terms) {
                return simplify_addition_with_options(&pythagorean_terms, factor_common_terms);
            }

            match result_terms.len() {
                0 => Expression::integer(0),
                1 => result_terms
                    .into_iter()
                    .next()
                    .expect("BUG: result_terms has length 1 but iterator is empty"),
                _ => {
                    let commutativity =
                        Commutativity::combine(result_terms.iter().map(|t| t.commutativity()));

                    if commutativity.can_sort() {
                        result_terms.sort_by(expression_order);
                    }

                    Expression::Add(Arc::new(result_terms))
                }
            }
        }
    }
}

pub fn simplify_addition(terms: &[Expression]) -> Expression {
    simplify_addition_with_options(terms, true)
}

pub fn simplify_addition_without_factoring(terms: &[Expression]) -> Expression {
    simplify_addition_with_options(terms, false)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::simplify::Simplify;
    use crate::{expr, symbol, Expression};

    #[test]
    fn test_addition_simplification() {
        let expr = simplify_addition(&[Expression::integer(2), Expression::integer(3)]);
        assert_eq!(expr, Expression::integer(5));

        let expr = simplify_addition(&[Expression::integer(5), Expression::integer(0)]);
        assert_eq!(expr, Expression::integer(5));

        let x = symbol!(x);
        let expr = simplify_addition(&[Expression::integer(2), Expression::symbol(x.clone())]);
        assert_eq!(
            expr,
            Expression::add(vec![Expression::integer(2), Expression::symbol(x)])
        );
    }

    #[test]
    fn test_scalar_terms_combine() {
        let x = symbol!(x);
        let y = symbol!(y);

        let xy = Expression::mul(vec![
            Expression::symbol(x.clone()),
            Expression::symbol(y.clone()),
        ]);
        let yx = Expression::mul(vec![
            Expression::symbol(y.clone()),
            Expression::symbol(x.clone()),
        ]);
        let expr = Expression::add(vec![xy.clone(), yx.clone()]);

        let simplified = expr.simplify();

        match simplified {
            Expression::Mul(factors) => {
                assert_eq!(factors.len(), 3);
                assert_eq!(factors[0], Expression::integer(2));
            }
            _ => panic!("Expected Mul, got {:?}", simplified),
        }
    }

    #[test]
    fn test_matrix_terms_not_combined() {
        let mat_a = symbol!(A; matrix);
        let mat_b = symbol!(B; matrix);

        let ab = Expression::mul(vec![
            Expression::symbol(mat_a.clone()),
            Expression::symbol(mat_b.clone()),
        ]);
        let ba = Expression::mul(vec![
            Expression::symbol(mat_b.clone()),
            Expression::symbol(mat_a.clone()),
        ]);
        let expr = Expression::add(vec![ab.clone(), ba.clone()]);

        let simplified = expr.simplify();

        match simplified {
            Expression::Add(terms) => {
                assert_eq!(terms.len(), 2);
            }
            _ => panic!("Expected Add with 2 terms, got {:?}", simplified),
        }
    }

    #[test]
    fn test_identical_matrix_terms_combine() {
        let mat_a = symbol!(A; matrix);
        let mat_b = symbol!(B; matrix);

        let ab1 = Expression::mul(vec![
            Expression::symbol(mat_a.clone()),
            Expression::symbol(mat_b.clone()),
        ]);
        let ab2 = Expression::mul(vec![
            Expression::symbol(mat_a.clone()),
            Expression::symbol(mat_b.clone()),
        ]);
        let expr = Expression::add(vec![ab1, ab2]);

        let simplified = expr.simplify();

        match simplified {
            Expression::Mul(factors) => {
                assert_eq!(factors.len(), 3);
                assert_eq!(factors[0], Expression::integer(2));
            }
            _ => panic!("Expected Mul, got {:?}", simplified),
        }
    }

    #[test]
    fn test_operator_terms_not_combined() {
        let operator_p = symbol!(P; operator);
        let operator_q = symbol!(Q; operator);

        let pq = Expression::mul(vec![
            Expression::symbol(operator_p.clone()),
            Expression::symbol(operator_q.clone()),
        ]);
        let qp = Expression::mul(vec![
            Expression::symbol(operator_q.clone()),
            Expression::symbol(operator_p.clone()),
        ]);
        let expr = Expression::add(vec![pq, qp]);

        let simplified = expr.simplify();

        match simplified {
            Expression::Add(terms) => {
                assert_eq!(terms.len(), 2);
            }
            _ => panic!("Expected Add with 2 terms, got {:?}", simplified),
        }
    }

    #[test]
    fn test_quaternion_terms_not_combined() {
        let i = symbol!(i; quaternion);
        let j = symbol!(j; quaternion);

        let ij = Expression::mul(vec![
            Expression::symbol(i.clone()),
            Expression::symbol(j.clone()),
        ]);
        let ji = Expression::mul(vec![
            Expression::symbol(j.clone()),
            Expression::symbol(i.clone()),
        ]);
        let expr = Expression::add(vec![ij, ji]);

        let simplified = expr.simplify();

        match simplified {
            Expression::Add(terms) => {
                assert_eq!(terms.len(), 2);
            }
            _ => panic!("Expected Add with 2 terms, got {:?}", simplified),
        }
    }

    #[test]
    fn test_scalar_addition_sorts() {
        let y = symbol!(y);
        let x = symbol!(x);
        let expr = Expression::add(vec![
            Expression::symbol(y.clone()),
            Expression::symbol(x.clone()),
        ]);
        let simplified = expr.simplify();

        match simplified {
            Expression::Add(terms) => {
                assert_eq!(terms.len(), 2);
                assert_eq!(terms[0], Expression::symbol(symbol!(x)));
                assert_eq!(terms[1], Expression::symbol(symbol!(y)));
            }
            _ => panic!("Expected Add, got {:?}", simplified),
        }
    }

    #[test]
    fn test_matrix_addition_preserves_order() {
        let mat_b = symbol!(B; matrix);
        let mat_a = symbol!(A; matrix);
        let expr = Expression::add(vec![
            Expression::symbol(mat_b.clone()),
            Expression::symbol(mat_a.clone()),
        ]);
        let simplified = expr.simplify();

        match simplified {
            Expression::Add(terms) => {
                assert_eq!(terms.len(), 2);
                assert_eq!(terms[0], Expression::symbol(symbol!(B; matrix)));
                assert_eq!(terms[1], Expression::symbol(symbol!(A; matrix)));
            }
            _ => panic!("Expected Add, got {:?}", simplified),
        }
    }

    #[test]
    fn test_mixed_scalar_matrix_addition_preserves_order() {
        let x = symbol!(x);
        let mat_a = symbol!(A; matrix);
        let expr = Expression::add(vec![
            Expression::symbol(x.clone()),
            Expression::symbol(mat_a.clone()),
        ]);
        let simplified = expr.simplify();

        match simplified {
            Expression::Add(terms) => {
                assert_eq!(terms.len(), 2);
                assert_eq!(terms[0], expr!(x));
                assert_eq!(terms[1], Expression::symbol(symbol!(A; matrix)));
            }
            _ => panic!("Expected Add, got {:?}", simplified),
        }
    }

    #[test]
    fn test_three_scalar_like_terms_combine() {
        let x = symbol!(x);
        let expr = Expression::add(vec![
            Expression::symbol(x.clone()),
            Expression::symbol(x.clone()),
            Expression::symbol(x.clone()),
        ]);
        let simplified = expr.simplify();

        match simplified {
            Expression::Mul(factors) => {
                assert_eq!(factors.len(), 2);
                assert_eq!(factors[0], Expression::integer(3));
                assert_eq!(factors[1], expr!(x));
            }
            _ => panic!("Expected Mul, got {:?}", simplified),
        }
    }

    #[test]
    fn test_three_matrix_like_terms_combine() {
        let mat_a = symbol!(A; matrix);
        let expr = Expression::add(vec![
            Expression::symbol(mat_a.clone()),
            Expression::symbol(mat_a.clone()),
            Expression::symbol(mat_a.clone()),
        ]);
        let simplified = expr.simplify();

        match simplified {
            Expression::Mul(factors) => {
                assert_eq!(factors.len(), 2);
                assert_eq!(factors[0], Expression::integer(3));
                assert_eq!(factors[1], Expression::symbol(symbol!(A; matrix)));
            }
            _ => panic!("Expected Mul, got {:?}", simplified),
        }
    }

    #[test]
    fn test_incompatible_matrix_addition_during_simplification() {
        let a = Expression::matrix(vec![vec![expr!(1), expr!(2)], vec![expr!(3), expr!(4)]]);
        let b = Expression::matrix(vec![vec![expr!(5), expr!(6), expr!(7)]]);

        let expr = Expression::add(vec![a.clone(), b.clone()]);
        let simplified = expr.simplify();

        match simplified {
            Expression::Add(terms) => {
                assert_eq!(terms.len(), 2);
            }
            _ => panic!(
                "Expected Add with 2 terms for incompatible matrices during simplification, got {:?}",
                simplified
            ),
        }
    }

    #[test]
    fn test_pythagorean_identity_sin_cos() {
        let x = symbol!(x);
        let sin_x = Expression::function("sin", vec![Expression::symbol(x.clone())]);
        let cos_x = Expression::function("cos", vec![Expression::symbol(x.clone())]);
        let sin_squared = Expression::pow(sin_x, Expression::integer(2));
        let cos_squared = Expression::pow(cos_x, Expression::integer(2));

        let expr = Expression::add(vec![sin_squared, cos_squared]);
        let simplified = expr.simplify();

        assert_eq!(simplified, Expression::integer(1));
    }

    #[test]
    fn test_pythagorean_identity_cos_sin() {
        let x = symbol!(x);
        let sin_x = Expression::function("sin", vec![Expression::symbol(x.clone())]);
        let cos_x = Expression::function("cos", vec![Expression::symbol(x.clone())]);
        let sin_squared = Expression::pow(sin_x, Expression::integer(2));
        let cos_squared = Expression::pow(cos_x, Expression::integer(2));

        let expr = Expression::add(vec![cos_squared, sin_squared]);
        let simplified = expr.simplify();

        assert_eq!(simplified, Expression::integer(1));
    }

    #[test]
    fn test_pythagorean_identity_different_args() {
        let x = symbol!(x);
        let y = symbol!(y);
        let sin_x = Expression::function("sin", vec![Expression::symbol(x.clone())]);
        let cos_y = Expression::function("cos", vec![Expression::symbol(y.clone())]);
        let sin_squared = Expression::pow(sin_x, Expression::integer(2));
        let cos_squared = Expression::pow(cos_y, Expression::integer(2));

        let expr = Expression::add(vec![sin_squared, cos_squared]);
        let simplified = expr.simplify();

        match simplified {
            Expression::Add(_) => {}
            _ => panic!("Expected Add (unchanged), got {:?}", simplified),
        }
    }

    #[test]
    fn test_pythagorean_identity_with_additional_terms() {
        let x = symbol!(x);
        let y = symbol!(y);
        let sin_x = Expression::function("sin", vec![Expression::symbol(x.clone())]);
        let cos_x = Expression::function("cos", vec![Expression::symbol(x.clone())]);
        let sin_squared = Expression::pow(sin_x, Expression::integer(2));
        let cos_squared = Expression::pow(cos_x, Expression::integer(2));

        let expr = Expression::add(vec![
            sin_squared,
            cos_squared,
            Expression::symbol(y.clone()),
        ]);
        let simplified = expr.simplify();

        assert_eq!(
            simplified,
            Expression::add(vec![Expression::integer(1), Expression::symbol(y)])
        );
    }

    #[test]
    fn test_pythagorean_identity_not_squared() {
        let x = symbol!(x);
        let sin_x = Expression::function("sin", vec![Expression::symbol(x.clone())]);
        let cos_x = Expression::function("cos", vec![Expression::symbol(x.clone())]);

        let expr = Expression::add(vec![sin_x, cos_x]);
        let simplified = expr.simplify();

        match simplified {
            Expression::Add(_) => {}
            _ => panic!("Expected Add (unchanged), got {:?}", simplified),
        }
    }

    #[test]
    fn test_pythagorean_identity_with_numeric_coefficient() {
        let expr = expr!((2 * ((sin(x)) ^ 2)) + (2 * ((cos(x)) ^ 2)));
        let simplified = expr.simplify();

        assert_eq!(simplified, expr!(2));
    }

    #[test]
    fn test_pythagorean_identity_with_symbolic_coefficient() {
        let expr = expr!((a * ((sin(x)) ^ 2)) + (a * ((cos(x)) ^ 2)));
        let simplified = expr.simplify();

        assert_eq!(simplified, expr!(a));
    }

    #[test]
    fn test_tan_squared_plus_one_to_sec_squared() {
        let expr = expr!(((tan(x)) ^ 2) + 1);
        let simplified = expr.simplify();

        assert_eq!(simplified, expr!((sec(x)) ^ 2));
    }

    #[test]
    fn test_sec_squared_minus_tan_squared_to_one() {
        let expr = expr!(((sec(x)) ^ 2) - ((tan(x)) ^ 2));
        let simplified = expr.simplify();

        assert_eq!(simplified, expr!(1));
    }

    #[test]
    fn test_one_minus_sin_squared_to_cos_squared() {
        let expr = expr!(1 - ((sin(x)) ^ 2));
        let simplified = expr.simplify();

        assert_eq!(simplified, expr!((cos(x)) ^ 2));
    }

    #[test]
    fn test_csc_squared_minus_one_to_cot_squared_with_symbolic_coefficient() {
        let expr = expr!((a * ((csc(x)) ^ 2)) - a);
        let simplified = expr.simplify();

        assert_eq!(simplified, expr!(a * ((cot(x)) ^ 2)));
    }

    #[test]
    fn test_extracts_common_symbolic_factor() {
        let expr = expr!((x * y) + (x * z));
        let simplified = expr.simplify();

        assert_eq!(simplified, expr!(x * (y + z)));
    }

    #[test]
    fn test_extracts_common_integer_gcd_factor() {
        let expr = expr!((2 * x) + (4 * y));
        let simplified = expr.simplify();

        assert_eq!(simplified, expr!(2 * (x + (2 * y))));
    }

    #[test]
    fn test_extracts_common_factor_with_implicit_one() {
        let expr = expr!(x + (x * y));
        let simplified = expr.simplify();

        assert_eq!(simplified, expr!(x * (1 + y)));
    }

    #[test]
    fn test_common_factor_exposes_pythagorean_identity() {
        let expr = expr!(
            ((cos(y)) ^ 2 * cos(z) * sin(z)) + ((sin(y)) ^ 2 * cos(z) * sin(z))
        );
        let simplified = expr.simplify();

        assert_eq!(simplified, expr!(cos(z) * sin(z)));
    }

    #[test]
    fn test_does_not_factor_noncommutative_prefix() {
        let matrix_a = symbol!(A; matrix);
        let matrix_b = symbol!(B; matrix);
        let matrix_c = symbol!(C; matrix);

        let expr = Expression::add(vec![
            Expression::mul(vec![
                Expression::symbol(matrix_a.clone()),
                Expression::symbol(matrix_b),
            ]),
            Expression::mul(vec![
                Expression::symbol(matrix_a),
                Expression::symbol(matrix_c),
            ]),
        ]);
        let simplified = expr.simplify();

        assert_eq!(simplified, expr);
    }

    #[test]
    fn test_distribute_numeric_over_addition() {
        let x = symbol!(x);

        let expr = Expression::add(vec![Expression::mul(vec![
            Expression::integer(-1),
            Expression::add(vec![Expression::symbol(x.clone()), Expression::integer(1)]),
        ])]);

        let simplified = expr.simplify();

        match &simplified {
            Expression::Add(terms) => {
                assert_eq!(terms.len(), 2);
                let has_neg_one = terms
                    .iter()
                    .any(|t| matches!(t, Expression::Number(Number::Integer(-1))));
                let has_neg_x = terms.iter().any(|t| {
                    matches!(t, Expression::Mul(factors)
                        if factors.len() == 2
                        && matches!(factors[0], Expression::Number(Number::Integer(-1)))
                    )
                });
                assert!(
                    has_neg_one || has_neg_x,
                    "Expected distributed terms, got {:?}",
                    simplified
                );
            }
            _ => panic!("Expected Add with distributed terms, got {:?}", simplified),
        }
    }
}
