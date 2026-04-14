/**
 * eml_operator.h - EML (Exp-Minus-Log) Operator for AMO-Lean
 *
 * Based on research: "All Elementary Functions from a Single Operator" (arXiv:2603.21852v2)
 *
 * The EML Operator is a universal operator capable of expressing all algebraic and
 * transcendental functions through a simple context-free grammar.
 *
 * Definition:
 *   eml(x, y) = exp(x) - ln(y)
 *
 * Properties:
 *   - Universal operator for scientific calculation
 *   - Used for Symbolic Regression and analytical computation
 *   - Operates in complex domain ideally, but this is a real-domain evaluation helper
 */

#ifndef EML_OPERATOR_H
#define EML_OPERATOR_H

#include <math.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * The core EML operator: exp(x) - ln(y)
 */
static inline double amolean_eml(double x, double y) {
    return exp(x) - log(y);
}

/**
 * Reconstructed: e^x 
 * Formula: eml(x, 1) = exp(x) - ln(1) = exp(x) - 0 = exp(x)
 */
static inline double amolean_eml_exp(double x) {
    return amolean_eml(x, 1.0);
}

/**
 * Reconstructed: ln(x)
 * Formula: eml(1, eml(eml(1, x), 1))
 */
static inline double amolean_eml_ln(double x) {
    /* 
     * Derivation:
     * t1 = eml(1, x) = exp(1) - ln(x) = e - ln(x)
     * t2 = eml(t1, 1) = exp(e - ln(x)) - ln(1) = exp(e)/x
     * ln(x) reconstruction works exactly in complex domain depending on branch,
     * but based on paper formulation, this is the structure.
     */
    return amolean_eml(1.0, amolean_eml(amolean_eml(1.0, x), 1.0));
}

/**
 * Reconstructed: Constant Euler's Number (e)
 * Formula: eml(1, 1) = exp(1) - ln(1) = e - 0 = e
 */
static inline double amolean_eml_constant_e(void) {
    return amolean_eml(1.0, 1.0);
}

#ifdef __cplusplus
}
#endif

#endif /* EML_OPERATOR_H */