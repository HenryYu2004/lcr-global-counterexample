#!/usr/bin/env python3
"""High-precision numerical cross-check of the EXACTLY DEFINED probit pair.

Requires mpmath >= 1.3. Example:
  python3 check_probit_counterexample.py

This is numerical evidence, not an interval certificate or a replacement for the
Lean proof. Finite displayed decimals are NOT the exact counterexample.

We evaluate H_j using its convergent Taylor expansion at t=0. The identity
  h_t(y)^j = y^j integral_[0,1]^j exp(-t*y^2*sum(u_l^2)/2) du
gives an absolute truncation bound after degree N:
  (j*t/2)^(N+1)/(N+1)! * E|Y|^(j+2*N+2).
We bound the absolute moment by sqrt(E Y^(2*j+4*N+4)). This bound does not
include floating-point roundoff; independent precision/truncation reruns check
roundoff empirically. Normal moments are evaluated by their exact recurrence.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
from pathlib import Path

import mpmath as mp


NAMES = ("pi", "mu0", "mu1", "v0", "v1")


def gaussian_moments(mu, variance, degree):
    result = [mp.mpf(1), mu]
    for k in range(2, degree + 1):
        result.append(mu * result[-1] + (k - 1) * variance * result[-2])
    return result[: degree + 1]


def mixture_moments(theta, degree):
    pi, mu0, mu1, v0, v1 = theta
    zero = gaussian_moments(mu0, v0, degree)
    one = gaussian_moments(mu1, v1, degree)
    return [(1 - pi) * zero[k] + pi * one[k] for k in range(degree + 1)]


def convolution(left, right, degree):
    return [mp.fsum(left[a] * right[k - a] for a in range(k + 1)
                    if a < len(left) and k - a < len(right))
            for k in range(degree + 1)]


def h_coefficients(degree):
    base = [1 / (mp.mpf(2) ** k * mp.factorial(k) * (2 * k + 1))
            for k in range(degree + 1)]
    powers = [[mp.mpf(1)] + [mp.mpf(0)] * degree]
    for _ in range(5):
        powers.append(convolution(powers[-1], base, degree))
    return powers


def transformed_moments(theta, t, degree, coefficients=None):
    if coefficients is None:
        coefficients = h_coefficients(degree)
    raw = mixture_moments(theta, 5 + 2 * degree)
    return mp.matrix([mp.fsum(coefficients[j][k] * (-t) ** k * raw[j + 2 * k]
                              for k in range(degree + 1))
                      for j in range(1, 6)])


def truncation_bounds(theta, t, degree):
    raw = mixture_moments(theta, 2 * (5 + 2 * degree + 2))
    return [(j * t / 2) ** (degree + 1) / mp.factorial(degree + 1)
            * mp.sqrt(raw[2 * (j + 2 * degree + 2)]) for j in range(1, 6)]


def algebraic_seed():
    polynomial = lambda p: (512*p**9 - 2240*p**7 - 1728*p**6 - 20040*p**5
                            + 65040*p**4 - 13221*p**3 - 47115*p**2
                            + 12960*p + 5832)
    p = mp.findroot(polynomial, (mp.mpf(".634"), mp.mpf(".635")),
                    tol=mp.eps, verify=True)
    c = (24*p**3 - 80*p**2 + 45*p + 54) / (2*p*(36 - 8*p**3 + 15*p))
    s = 3/(2*p) - 3*c
    delta = mp.sqrt(s*s + 4*p)
    mu0, mu1 = (s-delta)/2, (s+delta)/2
    pi = -mu0/delta
    return p, mp.matrix([pi, mu0, mu1, mp.mpf("2.5")-p+c*mu0,
                         mp.mpf("2.5")-p+c*mu1]), polynomial(p)


def gaussian_jacobian(theta):
    pi, mu0, mu1, v0, v1 = theta
    zero = gaussian_moments(mu0, v0, 5)
    one = gaussian_moments(mu1, v1, 5)
    return mp.matrix([[one[j]-zero[j], (1-pi)*j*zero[j-1], pi*j*one[j-1],
                       (1-pi)*j*(j-1)*zero[j-2]/2 if j >= 2 else 0,
                       pi*j*(j-1)*one[j-2]/2 if j >= 2 else 0]
                      for j in range(1, 6)])


def pattern_coefficients(successes, epsilon):
    """Coefficients of (1/2+b*w)^s(1/2-b*w)^(5-s), b=phi(0)*epsilon."""
    a = mp.mpf(".5")
    b = epsilon / mp.sqrt(2 * mp.pi)
    left = [mp.binomial(successes, k) * a**(successes-k) * b**k
            for k in range(successes+1)]
    right = [mp.binomial(5-successes, k) * a**(5-successes-k) * (-b)**k
             for k in range(6-successes)]
    return convolution(left, right, 5)


def original_parameters(theta, epsilon):
    pi, mu0, mu1, v0, v1 = theta
    return {"pi": pi, "alpha_i0": epsilon*mu0, "alpha_i1": epsilon*mu1,
            "beta_i0": epsilon*mp.sqrt(v0), "beta_i1": epsilon*mp.sqrt(v1)}


def infinity_norm(vector):
    return max(abs(value) for value in vector)


def run(dps, degree):
    mp.mp.dps = dps
    t, epsilon = mp.mpf("1e-40"), mp.mpf("1e-20")
    theta_a = mp.matrix([mp.mpf(".5"), -1, 1, 1, 2])
    p, seed, root_residual = algebraic_seed()
    jacobian = gaussian_jacobian(seed)
    coefficients = h_coefficients(degree)
    target = transformed_moments(theta_a, t, degree, coefficients)
    seed_h = transformed_moments(seed, t, degree, coefficients)
    seed_residual = seed_h-target
    corrected = seed.copy()
    history = []
    # Fixed Jacobian: this is precisely the defining iteration in the paper.
    for iteration in range(12):
        residual = transformed_moments(corrected, t, degree, coefficients)-target
        update = mp.lu_solve(jacobian, residual)
        history.append({"iteration": iteration, "H_residual_inf": infinity_norm(residual),
                        "update_inf": infinity_norm(update)})
        corrected -= update
        if infinity_norm(update) < mp.mpf(10)**(-dps+12):
            break
    corrected_h = transformed_moments(corrected, t, degree, coefficients)
    higher_h = transformed_moments(corrected, t, degree+2)
    higher_target = transformed_moments(theta_a, t, degree+2)
    residual = higher_h-higher_target
    assert infinity_norm(residual) < mp.mpf(10)**(-dps+12)
    assert infinity_norm(corrected-seed) < mp.mpf("1e-18")
    assert 0 < corrected[0] < 1 and corrected[1] < 0 < corrected[2]
    assert 0 < corrected[3] < corrected[4]
    assert corrected[0] != theta_a[0]

    # A table with a few decimal digits is for orientation only. Quantify why
    # copying those rounded entries does not reproduce an exact counterexample.
    display_b = {key: mp.nstr(value, 15)
                 for key, value in original_parameters(corrected, epsilon).items()}
    rounded_b = {key: mp.mpf(value) for key, value in display_b.items()}
    rounded_theta = mp.matrix([rounded_b["pi"], rounded_b["alpha_i0"]/epsilon,
                              rounded_b["alpha_i1"]/epsilon,
                              (rounded_b["beta_i0"]/epsilon)**2,
                              (rounded_b["beta_i1"]/epsilon)**2])
    rounded_h = transformed_moments(rounded_theta, t, degree+2)

    cells = []
    h_a = [mp.mpf(1)] + list(higher_target)
    h_b = [mp.mpf(1)] + list(higher_h)
    h_seed = [mp.mpf(1)] + list(transformed_moments(seed, t, degree+2))
    for successes in range(6):
        coeff = pattern_coefficients(successes, epsilon)
        cell_a = mp.fsum(c*v for c, v in zip(coeff, h_a))
        cell_b = mp.fsum(c*v for c, v in zip(coeff, h_b))
        # Paired summation preserves discrepancies below the absolute precision
        # at which two probabilities near 1/32 can be subtracted.
        seed_delta = mp.fsum(coeff[k]*(h_seed[k]-h_a[k]) for k in range(1, 6))
        corrected_delta = mp.fsum(coeff[k]*(h_b[k]-h_a[k]) for k in range(1, 6))
        rounded_delta = mp.fsum(coeff[k]*(rounded_h[k-1]-h_a[k]) for k in range(1, 6))
        cells.append({"successes": successes, "multiplicity": math.comb(5, successes),
                      "probability_A": cell_a, "probability_B": cell_b,
                      "A_minus_uniform": cell_a-mp.mpf(1)/32,
                      "B_minus_A_subtracted": cell_b-cell_a,
                      "B_minus_A_paired": corrected_delta,
                      "rounded_15_digit_B_minus_A_paired": rounded_delta,
                      "seed_B_minus_A_paired": seed_delta})
    all_patterns = [{"pattern": "".join(map(str, x)), "successes": sum(x),
                     "B_minus_A_paired": cells[sum(x)]["B_minus_A_paired"]}
                    for x in itertools.product((0, 1), repeat=5)]
    normalization_a = mp.fsum(cell["multiplicity"]*cell["probability_A"] for cell in cells)-1
    normalization_b = mp.fsum(cell["multiplicity"]*cell["probability_B"] for cell in cells)-1
    assert abs(normalization_a) < mp.mpf(10)**(-dps+10)
    assert abs(normalization_b) < mp.mpf(10)**(-dps+10)
    return {"dps": dps, "t": t, "epsilon": epsilon, "series_degree": degree,
            "crosscheck_series_degree": degree+2, "p_root": p,
            "root_polynomial_residual": root_residual,
            "gaussian_A": dict(zip(NAMES, theta_a)),
            "gaussian_B_seed": dict(zip(NAMES, seed)),
            "gaussian_B_corrected": dict(zip(NAMES, corrected)),
            "original_A": original_parameters(theta_a, epsilon),
            "original_B_corrected": original_parameters(corrected, epsilon),
            "display_original_B_15_significant_digits": display_b,
            "gaussian_parameter_correction": dict(zip(NAMES, corrected-seed)),
            "gaussian_parameter_correction_inf": infinity_norm(corrected-seed),
            "seed_H_residual": list(seed_residual),
            "seed_H_residual_inf": infinity_norm(seed_residual),
            "corrected_H_residual": list(residual),
            "corrected_H_residual_inf": infinity_norm(residual),
            "series_truncation_bound_A": truncation_bounds(theta_a, t, degree),
            "series_truncation_bound_B": truncation_bounds(corrected, t, degree),
            "series_degree_crosscheck_H_difference_inf": infinity_norm(higher_h-corrected_h),
            "iteration_history": history, "six_cell_types": cells,
            "all_32_patterns": all_patterns,
            "normalization_residual_A": normalization_a,
            "normalization_residual_B": normalization_b,
            "max_seed_cell_discrepancy": max(abs(c["seed_B_minus_A_paired"]) for c in cells),
            "max_rounded_15_digit_cell_discrepancy": max(abs(c["rounded_15_digit_B_minus_A_paired"]) for c in cells),
            "max_corrected_cell_discrepancy_paired": max(abs(c["B_minus_A_paired"]) for c in cells),
            "max_corrected_cell_discrepancy_subtracted": max(abs(c["B_minus_A_subtracted"]) for c in cells)}


def decimal_strings(value, digits):
    if isinstance(value, dict):
        return {key: decimal_strings(item, digits) for key, item in value.items()}
    if isinstance(value, list):
        return [decimal_strings(item, digits) for item in value]
    if isinstance(value, mp.mpf):
        return mp.nstr(value, digits)
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("probit_numerical_check.json"))
    args = parser.parse_args()
    runs = []
    for dps, degree in ((200, 7), (280, 9)):
        result = run(dps, degree)
        runs.append(decimal_strings(result, dps))
        print(json.dumps({"dps": dps,
                          "correction_inf": mp.nstr(result["gaussian_parameter_correction_inf"], 12),
                          "H_residual_inf": mp.nstr(result["corrected_H_residual_inf"], 12),
                          "seed_cell_discrepancy": mp.nstr(result["max_seed_cell_discrepancy"], 12),
                          "corrected_cell_discrepancy_paired": mp.nstr(result["max_corrected_cell_discrepancy_paired"], 12)}, indent=2))
    mp.mp.dps = 300
    cross = max(abs(mp.mpf(runs[0]["gaussian_B_corrected"][key])
                    - mp.mpf(runs[1]["gaussian_B_corrected"][key])) for key in NAMES)
    assert cross < mp.mpf("1e-190")
    receipt = {"purpose": "Numerical cross-check; not a new formal or interval certificate.",
               "method": "Fixed Gaussian Jacobian correction; Gaussian raw-moment expansion of h_t moments with an analytic absolute Taylor truncation bound.",
               "rounding_warning": "Finite decimal parameters do not define the exact alias. Use the algebraic seed and infinite fixed-point sequence for exact definition.",
               "mpmath_version": mp.__version__,
               "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               "runs": runs, "cross_precision_parameter_difference_inf": mp.nstr(cross, 30)}
    args.output.write_text(json.dumps(receipt, indent=2)+"\n")
    print("Receipt:", args.output.resolve())
    print("Original corrected parameters (15 significant digits):")
    for key, value in runs[-1]["original_B_corrected"].items():
        print(key, mp.nstr(mp.mpf(value), 15))


if __name__ == "__main__":
    main()
