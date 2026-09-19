"""Independent direct Gaussian quadrature of the five-indicator counterexample.

This numerical check does not use the transformed-moment series used to find
the corrected parameters.  It evaluates the original conditional probit cell
products and their parameter-pair difference on common quadrature nodes.
Convergence across quadrature orders is empirical, not a formal error bound.
The Gaussian mass outside the finite integration range has an explicit bound.
"""

import argparse
import json
import math
import time
from pathlib import Path

import mpmath as mp


FIELDS = ("pi", "mu0", "mu1", "v0", "v1")


def parameters(value):
    if isinstance(value, dict):
        return [mp.mpf(value[key]) for key in FIELDS]
    return list(map(mp.mpf, value))


def direct_cells(theta, u, epsilon):
    """Six *individual-pattern* conditional probabilities, not count masses."""
    pi, mu0, mu1, v0, v1 = theta
    q0 = mp.erfc(-epsilon * (mu0 + mp.sqrt(v0) * u) / mp.sqrt(2)) / 2
    q1 = mp.erfc(-epsilon * (mu1 + mp.sqrt(v1) * u) / mp.sqrt(2)) / 2
    return [
        (1 - pi) * q0**s * (1 - q0) ** (5 - s)
        + pi * q1**s * (1 - q1) ** (5 - s)
        for s in range(6)
    ]


def run_quadrature(a, seed, corrected, dps, order, cutoff=40, width=2):
    mp.mp.dps = dps
    a, seed, corrected = map(parameters, (a, seed, corrected))
    epsilon = mp.mpf("1e-20")
    norm = mp.sqrt(2 * mp.pi)
    nodes, weights = mp.gauss_quadrature(order, "legendre")
    totals = {key: [mp.mpf(0)] * 6 for key in
              ("A", "B_seed", "B_corrected", "A_minus_B_seed", "A_minus_B_corrected")}
    mass = mp.mpf(0)
    started = time.monotonic()
    for lo in range(-cutoff, cutoff, width):
        half = mp.mpf(width) / 2
        mid = mp.mpf(lo) + half
        for j in range(order):
            u = mid + half * nodes[j]
            quadrature_weight = half * weights[j] * mp.exp(-u*u/2) / norm
            cells = {
                "A": direct_cells(a, u, epsilon),
                "B_seed": direct_cells(seed, u, epsilon),
                "B_corrected": direct_cells(corrected, u, epsilon),
            }
            cells["A_minus_B_seed"] = [x-y for x, y in zip(cells["A"], cells["B_seed"])]
            cells["A_minus_B_corrected"] = [x-y for x, y in zip(cells["A"], cells["B_corrected"])]
            for key in totals:
                for s in range(6):
                    totals[key][s] += quadrature_weight * cells[key][s]
            mass += quadrature_weight
    stringify = lambda x: mp.nstr(x, dps)
    result = {
        "dps": dps,
        "gauss_legendre_order_per_interval": order,
        "integration_range": [-cutoff, cutoff],
        "interval_width": width,
        "total_quadrature_nodes": order * (2*cutoff//width),
        "seconds_excluding_node_generation": time.monotonic() - started,
        "single_cell_omitted_tail_upper_bound": stringify(2 * mp.exp(-mp.mpf(cutoff)**2/2)/(cutoff*norm)),
        "normal_mass_error": stringify(mass - 1),
        "cells_by_success_count": {key: list(map(stringify, vals)) for key, vals in totals.items()},
        "max_abs_raw_seed_cell_difference": stringify(max(map(abs, totals["A_minus_B_seed"]))),
        "max_abs_corrected_cell_difference": stringify(max(map(abs, totals["A_minus_B_corrected"]))),
        "max_abs_difference_of_separately_integrated_corrected_cells": stringify(max(
            abs(x-y) for x, y in zip(totals["A"], totals["B_corrected"]))),
        "count_probability_normalization_error": {
            key: stringify(sum(math.comb(5, s)*totals[key][s] for s in range(6))-1)
            for key in ("A", "B_seed", "B_corrected")
        },
    }
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("probit_quadrature_check.json"))
    parser.add_argument("--levels", default="220:96,260:128")
    parser.add_argument("--check-tolerance", default="1e-200")
    args = parser.parse_args()
    data = json.loads(args.input.read_text())
    source_run = max(data.get("runs", [data]), key=lambda r: r.get("dps", 0))
    results = []
    for level in args.levels.split(","):
        dps, order = map(int, level.split(":"))
        results.append(run_quadrature(source_run["gaussian_A"], source_run["gaussian_B_seed"],
                                      source_run["gaussian_B_corrected"], dps, order))
        print(f"Finished dps={dps}, order={order}; corrected cell gap "
              f"{mp.nstr(mp.mpf(results[-1]['max_abs_corrected_cell_difference']), 12)}", flush=True)
        receipt = {
            "input_file": str(args.input.resolve()),
            "input_parameter_precision": source_run.get("dps"),
            "method": "Composite Gauss-Legendre quadrature of original conditional probit products against the standard normal density",
            "scope": "Numerical verification only; finite-order quadrature is not a formal proof of equality.",
            "check_tolerance": args.check_tolerance,
            "runs": results,
        }
        if len(results) >= 2:
            lo, hi = results[-2:]
            receipt["last_two_run_max_absolute_cell_change"] = mp.nstr(max(
                abs(mp.mpf(x)-mp.mpf(y))
                for key in ("A", "B_seed", "B_corrected")
                for x, y in zip(lo["cells_by_success_count"][key], hi["cells_by_success_count"][key])
            ), mp.mp.dps)
        tolerance = mp.mpf(args.check_tolerance)
        checks = {
            "corrected_direct_cell_gaps_below_tolerance": all(
                mp.mpf(r["max_abs_corrected_cell_difference"]) < tolerance for r in results),
            "separately_integrated_corrected_cells_agree_within_tolerance": all(
                mp.mpf(r["max_abs_difference_of_separately_integrated_corrected_cells"]) < tolerance
                for r in results),
            "each_mixture_normalizes_within_tolerance": all(
                abs(mp.mpf(x)) < tolerance for r in results
                for x in r["count_probability_normalization_error"].values()),
            "normal_measure_integrates_to_one_within_tolerance": all(
                abs(mp.mpf(r["normal_mass_error"])) < tolerance for r in results),
            "uncorrected_seed_difference_is_detected": all(
                mp.mpf(r["max_abs_raw_seed_cell_difference"]) > mp.mpf("1e-125") for r in results),
        }
        if len(results) >= 2:
            checks["cross_run_cells_stable_within_tolerance"] = (
                mp.mpf(receipt["last_two_run_max_absolute_cell_change"]) < tolerance)
        receipt["checks"] = checks
        receipt["status"] = "PASS" if all(checks.values()) else "FAIL"
        args.output.write_text(json.dumps(receipt, indent=2) + "\n")
        assert all(checks.values()), checks
    print(json.dumps({key: val for key, val in receipt.items() if key != "runs"}, indent=2))


if __name__ == "__main__":
    main()
