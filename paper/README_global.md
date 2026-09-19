# Reading and reproducing the research note

The [paper](global_counterexample.pdf) focuses on an exact counterexample to global identification. There is no generic local-identification theorem in this repository. See the [AI contribution statement](../AI_PROVENANCE.md) for how the work was produced.

## Reading guide

1. Theorem 1 states the precise global-identification claim that fails.
2. Section 2 explains why five moments determine the exchangeable five-indicator table.
3. Section 3 specifies two algebraic Gaussian-mixture starting points.
4. Section 4 defines the exact probit correction, proves convergence, and gives the final parameter pair.
5. Appendices A and B contain the polynomial calculations, rational certificates, and analytic bounds.

The algebraic starting point is `vartheta_B^0`; the final corrected Gaussian-mixture parameter is `vartheta_B^*`; the probit parameter is `theta_B^*`. The uncorrected seed is **not** asserted to be an exact alias at positive probit scale. The corrected point is defined by an infinite sequence, not by rounded decimals.

At epsilon = 10^(-20), the exact pair has identical probabilities for all 32 five-indicator patterns, different mixing weights, positive ordered loadings, and fixed class order. The proved maximum-norm error of the Gaussian-parameter iteration is at most `4 * 10^(-25) * 2^(-n)` after n iterations. Marginalization gives a four-indicator counterexample.

The example is exchangeable and extremely weak-signal, but strictly interior in the original parameter domain. It does not settle generic global identification with heterogeneous indicators, six-indicator identification, or identification under substantive lower bounds on discrimination. No elementary closed form or established novelty claim is asserted.

## Reproduce the PDF

From the repository root, with a standard TeX installation including `latexmk`:

```sh
cd paper
latexmk -pdf -interaction=nonstopmode -halt-on-error global_counterexample.tex
```

Alternatively, run `pdflatex -interaction=nonstopmode -halt-on-error global_counterexample.tex` twice from `paper/`.

## Exact rational certificate

From the repository root:

```sh
python3 auxiliary_exact_arithmetic/exact_interval_certificate.py
```

Only the Python standard library is required. Assertions use arbitrary-precision rational arithmetic; floating-point conversion is only for display. The certificate verifies the polynomial isolating interval, strict parameter bounds, a determinant in `(47,68)`, and an inverse infinity norm below 122. The optional `exact_gaussian_alias.py` illustration requires NumPy and is not used by this exact certificate.

## Separate numerical diagnostics

With `mpmath` installed (the recorded run used version 1.4.1), run from the repository root:

```sh
python3 numerical_checks/check_probit_counterexample.py
python3 numerical_checks/check_probit_quadrature.py numerical_checks/probit_numerical_check.json
```

These commands overwrite their corresponding diagnostic JSON files, not the paper or Lean sources.

The first script recomputes the algebraic seed and fixed-Jacobian correction at 200 and 280 decimal digits, using stable transformed moments and a separate analytic series-truncation bound. That bound does not include floating-point roundoff; precision/truncation reruns check stability.

The second script independently integrates the original Gaussian-CDF cell products using composite Gauss-Legendre quadrature at 220 and 260 decimal digits with increased quadrature order. The recorded runs pass an absolute paired-cell difference tolerance of `1e-200`. The higher-precision run reports a corrected paired gap of approximately `1.08e-263`, while the uncorrected seed has a detected gap of approximately `2.17332e-121`.

These are numerical diagnostics, not exact certificates or Lean theorems. The omitted normal tail has an explicit bound, but finite quadrature error is assessed empirically by increased precision and order. Full-precision parameters are retained in the JSON files; rounded displays must not be treated as the exact pair. The published quadrature receipt has only its original local input-path metadata sanitized.

## Formal proof

The [formalization guide](../formal_global/README.md) gives the theorem names, dependency pins, clean-build commands, and precise verification boundary. The final theorem concerns the actual Gaussian-integral counterexample, including the positive-scale correction and equality of all binary cells. The numerical diagnostics are not assumptions supplied to Lean.

The core theorem is formalized end to end; the claim does not extend to every auxiliary enclosure or sentence of the paper. In particular, Lean independently proves a sufficient inverse bound of 10^6, rather than the sharper rational-certificate bound 122.
