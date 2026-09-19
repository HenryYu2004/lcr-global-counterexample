# Exact global nonidentification: a completed Lean formalization

## Result

The core global counterexample is verified end to end in Lean 4.30.0 with
Mathlib. This is no longer just a polynomial certificate or a conditional
application of an implicit-function or fixed-point theorem.

The final declarations in `LCR/Main.lean` have **no analytic or
identification hypotheses**:

```lean
LCR.global_probit_counterexample : LCR.GlobalProbitCounterexample
LCR.not_injective_2LCR1_five
LCR.not_injective_2LCR_five
LCR.not_injective_2LCR1_four
LCR.not_injective_2LCR_four
```

The last four explicitly assert noninjectivity on the strictly restricted
parameter domains of the full, finite-product observation models.

For five indicators, the proof constructs two different parameter vectors
with

\[
0<\pi<1,\qquad \alpha_0<0<\alpha_1,\qquad 0<\beta_0<\beta_1,
\]

and proves exact equality of all 32 observable cell probabilities. The same
pair works for four indicators. The full-model embedding also proves that
these are counterexamples for both 2LCR1 and 2LCR; it does not silently
redefine 2LCR1 to require equal intercepts.

## What the exact construction means

1. `AlgebraicSeed.pStar` is the unique root of the stated integer polynomial
   in `(634/1000, 635/1000)`. Both existence and uniqueness are proved.
2. The Gaussian seeds are the rational vector `(1/2,-1,1,1,2)` and the
   reconstructed algebraic vector. Their first five **actual Gaussian
   integral moments** are equal.
3. `Phi` is Mathlib's CDF of `gaussianReal 0 1`, not a function satisfying
   postulated Gaussian identities. `H` is the actual integral map built from
   `hTransform t y = integral (u=0..y) exp(-t*u^2/2)`.
4. At the fixed positive time `t = 10^(-40)`, the exact iteration is
   `x ↦ x - J0^(-1) (H t x - H t seedA)`. Genuine integral differentiation,
   a verified inverse bound, and quantitative Jacobian stability prove that
   it is a contraction on the specified maximum-norm ball.
5. `correctedGaussianSeed` is the resulting unique solution in that ball.
   It is not the rounded algebraic seed. Its exact equation, convergence,
   displacement, and iteration error are all proved:

   \[
   H(10^{-40},B^*)=H(10^{-40},A),\qquad
   \|T^n(B^0)-B^*\|_\infty\le4\cdot10^{-25}2^{-n}.
   \]

6. `exactThetaA` and `exactThetaB` use the fixed scale `10^(-20)`.
   Admissibility, distinctness, the second weight interval `(.69,.72)`,
   and equality of every observable cell are proved. Their definitions are
   exact classical real objects; the formalization is not claiming to
   provide a floating-point evaluation of them.

## Proof map

| Part | Main files |
| --- | --- |
| Real algebraic root, reconstruction, exact moments | `AlgebraicSeed`, `SeedUniqueness`, `GaussianMoments`, `GaussianMixture` |
| Actual Gaussian CDF and binary observation integrals | `ProbitModel`, `ProbitTransform`, `TransformedMoments` |
| Genuine integral differentiation and domination | `TransformBounds`, `GaussianEnvelope`, `ComponentDifferentiation`, `HDerivative` |
| Quantitative derivative and initial-error bounds | `PowerBounds`, `JacobianStability`, `InitialResidual` |
| Actual polynomial derivative, determinant and inverse | `PolynomialDerivative`, `GaussianJacobian`, `JacobianInverse` |
| Contraction, exact limit and strict parameter margins | `CertifiedCorrection`, `CorrectionAssembly`, `SeedNeighborhood`, `SeedWeight` |
| Four/five indicators and unrestricted-model inclusion | `IndicatorReduction`, `FullModelEmbedding` |
| Unconditional final result | `Main` |

`CertifiedCorrection` and `CorrectionAssembly` are deliberately reusable,
conditional intermediate theorems. **`Main` discharges their conditions**
for the concrete probability integrals. Reading an intermediate theorem
alone is not a substitute for checking the final theorem.

## Reproduction

Pinned versions:

- Lean: `leanprover/lean4:v4.30.0`.
- Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

From the repository root, on a machine with Python 3, Git, and Lean's
[`elan`/`lake`](https://github.com/leanprover/elan#installation) installed:

```sh
cd formal_global
lake update
lake exe cache get
python3 verify.py
```

`lean-toolchain` and `lakefile.toml` pin the versions above. The scripts use
this project's `.lake/packages` by default and resolve the compiler through
elan (falling back to `lean` on `PATH`). No author-specific absolute path is
required. To develop interactively, `lake build` is also available; the clean
audit above is the release verification command.

The [GitHub Actions workflow](../.github/workflows/lean.yml) performs the same
dependency setup and audit on Ubuntu, using a read-only repository token.
Its configured existence is not a claim that an Actions run has passed: check
the run for the particular commit. The bundled local verification receipt
was produced using an existing clean cache at the pinned revision. A full
fresh dependency download has not been exercised in the local release setup.

To reuse an existing Lake project's dependency cache without modifying it,
the optional overrides are:

```sh
python3 verify.py --mathlib-project /absolute/path/to/cached/project \
  --lean /absolute/path/to/lean-4.30.0/bin/lean
```

The verification script discovers the final theorem's local import graph and
rebuilds every reachable project module into a **fresh temporary build
directory**, so old project `.olean` files cannot conceal stale proofs.
It records the compiler version, Mathlib revision, every source SHA-256,
individual build results, and final theorem axiom dependencies in
`verification/receipt.json`; compiler output is in `verification/build.log`.
The receipt also records the verification-script and configuration hashes.
A run replaces the previous receipt with `IN_PROGRESS` before checking
dependencies and writes `PASS` only after all checks succeed. The receipt is
an audit record, not a cryptographic attestation or a substitute for rebuilding.

The final dependency audits report only:

```text
propext, Classical.choice, Quot.sound
```

There is no `sorryAx`, added mathematical axiom, or `native_decide` in the
project proof. The Python scripts orchestrate builds and record results;
they do not supply mathematical facts to the Lean theorems. As usual, the
trusted base includes Lean's logical foundation and kernel and the
implementation/runtime/hardware used to check it. Mathlib supplies existing
definitions and theorems; compilation uses `--trust=0`, including kernel
checking of imported modules. Dependencies are downloaded as cached build
artifacts; this workflow does not rebuild all of Mathlib from source.

After a passing audit, an optional self-contained source-and-paper archive
(without downloaded dependencies) can be produced from the repository root:

```sh
python3 formal_global/make_bundle.py
```

It writes `dist/global_counterexample_lean_verified.zip`, checks the audited
source hashes again, and reads only files in this repository. An alternative
archive destination can be passed with `--output`.

## Precise verification boundary

The **core counterexample theorem and its positive-scale construction are
fully formalized**. This is not the claim that every sentence, bibliographic
statement, or sharper auxiliary bound in the PDF is formalized.

In particular:

- The sufficient bound `||J0^(-1)|| ≤ 10^6` is proved in Lean. The paper's
  sharper `<122` and finer table enclosures retain their separate exact
  rational-arithmetic certificates; they are not premises of the final
  Lean proof.
- The formal Jacobian variation argument uses direct pointwise differences
  and integrable envelopes. It need not formalize every displayed Hessian
  estimate in the paper to prove the same quantitative contraction.
- The integral formulas are the actual Gaussian-CDF Bernoulli-product
  observation formulas. Standalone normalization/nonnegativity theorems for
  the full cell vector, and the interpretive statement about class-specific
  marginal success probabilities, are not additional advertised results.
- This is a counterexample to injectivity on the whole admissible domain.
  It does **not** prove generic global nonidentification under heterogeneous
  indicators, an alias for six indicators, or a priority claim in the
  literature.

The separate rational Python checks are in `../auxiliary_exact_arithmetic/`.
They are not premises of the Lean proof. This project includes the real-analysis
and probability formalization needed for the final counterexample.

## Separate numerical diagnostics (20 September 2026)

The optional decimal parameter table and numerical-check discussion have been
removed from the manuscript at the author's request. The exact parameter
definitions and proof are unchanged. Rounded decimal displays are not an
exact alias and are not suitable inputs for reproducing high-precision equality.

The full bundle additionally includes `numerical_checks/`. Its first script
computes the corrected Gaussian-mixture parameters with arbitrary precision
and checks all 32 patterns through the transformed moments. Its second
script independently evaluates the original Gaussian-CDF product integrals
by quadrature. Full-precision parameter data and diagnostic outputs are saved
in JSON files. The uncorrected Gaussian seed is tested as a sensitivity
control, since its probit cell probabilities are not exactly equal.

These floating-point diagnostics are not Lean-verified assertions or
substitutes for the exact counterexample theorem. Their precision and
quadrature convergence checks are recorded separately. The formal sources
and their audited hashes are unchanged by this numerical supplement.
