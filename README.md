# An exact global-identification counterexample for 2LCR

An English research note and a Lean 4/Mathlib proof of an exact counterexample to global identification in a two-class probit-normal random-effects model, with four or five binary indicators.

**AI contribution:** the counterexample construction, mathematical proof, manuscript draft, and Lean formalization were produced by an AI system through OpenAI Codex. Hanrui Yu supplied the research questions, constraints, and iterative critical feedback. This was substantive AI mathematical work, not merely language editing. See [AI contribution and verification boundaries](AI_PROVENANCE.md).

## Start here

- [Read the paper (PDF)](paper/global_counterexample.pdf), its [LaTeX source](paper/global_counterexample.tex), and the [reading guide](paper/README_global.md).
- [Read the formalization guide](formal_global/README.md) and the [final Lean theorems](formal_global/LCR/Main.lean).
- Inspect the [recorded local verification receipt](formal_global/verification/receipt.json) and [compiler log](formal_global/verification/build.log). The receipt identifies the checked source hashes; it is not itself a substitute for rerunning Lean.

## What is proved

For five binary indicators, two distinct parameter vectors induce **exactly the same 32 joint cell probabilities**. Their mixing weights differ: one is 1/2 and the other lies strictly between 0.69 and 0.72. Both satisfy the strict restrictions

$$0<\pi<1,\qquad \alpha_0<0<\alpha_1,\qquad 0<\beta_0<\beta_1.$$

These restrictions also fix the relevant label/sign ambiguities. They are stronger than mere conventions; they are not assumed to be without loss of generality for every model parameter.

The pair lies in the exchangeable submodel with identical intercepts and loadings across indicators within each class. An injective embedding makes it a counterexample for both **2LCR1** (class-specific common loadings, potentially heterogeneous intercepts) and **2LCR** (potentially heterogeneous intercepts and loadings). Marginalization gives the four-indicator result.

The construction is exact: an isolated algebraic root specifies a Gaussian-mixture seed, then a proved contraction defines the corrected parameter as a convergent-sequence limit. Rounded decimal parameters and floating-point agreement are not the proof.

The unconditional final declarations are:

```lean
LCR.global_probit_counterexample
LCR.not_injective_2LCR1_five
LCR.not_injective_2LCR_five
LCR.not_injective_2LCR1_four
LCR.not_injective_2LCR_four
```

## What is not claimed

The example is exchangeable and very weak-signal, with a strictly positive scale of 10^(-20). It disproves injectivity on the whole stated parameter domain. It does **not** settle generic global identification under indicator heterogeneity, identification for six or more indicators, or identification with substantive lower bounds on discrimination. This repository does not prove a generic local-identification theorem.

The core counterexample is formalized, but not every sentence or auxiliary bound in the paper is. In particular, Lean proves the sufficient inverse-Jacobian bound 10^6; the sharper bound 122 has a separate exact rational-arithmetic certificate. Formal verification does not establish bibliographic novelty or constitute peer review.

## Reproduce the verification

Install Lean's `elan` toolchain manager and Python 3, then run from the repository root:

```sh
cd formal_global
lake update
lake exe cache get
python3 verify.py
```

The project pins Lean **4.30.0** and Mathlib commit **c5ea00351c28e24afc9f0f84379aa41082b1188f**. The verifier rebuilds the local proof modules in a fresh directory with `--trust=0`, checks source hashes, and audits the final theorem dependencies. See the [formalization guide](formal_global/README.md) for cached-dependency options and the distinction between the recorded local run and a fresh-machine build.

The expected axiom dependencies are only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. The project contains no `sorry`, added mathematical axiom, or `native_decide` proof.

Optional exact rational checks use only the Python standard library:

```sh
python3 auxiliary_exact_arithmetic/exact_interval_certificate.py
```

Separate [high-precision numerical diagnostics](numerical_checks/) require `mpmath`; see the [reading guide](paper/README_global.md). They are not premises of the Lean proof.

## Repository contents

| Directory | Purpose |
| --- | --- |
| `paper/` | English manuscript, PDF, and reading/reproduction guide |
| `formal_global/` | Lean source, pinned dependencies, verifier, and recorded audit |
| `auxiliary_exact_arithmetic/` | Exact rational certificate and optional numerical Gaussian-seed illustration |
| `numerical_checks/` | Independent floating-point diagnostics and their recorded outputs |

No reuse license has been selected for this repository. Public availability alone should not be interpreted as an open-source license; third-party dependencies retain their own licenses.
