# AI contribution and verification boundaries

## How this work was produced

This research artifact was developed through an iterative conversation between **Hanrui Yu** and an AI system accessed through **OpenAI Codex**.

Hanrui Yu proposed the scientific question about identification of latent-class random-effects models, specified the modeling constraints, requested an exact counterexample and formal verification, and supplied repeated questions, objections, and editorial direction.

The AI system produced the counterexample construction, mathematical argument, manuscript draft, Lean formalization, auxiliary checking programs, and publication packaging. Its contribution was substantive mathematical and implementation work, not merely language editing. Existing mathematical literature and the Lean/Mathlib libraries are essential prior work, not AI-created components.

This statement describes the workflow. It does not assert that Hanrui Yu independently checked every mathematical step or every line of code. No claim of independent human peer review is made.

## What was mechanically checked

The Lean project checks the core counterexample for the actual Gaussian-CDF conditional Bernoulli-product observation maps, including the positive-scale correction, strict admissibility, distinct parameter vectors, and equality of the observable cell probabilities. It also checks the embeddings into 2LCR1 and 2LCR and the four-indicator result.

The [verification receipt](formal_global/verification/receipt.json) records the compiler version, pinned Mathlib revision, source hashes, clean local-module build results, and axiom audits. The checker uses Lean's kernel with `--trust=0`. The recorded dependencies of the audited final declarations are `propext`, `Classical.choice`, and `Quot.sound`; no new mathematical axioms or `sorry` proofs are supplied by this project.

The Python verifier orchestrates compilation and records results. Its output is not an additional mathematical premise. The trusted computing base still includes Lean's kernel and foundational rules, the imported library as checked by Lean, and the software/hardware running the checker.

## What was not established by that check

- Lean verifies the encoded definitions and propositions; readers must still inspect that they express the intended statistical model.
- Not every sentence, interpretation, bibliographic claim, or sharper auxiliary numerical enclosure in the paper is formalized. The formal proof uses an inverse bound of 10^6; the sharper paper bound 122 is checked separately using exact rational arithmetic.
- The floating-point numerical diagnostics are not exact certificates or additional Lean theorems. Their precision and quadrature comparisons are empirical checks.
- The result is a global counterexample on a particular strictly admissible exchangeable submodel. It does not establish generic global nonidentification, settle six or more indicators, or prove generic local identification.
- Formal verification does not establish novelty, completeness of the literature review, statistical practical importance, or publication readiness. No claim of established bibliographic priority is made.

## Publication changes

The public package adds this disclosure, portable reproduction instructions and build support, and an AI-contribution paragraph in the paper. The mathematical Lean source files are unchanged from the previously verified construction. The numerical quadrature receipt's original machine-local input path is replaced by a repository-relative path for portability and privacy; its recorded numerical values are unchanged.

The repository contains only the research artifact and its verification material. Private conversation logs and unrelated local research files are not included. No reuse license has been selected; third-party dependencies retain their own licenses.
