The paper is in paper/. The completed Lean proof, reproducibility guide,
clean-build log and axiom-audit receipt are in formal_global/.
Start with README.md and formal_global/LCR/Main.lean.
The auxiliary exact-arithmetic Python checks are not trusted premises
of the final Lean theorems. numerical_checks/ contains separate
high-precision diagnostics, not formal certificates. Mathlib binaries
are not bundled. See AI_PROVENANCE.md for the AI contribution statement.
