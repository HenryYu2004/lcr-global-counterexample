import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

/-!
# The first five moments of the genuine Gaussian probability measure

This file connects Bochner integrals against `ProbabilityTheory.gaussianReal`
to their usual polynomial formulas. In particular, none of the moment
identities below is a definition of a polynomial called a moment.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LCR

lemma integrable_pow_gaussianReal (μ : ℝ) (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ => x^n) (gaussianReal μ v) := by
  exact integrable_pow_of_mem_interior_integrableExpSet (by simp) n

private noncomputable def E (μ v t : ℝ) : ℝ :=
  Real.exp (μ*t+v*t^2/2)

private lemma derivative_E (μ v t : ℝ) :
    HasDerivAt (E μ v) ((μ+v*t)*E μ v t) t := by
  unfold E
  convert (((hasDerivAt_id t).const_mul μ).add
    ((((hasDerivAt_id t).pow 2).const_mul v).div_const 2)).exp using 1
  dsimp
  ring

private lemma derivative_E1 (μ v t : ℝ) :
    HasDerivAt (fun t => (μ+v*t)*E μ v t)
      (((μ+v*t)^2+v)*E μ v t) t := by
  have ha := (hasDerivAt_const t μ).add ((hasDerivAt_id t).const_mul v)
  convert ha.mul (derivative_E μ v t) using 1
  dsimp
  ring

private lemma derivative_E2 (μ v t : ℝ) :
    HasDerivAt (fun t => ((μ+v*t)^2+v)*E μ v t)
      (((μ+v*t)^3+3*v*(μ+v*t))*E μ v t) t := by
  have ha := (hasDerivAt_const t μ).add ((hasDerivAt_id t).const_mul v)
  convert ((ha.pow 2).add (hasDerivAt_const t v)).mul
    (derivative_E μ v t) using 1
  dsimp
  ring

private lemma derivative_E3 (μ v t : ℝ) :
    HasDerivAt (fun t => ((μ+v*t)^3+3*v*(μ+v*t))*E μ v t)
      (((μ+v*t)^4+6*v*(μ+v*t)^2+3*v^2)*E μ v t) t := by
  have ha := (hasDerivAt_const t μ).add ((hasDerivAt_id t).const_mul v)
  convert ((ha.pow 3).add (ha.const_mul (3*v))).mul
    (derivative_E μ v t) using 1
  dsimp
  ring

private lemma derivative_E4 (μ v t : ℝ) :
    HasDerivAt
      (fun t => ((μ+v*t)^4+6*v*(μ+v*t)^2+3*v^2)*E μ v t)
      (((μ+v*t)^5+10*v*(μ+v*t)^3+15*v^2*(μ+v*t))*E μ v t) t := by
  have ha := (hasDerivAt_const t μ).add ((hasDerivAt_id t).const_mul v)
  convert (((ha.pow 4).add ((ha.pow 2).const_mul (6*v))).add
    (hasDerivAt_const t (3*v^2))).mul (derivative_E μ v t) using 1
  dsimp
  ring

private lemma iterated_E1 (μ v : ℝ) :
    iteratedDeriv 1 (E μ v) = fun t => (μ+v*t)*E μ v t := by
  funext t
  rw [iteratedDeriv_one]
  exact (derivative_E μ v t).deriv

private lemma iterated_E2 (μ v : ℝ) :
    iteratedDeriv 2 (E μ v) = fun t => ((μ+v*t)^2+v)*E μ v t := by
  rw [iteratedDeriv_succ, iterated_E1]
  funext t
  exact (derivative_E1 μ v t).deriv

private lemma iterated_E3 (μ v : ℝ) :
    iteratedDeriv 3 (E μ v) = fun t => ((μ+v*t)^3+3*v*(μ+v*t))*E μ v t := by
  rw [iteratedDeriv_succ, iterated_E2]
  funext t
  exact (derivative_E2 μ v t).deriv

private lemma iterated_E4 (μ v : ℝ) :
    iteratedDeriv 4 (E μ v) =
      fun t => ((μ+v*t)^4+6*v*(μ+v*t)^2+3*v^2)*E μ v t := by
  rw [iteratedDeriv_succ, iterated_E3]
  funext t
  exact (derivative_E3 μ v t).deriv

private lemma iterated_E5 (μ v : ℝ) :
    iteratedDeriv 5 (E μ v) =
      fun t => ((μ+v*t)^5+10*v*(μ+v*t)^3+15*v^2*(μ+v*t))*E μ v t := by
  rw [iteratedDeriv_succ, iterated_E4]
  funext t
  exact (derivative_E4 μ v t).deriv

private lemma moment_eq_derivative (μ : ℝ) (v : ℝ≥0) (n : ℕ) :
    (∫ x : ℝ, x^n ∂gaussianReal μ v) = iteratedDeriv n (E μ v) 0 := by
  have h := iteratedDeriv_mgf_zero
    (X := fun x : ℝ => x) (μ := gaussianReal μ v) (by simp) n
  rw [mgf_fun_id_gaussianReal] at h
  exact h.symm

theorem integral_pow_gaussianReal_0 (μ : ℝ) (v : ℝ≥0) :
    (∫ x : ℝ, x^0 ∂gaussianReal μ v) = 1 := by simp

theorem integral_pow_gaussianReal_1 (μ : ℝ) (v : ℝ≥0) :
    (∫ x : ℝ, x^1 ∂gaussianReal μ v) = μ := by simp

theorem integral_pow_gaussianReal_2 (μ : ℝ) (v : ℝ≥0) :
    (∫ x : ℝ, x^2 ∂gaussianReal μ v) = μ^2+v := by
  rw [moment_eq_derivative, iterated_E2]
  simp [E]

theorem integral_pow_gaussianReal_3 (μ : ℝ) (v : ℝ≥0) :
    (∫ x : ℝ, x^3 ∂gaussianReal μ v) = μ^3+3*μ*v := by
  rw [moment_eq_derivative, iterated_E3]
  simp [E]
  ring

theorem integral_pow_gaussianReal_4 (μ : ℝ) (v : ℝ≥0) :
    (∫ x : ℝ, x^4 ∂gaussianReal μ v) = μ^4+6*μ^2*v+3*(v:ℝ)^2 := by
  rw [moment_eq_derivative, iterated_E4]
  simp [E]
  ring

theorem integral_pow_gaussianReal_5 (μ : ℝ) (v : ℝ≥0) :
    (∫ x : ℝ, x^5 ∂gaussianReal μ v) = μ^5+10*μ^3*v+15*μ*(v:ℝ)^2 := by
  rw [moment_eq_derivative, iterated_E5]
  simp [E]
  ring

end LCR
