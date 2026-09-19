import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-!
Actual Gaussian-CDF observation model and the finite-moment-to-cell bridge.
There are no assumed identification, Gaussian moment, or contraction results.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LCR

noncomputable def standardGaussian : Measure ℝ := gaussianReal 0 1

/-- The actual standard Gaussian CDF, not an unspecified link function. -/
noncomputable def Phi (x : ℝ) : ℝ := cdf standardGaussian x

theorem Phi_nonneg (x : ℝ) : 0 ≤ Phi x := cdf_nonneg _ _
theorem Phi_le_one (x : ℝ) : Phi x ≤ 1 := cdf_le_one _ _
theorem measurable_Phi : Measurable Phi := (monotone_cdf _).measurable

instance standardGaussian_isProbability : IsProbabilityMeasure standardGaussian := by
  unfold standardGaussian
  infer_instance

structure ProbitParams where
  weight : ℝ
  alpha0 : ℝ
  alpha1 : ℝ
  beta0 : ℝ
  beta1 : ℝ

/-- Strict label and loading conventions used in the global counterexample. -/
def ProbitParams.Admissible (θ : ProbitParams) : Prop :=
  0 < θ.weight ∧ θ.weight < 1 ∧ θ.alpha0 < 0 ∧ 0 < θ.alpha1 ∧
  0 < θ.beta0 ∧ θ.beta0 < θ.beta1

noncomputable def componentMoment (a b : ℝ) (k : ℕ) : ℝ :=
  ∫ u, Phi (a + b * u) ^ k ∂standardGaussian

noncomputable def observedMoment (θ : ProbitParams) (k : ℕ) : ℝ :=
  (1 - θ.weight) * componentMoment θ.alpha0 θ.beta0 k +
    θ.weight * componentMoment θ.alpha1 θ.beta1 k

def successCount {n : ℕ} (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i => x i = true).card

theorem successCount_le {n : ℕ} (x : Fin n → Bool) : successCount x ≤ n := by
  simpa [successCount] using
    (Finset.card_filter_le (s := Finset.univ) (p := fun i => x i = true))

noncomputable def componentCell (a b : ℝ) (k m : ℕ) : ℝ :=
  ∫ u, Phi (a + b * u) ^ k * (1 - Phi (a + b * u)) ^ m ∂standardGaussian

/-- The integrated conditional-Bernoulli cell probability in the manuscript. -/
noncomputable def probitCell {n : ℕ} (θ : ProbitParams) (x : Fin n → Bool) : ℝ :=
  (1 - θ.weight) * componentCell θ.alpha0 θ.beta0 (successCount x) (n - successCount x) +
    θ.weight * componentCell θ.alpha1 θ.beta1 (successCount x) (n - successCount x)

theorem integrable_component_pow (a b : ℝ) (k : ℕ) :
    Integrable (fun u => Phi (a + b * u) ^ k) standardGaussian := by
  apply (integrable_const (1 : ℝ)).mono'
  · exact ((measurable_Phi.comp (by fun_prop)).pow_const k).aestronglyMeasurable
  · filter_upwards [] with u
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (Phi_nonneg _) _)]
    exact pow_le_one₀ (Phi_nonneg _) (Phi_le_one _)

theorem bernstein_expansion (q : ℝ) (k m : ℕ) :
    q ^ k * (1 - q) ^ m =
      ∑ j ∈ Finset.range (m + 1), ((-1 : ℝ) ^ j * (m.choose j : ℝ)) * q ^ (k + j) := by
  rw [show 1 - q = -q + 1 by ring, add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hneg : (-q) ^ j = (-1 : ℝ) ^ j * q ^ j := by
    rw [show -q = (-1 : ℝ) * q by ring, mul_pow]
  simp only [one_pow, mul_one, hneg, pow_add]
  ring

theorem componentCell_eq_moments (a b : ℝ) (k m : ℕ) :
    componentCell a b k m =
      ∑ j ∈ Finset.range (m + 1),
        ((-1 : ℝ) ^ j * (m.choose j : ℝ)) * componentMoment a b (k + j) := by
  unfold componentCell componentMoment
  simp_rw [bernstein_expansion]
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
  · intro j hj
    exact (integrable_component_pow a b (k + j)).const_mul _

theorem probitCell_eq_moments {n : ℕ} (θ : ProbitParams) (x : Fin n → Bool) :
    probitCell θ x =
      ∑ j ∈ Finset.range (n - successCount x + 1),
        ((-1 : ℝ) ^ j * ((n - successCount x).choose j : ℝ)) *
          observedMoment θ (successCount x + j) := by
  unfold probitCell
  rw [componentCell_eq_moments, componentCell_eq_moments]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  unfold observedMoment
  ring

/-- A genuine probability-integral bridge, valid for any number of indicators.
This is an intermediate implication; it does not assert that aliases exist. -/
theorem equal_moments_implies_equal_cells {n : ℕ} {θ η : ProbitParams}
    (hm : ∀ k ≤ n, observedMoment θ k = observedMoment η k) :
    ∀ x : Fin n → Bool, probitCell θ x = probitCell η x := by
  intro x
  rw [probitCell_eq_moments, probitCell_eq_moments]
  apply Finset.sum_congr rfl
  intro j hj
  have hx := successCount_le x
  have hj' := Finset.mem_range.mp hj
  rw [hm (successCount x + j) (by omega)]

theorem componentMoment_zero (a b : ℝ) : componentMoment a b 0 = 1 := by
  simp [componentMoment]

theorem observedMoment_zero (θ : ProbitParams) : observedMoment θ 0 = 1 := by
  simp [observedMoment, componentMoment_zero]

theorem equal_positive_moments_implies_equal_cells {n : ℕ} {θ η : ProbitParams}
    (hm : ∀ k, 1 ≤ k → k ≤ n → observedMoment θ k = observedMoment η k) :
    ∀ x : Fin n → Bool, probitCell θ x = probitCell η x := by
  apply equal_moments_implies_equal_cells
  intro k hk
  by_cases hzero : k = 0
  · subst k
    rw [observedMoment_zero, observedMoment_zero]
  · exact hm k (by omega) hk

end LCR
