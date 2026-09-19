import LCR.GaussianMixture
import LCR.ProbitTransform

/-!
# Transformed Gaussian moments and actual probit cell probabilities

The map `H` is defined by probability integrals. Its zero-scale value consists
of Gaussian moments. Equality at a nonnegative scale implies equality of
the actual thirty-two binary cell probabilities, by the exact CDF identity
and the binomial theorem. No identification premise is used here.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

noncomputable section
namespace LCR

def transformedComponentMoment (t μ v : ℝ) (k : ℕ) : ℝ :=
  ∫ u, hTransform t (μ + Real.sqrt v*u)^k ∂standardGaussian

def transformedMoment (t : ℝ) (θ : GaussianSpace) (k : ℕ) : ℝ :=
  (1-θ 0)*transformedComponentMoment t (θ 1) (θ 3) k +
    θ 0*transformedComponentMoment t (θ 2) (θ 4) k

def H (t : ℝ) (θ : GaussianSpace) : GaussianSpace :=
  fun i => transformedMoment t θ (i.val+1)

def probitFromGaussian (ε : ℝ) (θ : GaussianSpace) : ProbitParams where
  weight := θ 0
  alpha0 := ε*θ 1
  alpha1 := ε*θ 2
  beta0 := ε*Real.sqrt (θ 3)
  beta1 := ε*Real.sqrt (θ 4)

theorem transformedComponentMoment_zero_scale (μ v : ℝ) (k : ℕ) :
    transformedComponentMoment 0 μ v k = affineGaussianMoment μ v k := by
  simp only [transformedComponentMoment, hTransform_zero, affineGaussianMoment]

theorem transformedMoment_zero_scale (θ : GaussianSpace) (k : ℕ) :
    transformedMoment 0 θ k = gaussianMixtureMoment θ k := by
  simp only [transformedMoment, transformedComponentMoment_zero_scale, gaussianMixtureMoment]

theorem H_zero (θ : GaussianSpace) :
    H 0 θ = fun i => gaussianMixtureMoment θ (i.val+1) := by
  funext i
  exact transformedMoment_zero_scale θ (i.val+1)

theorem H_zero_gaussian_seeds : H 0 gaussianSeedA = H 0 gaussianSeedB := by
  rw [H_zero, H_zero]
  funext i
  apply gaussian_seeds_equal_moments
  have hi := i.isLt
  omega

theorem probitFromGaussian_admissible (ε : ℝ) (θ : GaussianSpace)
    (hε : 0 < ε) (hθ : GaussianAdmissible θ) :
    (probitFromGaussian ε θ).Admissible := by
  rcases hθ with ⟨hw0, hw1, hμ0, hμ1, hv0, hv01⟩
  change 0 < θ 0 ∧ θ 0 < 1 ∧ ε*θ 1 < 0 ∧ 0 < ε*θ 2 ∧
    0 < ε*Real.sqrt (θ 3) ∧ ε*Real.sqrt (θ 3) < ε*Real.sqrt (θ 4)
  exact ⟨hw0, hw1, mul_neg_of_pos_of_neg hε hμ0, mul_pos hε hμ1,
    mul_pos hε (Real.sqrt_pos.mpr hv0),
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt hv0.le hv01) hε⟩

theorem probitFromGaussian_ne_of_weight_ne (ε ε' : ℝ) (θ η : GaussianSpace)
    (hw : θ 0 ≠ η 0) : probitFromGaussian ε θ ≠ probitFromGaussian ε' η := by
  intro heq
  exact hw (congrArg ProbitParams.weight heq)

theorem transformedComponentMoment_zero (t μ v : ℝ) :
    transformedComponentMoment t μ v 0 = 1 := by
  simp [transformedComponentMoment]

theorem transformedMoment_zero (t : ℝ) (θ : GaussianSpace) :
    transformedMoment t θ 0 = 1 := by
  simp [transformedMoment, transformedComponentMoment_zero]

theorem integrable_transformed_affine_pow (t μ v : ℝ) (k : ℕ)
    (ht : 0 ≤ t) (hv : 0 ≤ v) :
    Integrable (fun u => hTransform t (μ+Real.sqrt v*u)^k) standardGaussian := by
  have hi := integrable_hTransform_pow μ ⟨v, hv⟩ k t ht
  rw [← map_affine_standardGaussian μ v hv] at hi
  exact (integrable_map_measure
    (((continuous_hTransform t).pow k).aestronglyMeasurable) (by fun_prop)).mp hi

def transformCoefficient (t : ℝ) (k j : ℕ) : ℝ :=
  (phi0*Real.sqrt t)^j * (1/2:ℝ)^(k-j) * (k.choose j:ℝ)

theorem Phi_power_eq_transformed_sum (t y : ℝ) (ht : 0 ≤ t) (k : ℕ) :
    Phi (Real.sqrt t*y)^k =
      ∑ j ∈ Finset.range (k+1), transformCoefficient t k j * hTransform t y^j := by
  rw [Phi_sqrt_mul_eq t y ht]
  have heq : (1/2:ℝ)+phi0*Real.sqrt t*hTransform t y =
      (phi0*Real.sqrt t)*hTransform t y+1/2 := by ring
  rw [heq, add_pow]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [transformCoefficient, mul_pow]
  ring

theorem componentMoment_eq_transformed_sum (t μ v : ℝ) (ht : 0 ≤ t)
    (hv : 0 ≤ v) (k : ℕ) :
    componentMoment (Real.sqrt t*μ) (Real.sqrt t*Real.sqrt v) k =
      ∑ j ∈ Finset.range (k+1),
        transformCoefficient t k j * transformedComponentMoment t μ v j := by
  unfold componentMoment transformedComponentMoment
  have heq : (fun u : ℝ => Phi (Real.sqrt t*μ+Real.sqrt t*Real.sqrt v*u)^k) =
      fun u => ∑ j ∈ Finset.range (k+1),
        transformCoefficient t k j * hTransform t (μ+Real.sqrt v*u)^j := by
    funext u
    rw [show Real.sqrt t*μ+Real.sqrt t*Real.sqrt v*u =
      Real.sqrt t*(μ+Real.sqrt v*u) by ring]
    exact Phi_power_eq_transformed_sum t (μ+Real.sqrt v*u) ht k
  rw [heq, integral_finsetSum]
  · simp only [integral_const_mul]
  · intro j hj
    exact (integrable_transformed_affine_pow t μ v j ht hv).const_mul _

theorem observedMoment_eq_transformed_sum (t : ℝ) (θ : GaussianSpace)
    (ht : 0 ≤ t) (hv0 : 0 ≤ θ 3) (hv1 : 0 ≤ θ 4) (k : ℕ) :
    observedMoment (probitFromGaussian (Real.sqrt t) θ) k =
      ∑ j ∈ Finset.range (k+1), transformCoefficient t k j * transformedMoment t θ j := by
  simp only [observedMoment, probitFromGaussian,
    componentMoment_eq_transformed_sum _ _ _ ht hv0,
    componentMoment_eq_transformed_sum _ _ _ ht hv1]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  unfold transformedMoment
  ring

theorem equal_transformedMoments_implies_equal_observedMoments
    (t : ℝ) (θ η : GaussianSpace) (ht : 0 ≤ t)
    (hvθ0 : 0 ≤ θ 3) (hvθ1 : 0 ≤ θ 4)
    (hvη0 : 0 ≤ η 3) (hvη1 : 0 ≤ η 4) (n : ℕ)
    (heq : ∀ k ≤ n, transformedMoment t θ k = transformedMoment t η k) :
    ∀ k ≤ n, observedMoment (probitFromGaussian (Real.sqrt t) θ) k =
      observedMoment (probitFromGaussian (Real.sqrt t) η) k := by
  intro k hk
  rw [observedMoment_eq_transformed_sum t θ ht hvθ0 hvθ1 k,
    observedMoment_eq_transformed_sum t η ht hvη0 hvη1 k]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [heq j (by omega)]

theorem equal_transformedMoments_implies_equal_probitCells
    (t : ℝ) (θ η : GaussianSpace) (ht : 0 ≤ t)
    (hvθ0 : 0 ≤ θ 3) (hvθ1 : 0 ≤ θ 4)
    (hvη0 : 0 ≤ η 3) (hvη1 : 0 ≤ η 4) (n : ℕ)
    (heq : ∀ k ≤ n, transformedMoment t θ k = transformedMoment t η k) :
    ∀ x : Fin n → Bool,
      probitCell (probitFromGaussian (Real.sqrt t) θ) x =
      probitCell (probitFromGaussian (Real.sqrt t) η) x := by
  apply equal_moments_implies_equal_cells
  exact equal_transformedMoments_implies_equal_observedMoments
    t θ η ht hvθ0 hvθ1 hvη0 hvη1 n heq

theorem equal_H_implies_equal_probitCells
    (t : ℝ) (θ η : GaussianSpace) (ht : 0 ≤ t)
    (hvθ0 : 0 ≤ θ 3) (hvθ1 : 0 ≤ θ 4)
    (hvη0 : 0 ≤ η 3) (hvη1 : 0 ≤ η 4)
    (heq : H t θ = H t η) :
    ∀ x : Fin 5 → Bool,
      probitCell (probitFromGaussian (Real.sqrt t) θ) x =
      probitCell (probitFromGaussian (Real.sqrt t) η) x := by
  apply equal_transformedMoments_implies_equal_probitCells t θ η ht
    hvθ0 hvθ1 hvη0 hvη1 5
  intro k hk
  by_cases hzero : k = 0
  · subst k
    rw [transformedMoment_zero, transformedMoment_zero]
  · have hi : k-1 < 5 := by omega
    have h := congrFun heq (⟨k-1, hi⟩ : Fin 5)
    have hk' : k-1+1 = k := by omega
    simpa only [H, hk'] using h

end LCR
