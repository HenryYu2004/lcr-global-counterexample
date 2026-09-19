import LCR.GaussianMoments
import LCR.ProbitModel
import LCR.AlgebraicSeed

/-! The real-algebraic aliases are aliases of genuine Gaussian integrals.
This does not yet claim that they are probit aliases at positive scale. -/

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section
namespace LCR

/-- Coordinates: mixing weight, two means, and two variances. -/
abbrev GaussianSpace := Fin 5 → ℝ

def gaussianSeedA : GaussianSpace := ![1/2, -1, 1, 1, 2]

def gaussianSeedB : GaussianSpace :=
  ![AlgebraicSeed.piOf AlgebraicSeed.pStar,
    AlgebraicSeed.mu0Of AlgebraicSeed.pStar,
    AlgebraicSeed.mu1Of AlgebraicSeed.pStar,
    AlgebraicSeed.variance0Of AlgebraicSeed.pStar,
    AlgebraicSeed.variance1Of AlgebraicSeed.pStar]

def affineGaussianMoment (μ v : ℝ) (k : ℕ) : ℝ :=
  ∫ u, (μ + Real.sqrt v * u)^k ∂standardGaussian

def gaussianMixtureMoment (θ : GaussianSpace) (k : ℕ) : ℝ :=
  (1-θ 0)*affineGaussianMoment (θ 1) (θ 3) k +
    θ 0*affineGaussianMoment (θ 2) (θ 4) k

theorem map_affine_standardGaussian (μ v : ℝ) (hv : 0 ≤ v) :
    standardGaussian.map (fun u => μ + Real.sqrt v * u) = gaussianReal μ ⟨v, hv⟩ := by
  unfold standardGaussian
  have hs : (NNReal.mk ((Real.sqrt v)^2) (sq_nonneg (Real.sqrt v))) = ⟨v, hv⟩ := by
    apply Subtype.ext
    exact Real.sq_sqrt hv
  have hcomp : (fun u : ℝ => μ + Real.sqrt v * u) =
      (fun y : ℝ => μ+y) ∘ (fun u : ℝ => Real.sqrt v*u) := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
    gaussianReal_map_const_mul, mul_zero, mul_one, hs, gaussianReal_map_const_add, zero_add]

theorem affineGaussianMoment_eq (μ v : ℝ) (hv : 0 ≤ v) (k : ℕ) :
    affineGaussianMoment μ v k = ∫ x, x^k ∂gaussianReal μ ⟨v, hv⟩ := by
  rw [← map_affine_standardGaussian μ v hv,
    integral_map (by fun_prop) (by fun_prop)]
  rfl

theorem integrable_affineGaussian_pow (μ v : ℝ) (hv : 0 ≤ v) (k : ℕ) :
    Integrable (fun u => (μ + Real.sqrt v*u)^k) standardGaussian := by
  have h := integrable_pow_gaussianReal μ ⟨v, hv⟩ k
  rw [← map_affine_standardGaussian μ v hv] at h
  exact (integrable_map_measure (g := fun x : ℝ => x^k)
    (by fun_prop) (by fun_prop)).mp h

theorem affineGaussianMoment_polynomial (μ v : ℝ) (hv : 0 ≤ v) (k : ℕ) (hk : k ≤ 5) :
    affineGaussianMoment μ v k = AlgebraicSeed.normalMomentPolynomial μ v k := by
  rw [affineGaussianMoment_eq μ v hv]
  interval_cases k <;>
    simp only [AlgebraicSeed.normalMomentPolynomial,
      integral_pow_gaussianReal_0, integral_pow_gaussianReal_1,
      integral_pow_gaussianReal_2, integral_pow_gaussianReal_3,
      integral_pow_gaussianReal_4, integral_pow_gaussianReal_5] <;> rfl

theorem gaussianMixtureMoment_polynomial (θ : GaussianSpace)
    (hv0 : 0 ≤ θ 3) (hv1 : 0 ≤ θ 4) (k : ℕ) (hk : k ≤ 5) :
    gaussianMixtureMoment θ k =
      AlgebraicSeed.mixtureMomentPolynomial (θ 0) (θ 1) (θ 2) (θ 3) (θ 4) k := by
  simp only [gaussianMixtureMoment, AlgebraicSeed.mixtureMomentPolynomial,
    affineGaussianMoment_polynomial _ _ hv0 k hk,
    affineGaussianMoment_polynomial _ _ hv1 k hk]

theorem gaussianSeedB_variances_pos : 0 < gaussianSeedB 3 ∧ 0 < gaussianSeedB 4 := by
  have h := AlgebraicSeed.seed_admissible
  change 0 < AlgebraicSeed.variance0Of AlgebraicSeed.pStar ∧
    0 < AlgebraicSeed.variance1Of AlgebraicSeed.pStar
  constructor <;> linarith [h.2.2.1.1, h.2.2.2.1]

theorem gaussian_seeds_ne : gaussianSeedA ≠ gaussianSeedB := by
  intro heq
  have hw := congrFun heq 0
  have h := AlgebraicSeed.seed_admissible.1.1
  change (1/2 : ℝ) = AlgebraicSeed.piOf AlgebraicSeed.pStar at hw
  linarith

theorem gaussianMixtureMoment_zero (θ : GaussianSpace) : gaussianMixtureMoment θ 0 = 1 := by
  simp [gaussianMixtureMoment, affineGaussianMoment]

/-- Exact equality of five genuine integrals, not numerical moment matching. -/
theorem gaussian_seeds_equal_moments (k : ℕ) (hk : k ≤ 5) :
    gaussianMixtureMoment gaussianSeedA k = gaussianMixtureMoment gaussianSeedB k := by
  have hvA0 : 0 ≤ gaussianSeedA 3 := by change (0 : ℝ) ≤ 1; norm_num
  have hvA1 : 0 ≤ gaussianSeedA 4 := by change (0 : ℝ) ≤ 2; norm_num
  rw [gaussianMixtureMoment_polynomial gaussianSeedA hvA0 hvA1 k hk,
    gaussianMixtureMoment_polynomial gaussianSeedB
      gaussianSeedB_variances_pos.1.le gaussianSeedB_variances_pos.2.le k hk]
  obtain ⟨h1,h2,h3,h4,h5⟩ := AlgebraicSeed.algebraic_seed_moments
  obtain ⟨g1,g2,g3,g4,g5⟩ := AlgebraicSeed.rational_seed_moments
  change AlgebraicSeed.mixtureMomentPolynomial (1/2) (-1) 1 1 2 k =
    AlgebraicSeed.mixtureMomentPolynomial (AlgebraicSeed.piOf AlgebraicSeed.pStar)
      (AlgebraicSeed.mu0Of AlgebraicSeed.pStar) (AlgebraicSeed.mu1Of AlgebraicSeed.pStar)
      (AlgebraicSeed.variance0Of AlgebraicSeed.pStar) (AlgebraicSeed.variance1Of AlgebraicSeed.pStar) k
  interval_cases k
  · simp [AlgebraicSeed.mixtureMomentPolynomial, AlgebraicSeed.normalMomentPolynomial]
  · exact g1.trans h1.symm
  · exact g2.trans h2.symm
  · exact g3.trans h3.symm
  · exact g4.trans h4.symm
  · exact g5.trans h5.symm

def GaussianAdmissible (θ : GaussianSpace) : Prop :=
  0 < θ 0 ∧ θ 0 < 1 ∧ θ 1 < 0 ∧ 0 < θ 2 ∧ 0 < θ 3 ∧ θ 3 < θ 4

theorem gaussianSeedA_admissible : GaussianAdmissible gaussianSeedA := by
  change (0 : ℝ) < 1/2 ∧ (1/2 : ℝ) < 1 ∧ (-1 : ℝ) < 0 ∧
    (0 : ℝ) < 1 ∧ (0 : ℝ) < 1 ∧ (1 : ℝ) < 2
  norm_num

theorem gaussianSeedB_admissible : GaussianAdmissible gaussianSeedB := by
  have ha := AlgebraicSeed.seed_admissible
  have hc := (AlgebraicSeed.cOf_bounds AlgebraicSeed.pStar_spec.1
    AlgebraicSeed.pStar_spec.2.1).1
  have hvar : AlgebraicSeed.variance0Of AlgebraicSeed.pStar <
      AlgebraicSeed.variance1Of AlgebraicSeed.pStar := by
    unfold AlgebraicSeed.variance0Of AlgebraicSeed.variance1Of
    have hmean : AlgebraicSeed.mu0Of AlgebraicSeed.pStar <
        AlgebraicSeed.mu1Of AlgebraicSeed.pStar := by linarith [ha.2.1.1, ha.2.1.2]
    have hp := mul_lt_mul_of_pos_left hmean (show 0 < AlgebraicSeed.cOf AlgebraicSeed.pStar by linarith)
    linarith
  change 0 < AlgebraicSeed.piOf AlgebraicSeed.pStar ∧
    AlgebraicSeed.piOf AlgebraicSeed.pStar < 1 ∧
    AlgebraicSeed.mu0Of AlgebraicSeed.pStar < 0 ∧
    0 < AlgebraicSeed.mu1Of AlgebraicSeed.pStar ∧
    0 < AlgebraicSeed.variance0Of AlgebraicSeed.pStar ∧
    AlgebraicSeed.variance0Of AlgebraicSeed.pStar < AlgebraicSeed.variance1Of AlgebraicSeed.pStar
  exact ⟨by linarith [ha.1.1], by linarith [ha.1.2], ha.2.1.1, ha.2.1.2,
    by linarith [ha.2.2.1.1], hvar⟩

/-- A completed zero-scale result.  Probit aliases at positive scale require
the additional, separately verified analytic correction step. -/
theorem exists_distinct_admissible_gaussian_five_moment_pair :
    ∃ θ η : GaussianSpace, GaussianAdmissible θ ∧ GaussianAdmissible η ∧
      θ ≠ η ∧ ∀ k ≤ 5, gaussianMixtureMoment θ k = gaussianMixtureMoment η k := by
  exact ⟨gaussianSeedA, gaussianSeedB, gaussianSeedA_admissible,
    gaussianSeedB_admissible, gaussian_seeds_ne, gaussian_seeds_equal_moments⟩

end LCR
