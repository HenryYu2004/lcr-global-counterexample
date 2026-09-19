import LCR.TransformedMoments
import LCR.TransformBounds
import LCR.GaussianEnvelope
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Quantitative initial residual for genuine transformed Gaussian moments

Every integral and time derivative in this file is the actual one defined
in the observation model. The pointwise estimate is proved by the mean
value theorem, not supplied as an assumption about the moment map.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

noncomputable section
namespace LCR

theorem abs_hTransform_sub_self_le (t y : ℝ) (ht : 0 ≤ t) :
    |hTransform t y-y| ≤ t*|y|^3/6 := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := (0 : ℝ)) (b := t) (f := fun s => hTransform s y)
    (f' := fun s => hTransformTime s y) (C := |y|^3/6)
    (fun s hs => (hasDerivAt_hTransform_time s y).hasDerivWithinAt)
    (fun s hs => by
      simpa only [Real.norm_eq_abs] using abs_hTransformTime_le s y hs.1)
    t ⟨ht, le_rfl⟩
  simp only [Real.norm_eq_abs, hTransform_zero, sub_zero] at h
  nlinarith

theorem abs_time_derivative_transform_power_le (s y L : ℝ)
    (hs : 0 ≤ s) (hL : 1 ≤ L) (hy : |y| ≤ L) (k : ℕ) (hk : k ≤ 5) :
    |(k:ℝ)*hTransform s y^(k-1)*hTransformTime s y| ≤ L^7 := by
  have hLn : 0 ≤ L := by linarith
  have hkR : (k:ℝ) ≤ 5 := by exact_mod_cast hk
  have hh : |hTransform s y| ≤ L := (abs_hTransform_le s y hs).trans hy
  have hd : |hTransformTime s y| ≤ L^3/6 := by
    calc
      _ ≤ |y|^3/6 := abs_hTransformTime_le s y hs
      _ ≤ L^3/6 := by gcongr
  calc
    _ = (k:ℝ)*|hTransform s y|^(k-1)*|hTransformTime s y| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg k), abs_pow]
    _ ≤ 5*L^(k-1)*(L^3/6) := by gcongr
    _ = (5/6:ℝ)*L^((k-1)+3) := by rw [pow_add]; ring
    _ ≤ (5/6:ℝ)*L^7 := by
      apply mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by omega))
      norm_num
    _ ≤ L^7 := by nlinarith [pow_nonneg hLn 7]

theorem abs_transform_power_sub_power_le (t y L : ℝ)
    (ht : 0 ≤ t) (hL : 1 ≤ L) (hy : |y| ≤ L) (k : ℕ) (hk : k ≤ 5) :
    |hTransform t y^k-y^k| ≤ t*L^7 := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := (0 : ℝ)) (b := t) (f := fun s => hTransform s y^k)
    (f' := fun s => (k:ℝ)*hTransform s y^(k-1)*hTransformTime s y)
    (C := L^7)
    (fun s hs => ((hasDerivAt_hTransform_time s y).pow k).hasDerivWithinAt)
    (fun s hs => by
      simpa only [Real.norm_eq_abs] using
        abs_time_derivative_transform_power_le s y L hs.1 hL hy k hk)
    t ⟨ht, le_rfl⟩
  simpa only [Real.norm_eq_abs, hTransform_zero, sub_zero, mul_comm] using h

/-- Closed rectangle used for the quantitative analytic estimates. -/
structure PaperBox (θ : GaussianSpace) : Prop where
  weight_mem : θ 0 ∈ Icc (1/4) (3/4)
  mean0_abs : |θ 1| ≤ 2
  mean1_abs : |θ 2| ≤ 2
  variance0_mem : θ 3 ∈ Icc (1/2) 3
  variance1_mem : θ 4 ∈ Icc (1/2) 3

theorem component_initial_residual_le (t μ v : ℝ)
    (ht : 0 ≤ t) (hμ : |μ| ≤ 2) (hv0 : 0 ≤ v) (hv3 : v ≤ 3)
    (k : ℕ) (hk : k ≤ 5) :
    |transformedComponentMoment t μ v k-affineGaussianMoment μ v k| ≤ 876544*t := by
  have hi := integrable_transformed_affine_pow t μ v k ht hv0
  have hg := integrable_affineGaussian_pow μ v hv0 k
  unfold transformedComponentMoment affineGaussianMoment
  rw [← integral_sub hi hg]
  calc
    _ ≤ ∫ u, |hTransform t (μ+Real.sqrt v*u)^k-(μ+Real.sqrt v*u)^k|
          ∂standardGaussian := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun u => hTransform t (μ+Real.sqrt v*u)^k-(μ+Real.sqrt v*u)^k)
    _ ≤ ∫ u, t*gaussianEnvelope u^7 ∂standardGaussian := by
      apply integral_mono_ae (hi.sub hg).norm (integrable_gaussianEnvelope_seven.const_mul t)
      filter_upwards [] with u
      exact abs_transform_power_sub_power_le t (μ+Real.sqrt v*u) (gaussianEnvelope u)
        ht (by linarith [gaussianEnvelope_ge_two u])
        (abs_affineGaussian_le_envelope μ v u hμ hv3) k hk
    _ = t*(∫ u, gaussianEnvelope u^7 ∂standardGaussian) := integral_const_mul t _
    _ ≤ 876544*t := by
      have h := mul_le_mul_of_nonneg_left integral_gaussianEnvelope_seven_le ht
      nlinarith

theorem transformedMoment_initial_residual_sharp (t : ℝ) (θ : GaussianSpace)
    (ht : 0 ≤ t) (hθ : PaperBox θ) (k : ℕ) (hk : k ≤ 5) :
    |transformedMoment t θ k-gaussianMixtureMoment θ k| ≤ 876544*t := by
  have hv0 : 0 ≤ θ 3 := by linarith [hθ.variance0_mem.1]
  have hv1 : 0 ≤ θ 4 := by linarith [hθ.variance1_mem.1]
  have hw0 : 0 ≤ θ 0 := by linarith [hθ.weight_mem.1]
  have hw1 : 0 ≤ 1-θ 0 := by linarith [hθ.weight_mem.2]
  have h0 := component_initial_residual_le t (θ 1) (θ 3) ht hθ.mean0_abs hv0
    hθ.variance0_mem.2 k hk
  have h1 := component_initial_residual_le t (θ 2) (θ 4) ht hθ.mean1_abs hv1
    hθ.variance1_mem.2 k hk
  have heq : transformedMoment t θ k-gaussianMixtureMoment θ k =
      (1-θ 0)*(transformedComponentMoment t (θ 1) (θ 3) k-affineGaussianMoment (θ 1) (θ 3) k)+
      θ 0*(transformedComponentMoment t (θ 2) (θ 4) k-affineGaussianMoment (θ 2) (θ 4) k) := by
    unfold transformedMoment gaussianMixtureMoment
    ring
  rw [heq]
  calc
    _ ≤ |(1-θ 0)*(transformedComponentMoment t (θ 1) (θ 3) k-
          affineGaussianMoment (θ 1) (θ 3) k)| +
        |θ 0*(transformedComponentMoment t (θ 2) (θ 4) k-
          affineGaussianMoment (θ 2) (θ 4) k)| := abs_add_le _ _
    _ = (1-θ 0)*|transformedComponentMoment t (θ 1) (θ 3) k-
          affineGaussianMoment (θ 1) (θ 3) k| +
        θ 0*|transformedComponentMoment t (θ 2) (θ 4) k-
          affineGaussianMoment (θ 2) (θ 4) k| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hw1, abs_of_nonneg hw0]
    _ ≤ (1-θ 0)*(876544*t)+θ 0*(876544*t) :=
      add_le_add (mul_le_mul_of_nonneg_left h0 hw1) (mul_le_mul_of_nonneg_left h1 hw0)
    _ = 876544*t := by ring

theorem transformedMoment_initial_residual_le (t : ℝ) (θ : GaussianSpace)
    (ht : 0 ≤ t) (hθ : PaperBox θ) (k : ℕ) (hk : k ≤ 5) :
    |transformedMoment t θ k-gaussianMixtureMoment θ k| ≤ 10^9*t := by
  have h := transformedMoment_initial_residual_sharp t θ ht hθ k hk
  nlinarith

theorem H_initial_residual_le (t : ℝ) (θ : GaussianSpace)
    (ht : 0 ≤ t) (hθ : PaperBox θ) :
    ‖H t θ-H 0 θ‖ ≤ 10^9*t := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  simp only [Pi.sub_apply, H, transformedMoment_zero_scale, Real.norm_eq_abs]
  apply transformedMoment_initial_residual_le t θ ht hθ (i.val+1)
  have hi := i.isLt
  omega

theorem H_pair_initial_residual_le (t : ℝ) (θ η : GaussianSpace)
    (ht : 0 ≤ t) (hθ : PaperBox θ) (hη : PaperBox η) (hzero : H 0 θ = H 0 η) :
    ‖H t θ-H t η‖ ≤ 2*10^9*t := by
  have heq : H t θ-H t η = (H t θ-H 0 θ)-(H t η-H 0 η) := by rw [hzero]; abel
  rw [heq]
  calc
    _ ≤ ‖H t θ-H 0 θ‖+‖H t η-H 0 η‖ := norm_sub_le _ _
    _ ≤ 10^9*t+10^9*t :=
      add_le_add (H_initial_residual_le t θ ht hθ) (H_initial_residual_le t η ht hη)
    _ = 2*10^9*t := by ring

theorem gaussianSeedA_paperBox : PaperBox gaussianSeedA := by
  constructor
  · change (1/2 : ℝ) ∈ Icc (1/4) (3/4)
    norm_num
  · change |(-1 : ℝ)| ≤ 2
    norm_num
  · change |(1 : ℝ)| ≤ 2
    norm_num
  · change (1 : ℝ) ∈ Icc (1/2) 3
    norm_num
  · change (2 : ℝ) ∈ Icc (1/2) 3
    norm_num

theorem gaussianSeedB_paperBox : PaperBox gaussianSeedB := by
  have hp := AlgebraicSeed.pStar_spec
  have hw := AlgebraicSeed.piOf_bounds hp.1 hp.2.1
  have hm := AlgebraicSeed.means_bounds hp.1 hp.2.1
  have hv := AlgebraicSeed.variances_bounds hp.1 hp.2.1
  constructor
  · change AlgebraicSeed.piOf AlgebraicSeed.pStar ∈ Icc (1/4) (3/4)
    constructor <;> linarith [hw.1, hw.2]
  · change |AlgebraicSeed.mu0Of AlgebraicSeed.pStar| ≤ 2
    rw [abs_le]
    constructor <;> linarith [hm.1.1, hm.1.2]
  · change |AlgebraicSeed.mu1Of AlgebraicSeed.pStar| ≤ 2
    rw [abs_le]
    constructor <;> linarith [hm.2.1, hm.2.2]
  · change AlgebraicSeed.variance0Of AlgebraicSeed.pStar ∈ Icc (1/2) 3
    exact ⟨hv.1.1.le, hv.1.2.le⟩
  · change AlgebraicSeed.variance1Of AlgebraicSeed.pStar ∈ Icc (1/2) 3
    exact ⟨hv.2.1.le, hv.2.2.le⟩

/-- Concrete seed residual, before applying any inverse-Jacobian operator. -/
theorem gaussian_seeds_H_initial_residual_le (t : ℝ) (ht : 0 ≤ t) :
    ‖H t gaussianSeedB-H t gaussianSeedA‖ ≤ 2*10^9*t := by
  exact H_pair_initial_residual_le t gaussianSeedB gaussianSeedA ht
    gaussianSeedB_paperBox gaussianSeedA_paperBox H_zero_gaussian_seeds.symm

end LCR
