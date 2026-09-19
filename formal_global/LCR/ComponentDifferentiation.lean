import LCR.TransformedMoments
import LCR.TransformBounds
import Mathlib

/-!
# Genuine differentiation of transformed Gaussian component moments

This module differentiates the actual Gaussian integrals. All domination and
integrability requirements are discharged using Gaussian absolute moments.
The moment order is arbitrary; in particular the results apply to orders 1–5.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped Topology BigOperators NNReal

namespace LCR

theorem integrable_standardGaussian_abs_pow (n : ℕ) :
    Integrable (fun u : ℝ => |u| ^ n) standardGaussian := by
  simpa [standardGaussian, Real.norm_eq_abs, abs_pow] using
    (integrable_pow_gaussianReal 0 1 n).norm

/-- All polynomial envelopes in `|U|` that are needed for parameter
differentiation are integrable. The proof is a finite binomial expansion. -/
theorem integrable_standardGaussian_affine_abs_pow_weight
    (a b : ℝ) (n m : ℕ) :
    Integrable (fun u : ℝ => (a + b * |u|) ^ n * |u| ^ m) standardGaussian := by
  have heq : (fun u : ℝ => (a + b * |u|) ^ n * |u| ^ m) =
      fun u => ∑ i ∈ Finset.range (n + 1),
        (a ^ i * b ^ (n - i) * (n.choose i : ℝ)) * |u| ^ ((n - i) + m) := by
    funext u
    rw [add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_pow, pow_add]
    ring
  rw [heq]
  apply integrable_finsetSum
  intro i _
  exact (integrable_standardGaussian_abs_pow ((n - i) + m)).const_mul _

theorem integrable_standardGaussian_affine_abs_pow (a b : ℝ) (n : ℕ) :
    Integrable (fun u : ℝ => (a + b * |u|) ^ n) standardGaussian := by
  simpa only [pow_zero, mul_one] using
    integrable_standardGaussian_affine_abs_pow_weight a b n 0

def endpointPowerKernel (t y : ℝ) (k : ℕ) : ℝ :=
  (k : ℝ) * hTransform t y ^ (k - 1) * Real.exp (-t * y ^ 2 / 2)

theorem continuous_endpointPowerKernel (t : ℝ) (k : ℕ) :
    Continuous (fun y => endpointPowerKernel t y k) := by
  unfold endpointPowerKernel
  exact (continuous_const.mul ((continuous_hTransform t).pow (k - 1))).mul (by fun_prop)

theorem hasDerivAt_hTransform_pow (t y : ℝ) (k : ℕ) :
    HasDerivAt (fun x => hTransform t x ^ k) (endpointPowerKernel t y k) y := by
  exact (hasDerivAt_hTransform t y).pow k

theorem abs_endpointPowerKernel_le (t y : ℝ) (k : ℕ) (ht : 0 ≤ t) :
    |endpointPowerKernel t y k| ≤ (k : ℝ) * |y| ^ (k - 1) := by
  rw [endpointPowerKernel, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _),
    abs_pow, abs_of_pos (Real.exp_pos _)]
  calc
    (k : ℝ) * |hTransform t y| ^ (k - 1) * Real.exp (-t * y ^ 2 / 2)
        ≤ (k : ℝ) * |hTransform t y| ^ (k - 1) * 1 :=
      mul_le_mul_of_nonneg_left (exp_transform_le_one t y ht) (by positivity)
    _ ≤ (k : ℝ) * |y| ^ (k - 1) := by
      rw [mul_one]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg _) (abs_hTransform_le t y ht) (k - 1))
        (Nat.cast_nonneg _)

def affineTransformedMoment (t a b : ℝ) (k : ℕ) : ℝ :=
  ∫ u, hTransform t (a + b * u) ^ k ∂standardGaussian

theorem integrable_affineTransformed_power (t a b : ℝ) (k : ℕ) (ht : 0 ≤ t) :
    Integrable (fun u => hTransform t (a + b * u) ^ k) standardGaussian := by
  apply (integrable_standardGaussian_affine_abs_pow |a| |b| k).mono'
  · exact (((continuous_hTransform t).comp (by fun_prop)).pow k).aestronglyMeasurable
  · filter_upwards [] with u
    rw [Real.norm_eq_abs, abs_pow]
    apply pow_le_pow_left₀ (abs_nonneg _)
    calc
      |hTransform t (a + b * u)| ≤ |a + b * u| := abs_hTransform_le t _ ht
      _ ≤ |a| + |b| * |u| := by simpa only [abs_mul] using abs_add_le a (b * u)

private theorem abs_le_center_add_one_of_mem_ball {x a : ℝ} (hx : x ∈ ball a 1) :
    |x| ≤ |a| + 1 := by
  have hx' : |x - a| < 1 := by simpa only [mem_ball, Real.dist_eq] using hx
  calc
    |x| = |(x - a) + a| := by congr 1; ring
    _ ≤ |x - a| + |a| := abs_add_le _ _
    _ ≤ |a| + 1 := by linarith

theorem hasDerivAt_affineTransformedMoment_mean (t a b : ℝ) (k : ℕ) (ht : 0 ≤ t) :
    HasDerivAt (fun x => affineTransformedMoment t x b k)
      (∫ u, endpointPowerKernel t (a + b * u) k ∂standardGaussian) a := by
  let bound : ℝ → ℝ := fun u => (k : ℝ) * (|a| + 1 + |b| * |u|) ^ (k - 1)
  have hb : ∀ᵐ u ∂standardGaussian, ∀ x ∈ ball a 1,
      ‖endpointPowerKernel t (x + b * u) k‖ ≤ bound u := by
    filter_upwards [] with u
    intro x hx
    have hxabs := abs_le_center_add_one_of_mem_ball hx
    have hy : |x + b * u| ≤ |a| + 1 + |b| * |u| := by
      calc
        |x + b * u| ≤ |x| + |b| * |u| := by simpa only [abs_mul] using abs_add_le x (b * u)
        _ ≤ _ := by linarith
    rw [Real.norm_eq_abs]
    exact (abs_endpointPowerKernel_le t _ k ht).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hy (k - 1)) (Nat.cast_nonneg _))
  have hd : ∀ᵐ u ∂standardGaussian, ∀ x ∈ ball a 1,
      HasDerivAt (fun z => hTransform t (z + b * u) ^ k)
        (endpointPowerKernel t (x + b * u) k) x := by
    filter_upwards [] with u
    intro x _
    simpa only [one_mul, mul_one] using
      (hasDerivAt_hTransform_pow t (x + b * u) k).comp x ((hasDerivAt_id x).add_const (b * u))
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := standardGaussian) (s := ball a 1)
    (F := fun x u : ℝ => hTransform t (x + b * u) ^ k)
    (F' := fun x u : ℝ => endpointPowerKernel t (x + b * u) k)
    (bound := bound) (ball_mem_nhds a (by norm_num))
    (Eventually.of_forall fun x =>
      (((continuous_hTransform t).comp (by fun_prop)).pow k).aestronglyMeasurable)
    (integrable_affineTransformed_power t a b k ht)
    (((continuous_endpointPowerKernel t k).comp (by fun_prop)).aestronglyMeasurable)
    hb
    ((integrable_standardGaussian_affine_abs_pow (|a| + 1) |b| (k - 1)).const_mul (k : ℝ))
    hd
  exact h.2

theorem hasDerivAt_transformedComponentMoment_mean (t μ v : ℝ) (k : ℕ) (ht : 0 ≤ t) :
    HasDerivAt (fun x => transformedComponentMoment t x v k)
      (∫ u, endpointPowerKernel t (μ + Real.sqrt v * u) k ∂standardGaussian) μ :=
  hasDerivAt_affineTransformedMoment_mean t μ (Real.sqrt v) k ht

theorem hasDerivAt_affineTransformedMoment_loading (t a b : ℝ) (k : ℕ) (ht : 0 ≤ t) :
    HasDerivAt (fun x => affineTransformedMoment t a x k)
      (∫ u, endpointPowerKernel t (a + b * u) k * u ∂standardGaussian) b := by
  let bound : ℝ → ℝ := fun u =>
    (k : ℝ) * ((|a| + (|b| + 1) * |u|) ^ (k - 1) * |u|)
  have hb : ∀ᵐ u ∂standardGaussian, ∀ x ∈ ball b 1,
      ‖endpointPowerKernel t (a + x * u) k * u‖ ≤ bound u := by
    filter_upwards [] with u
    intro x hx
    have hxabs := abs_le_center_add_one_of_mem_ball hx
    have hy : |a + x * u| ≤ |a| + (|b| + 1) * |u| := by
      calc
        |a + x * u| ≤ |a| + |x| * |u| := by simpa only [abs_mul] using abs_add_le a (x * u)
        _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hxabs (abs_nonneg u))
    rw [Real.norm_eq_abs, abs_mul]
    have hk := (abs_endpointPowerKernel_le t _ k ht).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hy (k - 1)) (Nat.cast_nonneg _))
    simpa only [bound, mul_assoc] using mul_le_mul_of_nonneg_right hk (abs_nonneg u)
  have hd : ∀ᵐ u ∂standardGaussian, ∀ x ∈ ball b 1,
      HasDerivAt (fun z => hTransform t (a + z * u) ^ k)
        (endpointPowerKernel t (a + x * u) k * u) x := by
    filter_upwards [] with u
    intro x _
    simpa only [mul_one, one_mul, zero_add] using
      (hasDerivAt_hTransform_pow t (a + x * u) k).comp x
        ((hasDerivAt_const x a).add ((hasDerivAt_id x).mul_const u))
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := standardGaussian) (s := ball b 1)
    (F := fun x u : ℝ => hTransform t (a + x * u) ^ k)
    (F' := fun x u : ℝ => endpointPowerKernel t (a + x * u) k * u)
    (bound := bound) (ball_mem_nhds b (by norm_num))
    (Eventually.of_forall fun x =>
      (((continuous_hTransform t).comp (by fun_prop)).pow k).aestronglyMeasurable)
    (integrable_affineTransformed_power t a b k ht)
    ((((continuous_endpointPowerKernel t k).comp (by fun_prop)).mul continuous_id).aestronglyMeasurable)
    hb
    (by simpa only [pow_one] using
      (integrable_standardGaussian_affine_abs_pow_weight |a| (|b| + 1) (k - 1) 1).const_mul (k : ℝ))
    hd
  exact h.2

theorem hasDerivAt_transformedComponentMoment_variance (t μ v : ℝ) (k : ℕ)
    (ht : 0 ≤ t) (hv : 0 < v) :
    HasDerivAt (fun x => transformedComponentMoment t μ x k)
      (∫ u, endpointPowerKernel t (μ + Real.sqrt v * u) k * u /
        (2 * Real.sqrt v) ∂standardGaussian) v := by
  have h := (hasDerivAt_affineTransformedMoment_loading t μ (Real.sqrt v) k ht).comp v
    (Real.hasDerivAt_sqrt hv.ne')
  convert h using 1
  rw [integral_div]
  ring

def affinePairDerivative (t : ℝ) (p : ℝ × ℝ) (k : ℕ) (u : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  endpointPowerKernel t (p.1 + p.2 * u) k •
    (ContinuousLinearMap.fst ℝ ℝ ℝ + u • ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem continuous_affinePairDerivative (t : ℝ) (p : ℝ × ℝ) (k : ℕ) :
    Continuous (affinePairDerivative t p k) := by
  unfold affinePairDerivative
  exact ((continuous_endpointPowerKernel t k).comp (by fun_prop)).smul (by fun_prop)

theorem norm_affinePairDerivative_le (t : ℝ) (p : ℝ × ℝ) (k : ℕ) (u : ℝ)
    (ht : 0 ≤ t) :
    ‖affinePairDerivative t p k u‖ ≤
      (k : ℝ) * |p.1 + p.2 * u| ^ (k - 1) * (1 + |u|) := by
  have he : ‖ContinuousLinearMap.fst ℝ ℝ ℝ + u • ContinuousLinearMap.snd ℝ ℝ ℝ‖ ≤
      1 + |u| := by
    calc
      _ ≤ ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖ + ‖u • ContinuousLinearMap.snd ℝ ℝ ℝ‖ := norm_add_le _ _
      _ = _ := by simp [norm_smul, Real.norm_eq_abs]
  rw [affinePairDerivative, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul (abs_endpointPowerKernel_le t _ k ht) he (norm_nonneg _) (by positivity)

theorem hasFDerivAt_affinePower_integrand (t : ℝ) (p : ℝ × ℝ) (k : ℕ) (u : ℝ) :
    HasFDerivAt (fun q : ℝ × ℝ => hTransform t (q.1 + q.2 * u) ^ k)
      (affinePairDerivative t p k u) p := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.fst ℝ ℝ ℝ + u • ContinuousLinearMap.snd ℝ ℝ ℝ
  have h := (hasDerivAt_hTransform_pow t (L p) k).comp_hasFDerivAt p L.hasFDerivAt
  simpa [affinePairDerivative, L, Function.comp_def, mul_comm u] using h

/-- A simultaneous mean/loading derivative, established directly under the
Gaussian integral rather than inferred from separate scalar partials. -/
theorem hasFDerivAt_affineTransformedMoment_pair (t : ℝ) (p : ℝ × ℝ) (k : ℕ)
    (ht : 0 ≤ t) :
    HasFDerivAt (fun q : ℝ × ℝ => affineTransformedMoment t q.1 q.2 k)
      (∫ u, affinePairDerivative t p k u ∂standardGaussian) p := by
  let A := |p.1| + 1
  let B := |p.2| + 1
  let bound : ℝ → ℝ := fun u => (k : ℝ) * ((A + B * |u|) ^ (k - 1) * (1 + |u|))
  have hb : ∀ᵐ u ∂standardGaussian, ∀ q ∈ ball p 1,
      ‖affinePairDerivative t q k u‖ ≤ bound u := by
    filter_upwards [] with u
    intro q hq
    have hq' : max (dist q.1 p.1) (dist q.2 p.2) < 1 := by
      simpa only [mem_ball, Prod.dist_eq] using hq
    have hqa := abs_le_center_add_one_of_mem_ball (max_lt_iff.mp hq').1
    have hqb := abs_le_center_add_one_of_mem_ball (max_lt_iff.mp hq').2
    have hy : |q.1 + q.2 * u| ≤ A + B * |u| := by
      calc
        _ ≤ |q.1| + |q.2| * |u| := by simpa only [abs_mul] using abs_add_le q.1 (q.2 * u)
        _ ≤ _ := add_le_add hqa (mul_le_mul_of_nonneg_right hqb (abs_nonneg u))
    have hp := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) hy (k - 1)) (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    exact (norm_affinePairDerivative_le t q k u ht).trans
      (by simpa only [bound, mul_assoc] using mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ 1 + |u|))
  have hbi : Integrable bound standardGaussian := by
    have h0 := integrable_standardGaussian_affine_abs_pow A B (k - 1)
    have h1 := integrable_standardGaussian_affine_abs_pow_weight A B (k - 1) 1
    simpa only [bound, Pi.add_apply, mul_add, mul_one, pow_one] using (h0.add h1).const_mul (k : ℝ)
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := standardGaussian) (s := ball p 1)
    (F := fun q : ℝ × ℝ => fun u => hTransform t (q.1 + q.2 * u) ^ k)
    (F' := fun q => affinePairDerivative t q k) (bound := bound)
    (ball_mem_nhds p (by norm_num))
    (Eventually.of_forall fun q =>
      (((continuous_hTransform t).comp (by fun_prop)).pow k).aestronglyMeasurable)
    (integrable_affineTransformed_power t p.1 p.2 k ht)
    ((continuous_affinePairDerivative t p k).aestronglyMeasurable)
    hb hbi
    (by filter_upwards [] with u; intro q _; exact hasFDerivAt_affinePower_integrand t q k u)

theorem integrable_affinePairDerivative (t : ℝ) (p : ℝ × ℝ) (k : ℕ) (ht : 0 ≤ t) :
    Integrable (affinePairDerivative t p k) standardGaussian := by
  let A := |p.1|
  let B := |p.2|
  have h0 := integrable_standardGaussian_affine_abs_pow A B (k - 1)
  have h1 := integrable_standardGaussian_affine_abs_pow_weight A B (k - 1) 1
  have hi : Integrable (fun u => (k : ℝ) * ((A + B * |u|) ^ (k - 1) * (1 + |u|)))
      standardGaussian := by
    simpa only [Pi.add_apply, mul_add, mul_one, pow_one] using (h0.add h1).const_mul (k : ℝ)
  apply hi.mono' (continuous_affinePairDerivative t p k).aestronglyMeasurable
  filter_upwards [] with u
  have hy : |p.1 + p.2 * u| ≤ A + B * |u| := by
    simpa only [A, B, abs_mul] using abs_add_le p.1 (p.2 * u)
  have hp := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (abs_nonneg _) hy (k - 1)) (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  exact (norm_affinePairDerivative_le t p k u ht).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ 1 + |u|))

/-- Pointwise Fréchet derivative with respect to arbitrary mean and variance
coordinates in the five-dimensional Gaussian parameter vector. -/
def componentParameterDerivative (t : ℝ) (a v : Fin 5) (k : ℕ)
    (θ : GaussianSpace) (u : ℝ) : GaussianSpace →L[ℝ] ℝ :=
  endpointPowerKernel t (θ a + Real.sqrt (θ v) * u) k •
    (ContinuousLinearMap.proj a + (u / (2 * Real.sqrt (θ v))) • ContinuousLinearMap.proj v)

theorem componentParameterDerivative_apply (t : ℝ) (a v : Fin 5) (k : ℕ)
    (θ : GaussianSpace) (u : ℝ) (d : GaussianSpace) :
    componentParameterDerivative t a v k θ u d =
      endpointPowerKernel t (θ a + Real.sqrt (θ v) * u) k *
        (d a + (u / (2 * Real.sqrt (θ v))) * d v) := by
  simp [componentParameterDerivative]
  ring

private def meanVarianceDerivative (a v : Fin 5) (θ : GaussianSpace) :
    GaussianSpace →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.proj a).prod
    ((1 / (2 * Real.sqrt (θ v))) • ContinuousLinearMap.proj v)

private theorem affinePairDerivative_comp_meanVariance (t : ℝ) (a v : Fin 5) (k : ℕ)
    (θ : GaussianSpace) (u : ℝ) :
    (affinePairDerivative t (θ a, Real.sqrt (θ v)) k u).comp (meanVarianceDerivative a v θ) =
      componentParameterDerivative t a v k θ u := by
  ext d
  change endpointPowerKernel t (θ a + Real.sqrt (θ v) * u) k *
      (d a + u * ((1 / (2 * Real.sqrt (θ v))) * d v)) =
    endpointPowerKernel t (θ a + Real.sqrt (θ v) * u) k *
      (d a + (u / (2 * Real.sqrt (θ v))) * d v)
  ring

theorem integrable_componentParameterDerivative (t : ℝ) (a v : Fin 5) (k : ℕ)
    (θ : GaussianSpace) (ht : 0 ≤ t) :
    Integrable (componentParameterDerivative t a v k θ) standardGaussian := by
  let R := (ContinuousLinearMap.compL ℝ GaussianSpace (ℝ × ℝ) ℝ).flip
    (meanVarianceDerivative a v θ)
  have hi := R.integrable_comp
    (integrable_affinePairDerivative t (θ a, Real.sqrt (θ v)) k ht)
  have heq : (fun u => R (affinePairDerivative t (θ a, Real.sqrt (θ v)) k u)) =
      componentParameterDerivative t a v k θ := by
    funext u
    exact affinePairDerivative_comp_meanVariance t a v k θ u
  exact heq ▸ hi

/-- Full five-dimensional Fréchet differentiability of an actual component
moment. No interchange of differentiation and integration is assumed. -/
theorem hasFDerivAt_transformedComponentMoment_parameters
    (t : ℝ) (a v : Fin 5) (k : ℕ) (θ : GaussianSpace) (ht : 0 ≤ t) (hv : 0 < θ v) :
    HasFDerivAt (fun η : GaussianSpace => transformedComponentMoment t (η a) (η v) k)
      (∫ u, componentParameterDerivative t a v k θ u ∂standardGaussian) θ := by
  have hg : HasFDerivAt (fun η : GaussianSpace => (η a, Real.sqrt (η v)))
      (meanVarianceDerivative a v θ) θ := by
    have ha : HasFDerivAt (fun η : GaussianSpace => η a) (ContinuousLinearMap.proj a) θ :=
      (ContinuousLinearMap.proj a : GaussianSpace →L[ℝ] ℝ).hasFDerivAt
    have hv' : HasFDerivAt (fun η : GaussianSpace => Real.sqrt (η v))
        ((1 / (2 * Real.sqrt (θ v))) • ContinuousLinearMap.proj v) θ :=
      (Real.hasDerivAt_sqrt hv.ne').comp_hasFDerivAt θ
        (ContinuousLinearMap.proj v : GaussianSpace →L[ℝ] ℝ).hasFDerivAt
    exact ha.prodMk hv'
  have h := (hasFDerivAt_affineTransformedMoment_pair t (θ a, Real.sqrt (θ v)) k ht).comp θ hg
  let R := (ContinuousLinearMap.compL ℝ GaussianSpace (ℝ × ℝ) ℝ).flip
    (meanVarianceDerivative a v θ)
  have heq : (∫ u, componentParameterDerivative t a v k θ u ∂standardGaussian) =
      (∫ u, affinePairDerivative t (θ a, Real.sqrt (θ v)) k u ∂standardGaussian).comp
        (meanVarianceDerivative a v θ) := by
    calc
      _ = ∫ u, R (affinePairDerivative t (θ a, Real.sqrt (θ v)) k u) ∂standardGaussian := by
        apply integral_congr_ae
        filter_upwards [] with u
        exact (affinePairDerivative_comp_meanVariance t a v k θ u).symm
      _ = _ := R.integral_comp_comm
        (integrable_affinePairDerivative t (θ a, Real.sqrt (θ v)) k ht)
  rw [heq]
  exact h

end LCR
