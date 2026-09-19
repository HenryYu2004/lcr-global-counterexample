import LCR.ProbitTransform
import Mathlib

/-!
# Bounds for the actual probit-transform interval integral

The function `LCR.hTransform` is the actual oriented interval integral from
`ProbitTransform.lean`, not an abstract function with postulated derivatives.
All estimates below hold for negative as well as positive endpoint `y`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Interval

namespace LCR

theorem deriv_hTransform_eq (t y : ℝ) :
    deriv (hTransform t) y = Real.exp (-t * y ^ 2 / 2) :=
  (hasDerivAt_hTransform t y).deriv

theorem exp_transform_le_one (t y : ℝ) (ht : 0 ≤ t) :
    Real.exp (-t * y ^ 2 / 2) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  nlinarith [mul_nonneg ht (sq_nonneg y)]

theorem abs_deriv_hTransform_le_one (t y : ℝ) (ht : 0 ≤ t) :
    |deriv (hTransform t) y| ≤ 1 := by
  rw [deriv_hTransform_eq, abs_of_pos (Real.exp_pos _)]
  exact exp_transform_le_one t y ht

theorem hasDerivAt_deriv_hTransform (t y : ℝ) :
    HasDerivAt (fun x => deriv (hTransform t) x)
      (-t * y * Real.exp (-t * y ^ 2 / 2)) y := by
  simp_rw [deriv_hTransform_eq]
  convert ((((hasDerivAt_id y).pow 2).const_mul (-t)).div_const 2).exp using 1 <;>
    simp only [Pi.pow_apply, id_eq] <;> ring

theorem deriv_deriv_hTransform_eq (t y : ℝ) :
    deriv (fun x => deriv (hTransform t) x) y =
      -t * y * Real.exp (-t * y ^ 2 / 2) :=
  (hasDerivAt_deriv_hTransform t y).deriv

theorem abs_deriv_deriv_hTransform_le (t y : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    |deriv (fun x => deriv (hTransform t) x) y| ≤ |y| := by
  rw [deriv_deriv_hTransform_eq, abs_mul, abs_mul, abs_neg,
    abs_of_nonneg ht, abs_of_pos (Real.exp_pos _)]
  calc
    t * |y| * Real.exp (-t * y ^ 2 / 2) ≤ t * |y| * 1 :=
      mul_le_mul_of_nonneg_left (exp_transform_le_one t y ht) (mul_nonneg ht (abs_nonneg y))
    _ ≤ |y| := by nlinarith [abs_nonneg y]

/-- The derivative of the exponential integrand with respect to its time
parameter. -/
def transformTimeKernel (t y : ℝ) : ℝ :=
  (-y ^ 2 / 2) * Real.exp (-t * y ^ 2 / 2)

theorem hasDerivAt_transform_integrand_time (t y : ℝ) :
    HasDerivAt (fun s => Real.exp (-s * y ^ 2 / 2)) (transformTimeKernel t y) t := by
  convert (((hasDerivAt_id t).neg.mul_const (y ^ 2)).div_const 2).exp using 1 <;>
    simp only [transformTimeKernel, Pi.neg_apply, id_eq] <;> ring

theorem abs_transformTimeKernel_le (t y : ℝ) (ht : 0 ≤ t) :
    |transformTimeKernel t y| ≤ y ^ 2 / 2 := by
  have hn : -y ^ 2 / 2 ≤ 0 := by nlinarith [sq_nonneg y]
  rw [transformTimeKernel, abs_mul, abs_of_nonpos hn, abs_of_pos (Real.exp_pos _)]
  have h := mul_le_mul_of_nonneg_left (exp_transform_le_one t y ht)
    (show 0 ≤ y ^ 2 / 2 by positivity)
  nlinarith

theorem hasDerivAt_deriv_hTransform_time (t y : ℝ) :
    HasDerivAt (fun s => deriv (hTransform s) y) (transformTimeKernel t y) t := by
  simpa only [deriv_hTransform_eq] using hasDerivAt_transform_integrand_time t y

theorem abs_deriv_time_deriv_hTransform_le (t y : ℝ) (ht : 0 ≤ t) :
    |deriv (fun s => deriv (hTransform s) y) t| ≤ |y| ^ 2 / 2 := by
  rw [(hasDerivAt_deriv_hTransform_time t y).deriv, sq_abs]
  exact abs_transformTimeKernel_le t y ht

/-- An actual interval integral, subsequently identified with the time
derivative of `hTransform`. -/
def hTransformTime (t y : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..y, transformTimeKernel t u

theorem abs_hTransformTime_le (t y : ℝ) (ht : 0 ≤ t) :
    |hTransformTime t y| ≤ |y| ^ 3 / 6 := by
  have h := intervalIntegral.norm_integral_le_abs_of_norm_le
    (μ := volume) (a := (0 : ℝ)) (b := y)
    (f := transformTimeKernel t) (g := fun u : ℝ => u ^ 2 / 2)
    (by
      filter_upwards [] with u
      simpa only [Real.norm_eq_abs] using abs_transformTimeKernel_le t u ht)
    ((by fun_prop : Continuous (fun u : ℝ => u ^ 2 / 2)).intervalIntegrable 0 y)
  convert h using 1 <;>
    norm_num [hTransformTime, Real.norm_eq_abs, integral_pow, abs_div, abs_pow] <;> ring

/-- Differentiation under the actual bounded-interval integral with respect
to the time parameter.  The proof uses a continuous dominating function on
the integration interval and works for every real `t`, including zero. -/
theorem hasDerivAt_hTransform_time (t y : ℝ) :
    HasDerivAt (fun s => hTransform s y) (hTransformTime t y) t := by
  let bound : ℝ → ℝ := fun u => (u ^ 2 / 2) * Real.exp ((1 - t) * u ^ 2 / 2)
  have hs : Ioi (t - 1) ∈ 𝓝 t := Ioi_mem_nhds (by linarith)
  have hb : ∀ᵐ u ∂volume, u ∈ Ι (0 : ℝ) y →
      ∀ s ∈ Ioi (t - 1), ‖transformTimeKernel s u‖ ≤ bound u := by
    filter_upwards [] with u
    intro _ s hs
    have hlow : -s ≤ 1 - t := by
      simp only [mem_Ioi] at hs
      linarith
    have hexp : -s * u ^ 2 / 2 ≤ (1 - t) * u ^ 2 / 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hlow (sq_nonneg u)]
    have hn : -u ^ 2 / 2 ≤ 0 := by nlinarith [sq_nonneg u]
    rw [transformTimeKernel, Real.norm_eq_abs, abs_mul,
      abs_of_nonpos hn, abs_of_pos (Real.exp_pos _)]
    dsimp [bound]
    calc
      -(-u ^ 2 / 2) * Real.exp (-s * u ^ 2 / 2)
          = (u ^ 2 / 2) * Real.exp (-s * u ^ 2 / 2) := by ring
      _ ≤ (u ^ 2 / 2) * Real.exp ((1 - t) * u ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := y)
    (F := fun s u : ℝ => Real.exp (-s * u ^ 2 / 2))
    (F' := transformTimeKernel) (bound := bound) hs
    (Eventually.of_forall fun s =>
      (by fun_prop : Continuous (fun u : ℝ => Real.exp (-s * u ^ 2 / 2))).aestronglyMeasurable)
    ((by fun_prop : Continuous (fun u : ℝ => Real.exp (-t * u ^ 2 / 2))).intervalIntegrable 0 y)
    ((by unfold transformTimeKernel; fun_prop : Continuous (transformTimeKernel t)).aestronglyMeasurable)
    hb
    ((by dsimp [bound]; fun_prop : Continuous bound).intervalIntegrable 0 y)
    (by
      filter_upwards [] with u
      intro _ s _
      exact hasDerivAt_transform_integrand_time s u)
  exact h.2

theorem deriv_hTransform_time_eq (t y : ℝ) :
    deriv (fun s => hTransform s y) t = hTransformTime t y :=
  (hasDerivAt_hTransform_time t y).deriv

theorem abs_deriv_hTransform_time_le (t y : ℝ) (ht : 0 ≤ t) :
    |deriv (fun s => hTransform s y) t| ≤ |y| ^ 3 / 6 := by
  rw [deriv_hTransform_time_eq]
  exact abs_hTransformTime_le t y ht

/-- The other order of the mixed time/endpoint derivative, obtained by
the fundamental theorem of calculus after the time-derivative formula. -/
theorem hasDerivAt_hTransformTime_endpoint (t y : ℝ) :
    HasDerivAt (hTransformTime t) (transformTimeKernel t y) y := by
  exact ((by unfold transformTimeKernel; fun_prop : Continuous (transformTimeKernel t)).integral_hasStrictDerivAt 0 y).hasDerivAt

theorem abs_deriv_endpoint_time_hTransform_le (t y : ℝ) (ht : 0 ≤ t) :
    |deriv (fun x => deriv (fun s => hTransform s x) t) y| ≤ |y| ^ 2 / 2 := by
  simp_rw [deriv_hTransform_time_eq]
  rw [(hasDerivAt_hTransformTime_endpoint t y).deriv, sq_abs]
  exact abs_transformTimeKernel_le t y ht

end LCR
