import LCR.GaussianMixture

/-! An exact eighth Gaussian moment and a polynomial domination envelope. -/

open MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal

set_option maxHeartbeats 2000000

noncomputable section
namespace LCR

private def positiveHermite : ℕ → Polynomial ℝ
  | 0 => 1
  | n+1 => (positiveHermite n).derivative + X * positiveHermite n

private def normalMGF (t : ℝ) : ℝ := Real.exp (t^2/2)

private theorem normalMGF_derivative (t : ℝ) :
    HasDerivAt normalMGF (t*normalMGF t) t := by
  unfold normalMGF
  convert (((hasDerivAt_id t).pow 2).div_const 2).exp using 1 <;> dsimp <;> ring

private theorem normalMGF_iterated (n : ℕ) :
    iteratedDeriv n normalMGF = fun t => (positiveHermite n).eval t * normalMGF t := by
  induction n with
  | zero => simp [positiveHermite]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have h := ((positiveHermite n).hasDerivAt t).mul (normalMGF_derivative t)
    calc
      _ = (positiveHermite n).derivative.eval t * normalMGF t +
          (positiveHermite n).eval t * (t * normalMGF t) := h.deriv
      _ = _ := by
        simp only [positiveHermite, eval_add, eval_mul, eval_X]
        ring

theorem standardGaussian_eighth_moment :
    (∫ u : ℝ, u^8 ∂standardGaussian) = 105 := by
  have h := iteratedDeriv_mgf_zero
    (X := fun u : ℝ => u) (μ := gaussianReal 0 1) (by simp) 8
  rw [mgf_fun_id_gaussianReal] at h
  have hm : (fun t : ℝ => Real.exp (0*t + (1:ℝ≥0)*t^2/2)) = normalMGF := by
    funext t
    simp [normalMGF]
  change iteratedDeriv 8 (fun t : ℝ => Real.exp (0*t + (1:ℝ≥0)*t^2/2)) 0 = _ at h
  rw [hm, normalMGF_iterated] at h
  change (positiveHermite 8).eval 0 * normalMGF 0 =
    ∫ u : ℝ, u^8 ∂standardGaussian at h
  rw [← h]
  norm_num [positiveHermite, normalMGF, derivative_add, derivative_mul,
    derivative_one, derivative_X, eval_add, eval_mul]

def gaussianEnvelope (u : ℝ) : ℝ := 2*(1+|u|)

theorem gaussianEnvelope_ge_two (u : ℝ) : 2 ≤ gaussianEnvelope u := by
  unfold gaussianEnvelope
  linarith [abs_nonneg u]

theorem abs_pow_seven_le (u : ℝ) : |u|^7 ≤ 1+u^8 := by
  by_cases hu : |u| ≤ 1
  · have hp := pow_le_one₀ (abs_nonneg u) hu (n := 7)
    nlinarith [show (0 : ℝ) ≤ u^8 by positivity]
  · have hu' : 1 ≤ |u| := le_of_lt (lt_of_not_ge hu)
    have hp : |u|^7 ≤ |u|^8 := pow_le_pow_right₀ hu' (by norm_num)
    rw [show |u|^8 = u^8 by rw [← abs_pow, abs_of_nonneg (by positivity)]] at hp
    linarith

theorem gaussianEnvelope_seven_bound (u : ℝ) :
    gaussianEnvelope u ^ 7 ≤ 8192*(2+u^8) := by
  have h := add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) (abs_nonneg u) 7
  norm_num at h
  have hp := abs_pow_seven_le u
  calc
    gaussianEnvelope u^7 = 128*(1+|u|)^7 := by unfold gaussianEnvelope; ring
    _ ≤ 8192*(1+|u|^7) := by linarith
    _ ≤ 8192*(2+u^8) := by linarith

theorem integrable_gaussianEnvelope_seven :
    Integrable (fun u => gaussianEnvelope u^7) standardGaussian := by
  have h8 : Integrable (fun u : ℝ => u^8) standardGaussian :=
    integrable_pow_gaussianReal 0 1 8
  apply (((integrable_const (2 : ℝ)).add h8).const_mul (8192 : ℝ)).mono'
  · exact (by unfold gaussianEnvelope; fun_prop :
      Continuous (fun u => gaussianEnvelope u^7)).aestronglyMeasurable
  · filter_upwards [] with u
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by
      have h := gaussianEnvelope_ge_two u
      linarith) 7)]
    exact gaussianEnvelope_seven_bound u

theorem integral_gaussianEnvelope_seven_le :
    (∫ u, gaussianEnvelope u^7 ∂standardGaussian) ≤ 876544 := by
  have h8 : Integrable (fun u : ℝ => u^8) standardGaussian :=
    integrable_pow_gaussianReal 0 1 8
  have hi := integral_mono integrable_gaussianEnvelope_seven
    (((integrable_const (2 : ℝ)).add h8).const_mul (8192 : ℝ)) gaussianEnvelope_seven_bound
  rw [integral_const_mul] at hi
  change (∫ u, gaussianEnvelope u^7 ∂standardGaussian) ≤
    8192*(∫ u : ℝ, 2+u^8 ∂standardGaussian) at hi
  rw [integral_add (integrable_const _) h8, standardGaussian_eighth_moment] at hi
  norm_num at hi
  exact hi

theorem gaussianEnvelope_pow_le_seven (u : ℝ) (k : ℕ) (hk : k ≤ 7) :
    gaussianEnvelope u^k ≤ gaussianEnvelope u^7 := by
  exact pow_le_pow_right₀ (by linarith [gaussianEnvelope_ge_two u]) hk

theorem integrable_gaussianEnvelope_pow (k : ℕ) (hk : k ≤ 7) :
    Integrable (fun u => gaussianEnvelope u^k) standardGaussian := by
  apply integrable_gaussianEnvelope_seven.mono'
  · exact (by unfold gaussianEnvelope; fun_prop :
      Continuous (fun u => gaussianEnvelope u^k)).aestronglyMeasurable
  · filter_upwards [] with u
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by
      have h := gaussianEnvelope_ge_two u
      linarith) k)]
    exact gaussianEnvelope_pow_le_seven u k hk

theorem integral_gaussianEnvelope_pow_le (k : ℕ) (hk : k ≤ 7) :
    (∫ u, gaussianEnvelope u^k ∂standardGaussian) ≤ 876544 := by
  exact (integral_mono (integrable_gaussianEnvelope_pow k hk)
    integrable_gaussianEnvelope_seven (fun u => gaussianEnvelope_pow_le_seven u k hk)).trans
      integral_gaussianEnvelope_seven_le

theorem abs_affineGaussian_le_envelope (μ v u : ℝ) (hμ : |μ| ≤ 2) (hv : v ≤ 3) :
    |μ + Real.sqrt v*u| ≤ gaussianEnvelope u := by
  have hs : Real.sqrt v ≤ 2 := by
    apply Real.sqrt_le_iff.mpr
    constructor <;> linarith
  calc
    |μ + Real.sqrt v*u| ≤ |μ| + |Real.sqrt v*u| := abs_add_le _ _
    _ = |μ| + Real.sqrt v*|u| := by rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    _ ≤ 2 + 2*|u| := add_le_add hμ (mul_le_mul_of_nonneg_right hs (abs_nonneg u))
    _ = gaussianEnvelope u := by unfold gaussianEnvelope; ring

end LCR
