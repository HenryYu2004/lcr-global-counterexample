import LCR.ProbitModel
import LCR.GaussianMoments
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exact Gaussian-CDF to transformed-moment identity

`Phi` is the CDF of the actual standard Gaussian measure. The auxiliary
function is defined by an oriented interval integral, so all identities
hold for negative as well as positive arguments.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace LCR

noncomputable def phi0 : ℝ := (Real.sqrt (2*Real.pi))⁻¹

noncomputable def hTransform (t y : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..y, Real.exp (-t*u^2/2)

theorem phi0_pos : 0 < phi0 := by
  unfold phi0
  positivity

theorem standardGaussian_density (x : ℝ) :
    gaussianPDFReal 0 1 x = phi0 * Real.exp (-x^2/2) := by
  simp [gaussianPDFReal, phi0]

theorem Phi_eq_density_integral (x : ℝ) :
    Phi x = ∫ u in Iic x, gaussianPDFReal 0 1 u := by
  unfold Phi standardGaussian
  rw [cdf_eq_real, measureReal_def, gaussianReal_apply_eq_integral 0 (by norm_num)]
  rw [ENNReal.toReal_ofReal]
  exact integral_nonneg (gaussianPDFReal_nonneg 0 1)

theorem Phi_zero : Phi 0 = 1/2 := by
  have hi := integrable_gaussianPDFReal 0 (1 : ℝ≥0)
  have hsym : (∫ u in Iic (0 : ℝ), gaussianPDFReal 0 1 u) =
      ∫ u in Ioi (0 : ℝ), gaussianPDFReal 0 1 u := by
    calc
      _ = ∫ u in Iic (0 : ℝ), gaussianPDFReal 0 1 (-u) := by
        apply integral_congr_ae
        filter_upwards [] with u
        simp [gaussianPDFReal]
      _ = _ := by
        simpa using integral_comp_neg_Iic 0 (gaussianPDFReal 0 1)
  have hsum := intervalIntegral.integral_Iic_add_Ioi (b := (0 : ℝ))
    hi.integrableOn hi.integrableOn
  rw [integral_gaussianPDFReal_eq_one 0 (by norm_num)] at hsum
  rw [Phi_eq_density_integral]
  linarith

theorem Phi_sub_half_eq_density_interval (x : ℝ) :
    Phi x - 1/2 = ∫ u in (0 : ℝ)..x, gaussianPDFReal 0 1 u := by
  have hi := integrable_gaussianPDFReal 0 (1 : ℝ≥0)
  have h := intervalIntegral.integral_Iic_sub_Iic (a := (0 : ℝ)) (b := x)
    hi.integrableOn hi.integrableOn
  rw [← Phi_eq_density_integral, ← Phi_eq_density_integral, Phi_zero] at h
  exact h

theorem Phi_eq_half_add_integral (x : ℝ) :
    Phi x = 1/2 + phi0 * (∫ u in (0 : ℝ)..x, Real.exp (-u^2/2)) := by
  have h := Phi_sub_half_eq_density_interval x
  simp_rw [standardGaussian_density] at h
  rw [intervalIntegral.integral_const_mul] at h
  linarith

theorem hTransform_zero (y : ℝ) : hTransform 0 y = y := by
  simp [hTransform]

theorem hTransform_at_zero (t : ℝ) : hTransform t 0 = 0 := by
  simp [hTransform]

theorem hasDerivAt_hTransform (t y : ℝ) :
    HasDerivAt (hTransform t) (Real.exp (-t*y^2/2)) y := by
  have hc : Continuous (fun u : ℝ => Real.exp (-t*u^2/2)) := by fun_prop
  exact (hc.integral_hasStrictDerivAt 0 y).hasDerivAt

theorem continuous_hTransform (t : ℝ) : Continuous (hTransform t) := by
  exact continuous_iff_continuousAt.mpr (fun y => (hasDerivAt_hTransform t y).continuousAt)

theorem abs_hTransform_le (t y : ℝ) (ht : 0 ≤ t) :
    |hTransform t y| ≤ |y| := by
  unfold hTransform
  simpa only [Real.norm_eq_abs, one_mul, sub_zero] using
    (intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := y) (C := (1 : ℝ))
      (f := fun u : ℝ => Real.exp (-t*u^2/2)) (by
        intro u hu
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
        have hprod := mul_nonneg ht (sq_nonneg u)
        nlinarith))

/-- All transformed moments needed by the construction are genuine
integrable functions under every real Gaussian law. -/
theorem integrable_hTransform_pow (μ : ℝ) (v : ℝ≥0) (n : ℕ)
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun y : ℝ => hTransform t y ^ n) (gaussianReal μ v) := by
  apply (integrable_pow_gaussianReal μ v n).norm.mono'
  · exact ((continuous_hTransform t).pow n).aestronglyMeasurable
  · filter_upwards [] with y
    simpa only [Real.norm_eq_abs, abs_pow] using
      pow_le_pow_left₀ (abs_nonneg (hTransform t y)) (abs_hTransform_le t y ht) n

/-- Exact interval-integral rescaling, including zero scale. -/
theorem sqrt_mul_hTransform (t y : ℝ) (ht : 0 ≤ t) :
    Real.sqrt t * hTransform t y =
      ∫ u in (0 : ℝ)..Real.sqrt t*y, Real.exp (-u^2/2) := by
  have h := intervalIntegral.smul_integral_comp_mul_left
    (f := fun u : ℝ => Real.exp (-u^2/2)) (a := (0 : ℝ)) (b := y) (Real.sqrt t)
  simp only [smul_eq_mul, mul_zero] at h
  rw [← h]
  congr 1
  unfold hTransform
  apply intervalIntegral.integral_congr
  intro u hu
  dsimp
  congr 1
  rw [mul_pow, Real.sq_sqrt ht]
  ring

/-- Actual Gaussian-CDF identity underlying the exact lifting argument. -/
theorem Phi_sqrt_mul_eq (t y : ℝ) (ht : 0 ≤ t) :
    Phi (Real.sqrt t*y) = 1/2 + phi0*Real.sqrt t*hTransform t y := by
  rw [Phi_eq_half_add_integral, ← sqrt_mul_hTransform t y ht]
  ring

end LCR
