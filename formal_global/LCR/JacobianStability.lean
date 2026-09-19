import LCR.PowerBounds
import LCR.InitialResidual
import LCR.JacobianEntries

/-! Explicit pointwise and integrated stability estimates for the genuine
Gaussian transformed-moment Jacobian. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

noncomputable section
namespace LCR

theorem sqrt_ge_half_of_half_le {v : ℝ} (hv : 1/2 ≤ v) :
    1/2 ≤ Real.sqrt v := by
  have hv0 : 0 ≤ v := by linarith
  have hs := Real.sqrt_nonneg v
  have hs2 := Real.sq_sqrt hv0
  nlinarith

theorem sqrt_lipschitz_on_variance_box {v w : ℝ}
    (hv : 1/2 ≤ v) (hw : 1/2 ≤ w) :
    |Real.sqrt v-Real.sqrt w| ≤ |v-w| := by
  have hv0 : 0 ≤ v := by linarith
  have hw0 : 0 ≤ w := by linarith
  have hs : 1 ≤ Real.sqrt v+Real.sqrt w := by
    linarith [sqrt_ge_half_of_half_le hv, sqrt_ge_half_of_half_le hw]
  have hprod : (Real.sqrt v-Real.sqrt w)*(Real.sqrt v+Real.sqrt w) = v-w := by
    nlinarith [Real.sq_sqrt hv0, Real.sq_sqrt hw0]
  have habs := congrArg abs hprod
  rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ Real.sqrt v+Real.sqrt w)] at habs
  nlinarith [abs_nonneg (Real.sqrt v-Real.sqrt w)]

def varianceSlope (v u : ℝ) : ℝ := u/(2*Real.sqrt v)

theorem abs_varianceSlope_le (v u : ℝ) (hv : 1/2 ≤ v) :
    |varianceSlope v u| ≤ |u| := by
  have hs := sqrt_ge_half_of_half_le hv
  have hd : 0 < 2*Real.sqrt v := by linarith
  rw [varianceSlope, abs_div, abs_of_pos hd, div_le_iff₀ hd]
  nlinarith [abs_nonneg u]

theorem abs_varianceSlope_sub_le (v w u : ℝ)
    (hv : 1/2 ≤ v) (hw : 1/2 ≤ w) :
    |varianceSlope v u-varianceSlope w u| ≤ 2 * |u| * |v-w| := by
  have hsv := sqrt_ge_half_of_half_le hv
  have hsw := sqrt_ge_half_of_half_le hw
  have hsv0 : Real.sqrt v ≠ 0 := by linarith
  have hsw0 : Real.sqrt w ≠ 0 := by linarith
  have hden : 0 < 2*Real.sqrt v*Real.sqrt w := by positivity
  have hdenlo : 1/2 ≤ 2*Real.sqrt v*Real.sqrt w := by
    nlinarith [mul_nonneg (show 0 ≤ Real.sqrt v-1/2 by linarith)
      (show 0 ≤ Real.sqrt w-1/2 by linarith)]
  have heq : varianceSlope v u-varianceSlope w u =
      u*(Real.sqrt w-Real.sqrt v)/(2*Real.sqrt v*Real.sqrt w) := by
    unfold varianceSlope
    field_simp
  rw [heq, abs_div, abs_mul, abs_of_pos hden]
  have hs : |Real.sqrt w-Real.sqrt v| ≤ |v-w| := by
    simpa only [abs_sub_comm] using sqrt_lipschitz_on_variance_box hw hv
  rw [div_le_iff₀ hden]
  have hfirst := mul_le_mul_of_nonneg_left hs (abs_nonneg u)
  have hprod := mul_le_mul_of_nonneg_left hdenlo
    (show 0 ≤ 2 * |u| * |v-w| by positivity)
  nlinarith

theorem abs_affineGaussian_sub_le (μ ν v w u : ℝ)
    (hv : 1/2 ≤ v) (hw : 1/2 ≤ w) :
    |(μ+Real.sqrt v*u)-(ν+Real.sqrt w*u)| ≤ |μ-ν| + |u| * |v-w| := by
  have heq : (μ+Real.sqrt v*u)-(ν+Real.sqrt w*u) =
      (μ-ν)+(Real.sqrt v-Real.sqrt w)*u := by ring
  rw [heq]
  calc
    _ ≤ |μ-ν|+|(Real.sqrt v-Real.sqrt w)*u| := abs_add_le _ _
    _ = |μ-ν| + |u| * |Real.sqrt v-Real.sqrt w| := by rw [abs_mul]; ring
    _ ≤ _ := add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (sqrt_lipschitz_on_variance_box hv hw) (abs_nonneg u))

theorem endpointPowerKernel_time_difference_le (t y L : ℝ) (k : ℕ)
    (ht : 0 ≤ t) (hy : |y| ≤ L) (hL : 1 ≤ L) (hk : k ≤ 5) :
    |endpointPowerKernel t y k-endpointPowerKernel 0 y k| ≤ 6*L^6*t := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := (0 : ℝ)) (b := t) (f := fun s => endpointPowerKernel s y k)
    (f' := fun s => endpointPowerTime s y k) (C := 6*L^6)
    (fun s hs => (hasDerivAt_endpointPowerKernel_time s y k).hasDerivWithinAt)
    (fun s hs => by
      rw [Real.norm_eq_abs]
      have h := abs_endpointPowerTime_le_envelope s y L k hs.1 hy hL hk
      have hpos : 0 ≤ L^6 := by positivity
      nlinarith)
    t ⟨ht, le_rfl⟩
  simpa only [Real.norm_eq_abs, sub_zero] using h

theorem endpointPowerKernel_endpoint_difference_le (y z L : ℝ) (k : ℕ)
    (hy : |y| ≤ L) (hz : |z| ≤ L) (hL : 1 ≤ L) (hk : k ≤ 5) :
    |endpointPowerKernel 0 y k-endpointPowerKernel 0 z k| ≤ 25*L^5*|y-z| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Icc (-L) L) (f := fun x => endpointPowerKernel 0 x k)
    (f' := fun x => endpointPowerY 0 x k) (C := 25*L^5)
    (fun x hx => (hasDerivAt_endpointPowerKernel_y 0 x k).hasDerivWithinAt)
    (fun x hx => by
      rw [Real.norm_eq_abs]
      exact abs_endpointPowerY_le_envelope 0 x L k (by norm_num) (by norm_num)
        (abs_le.mpr hx) hL hk)
    (convex_Icc (-L) L) (abs_le.mp hz) (abs_le.mp hy)
  simpa only [Real.norm_eq_abs] using h

theorem abs_self_le_gaussianEnvelope (u : ℝ) : |u| ≤ gaussianEnvelope u := by
  unfold gaussianEnvelope
  linarith [abs_nonneg u]

theorem meanJacobian_kernel_difference_le (t μ v ν w u : ℝ) (k : ℕ)
    (ht : 0 ≤ t) (hμ : |μ| ≤ 2) (hν : |ν| ≤ 2)
    (hv : v ∈ Icc (1/2) 3) (hw : w ∈ Icc (1/2) 3) (hk : k ≤ 5) :
    |endpointPowerKernel t (μ+Real.sqrt v*u) k-
      endpointPowerKernel 0 (ν+Real.sqrt w*u) k| ≤
      31*gaussianEnvelope u^6*(t+|μ-ν|+|v-w|) := by
  let L := gaussianEnvelope u
  have hL : 1 ≤ L := by dsimp [L]; linarith [gaussianEnvelope_ge_two u]
  have hL0 : 0 ≤ L := by linarith
  have hu : |u| ≤ L := abs_self_le_gaussianEnvelope u
  have hy : |μ+Real.sqrt v*u| ≤ L := abs_affineGaussian_le_envelope μ v u hμ hv.2
  have hz : |ν+Real.sqrt w*u| ≤ L := abs_affineGaussian_le_envelope ν w u hν hw.2
  have hd : |(μ+Real.sqrt v*u)-(ν+Real.sqrt w*u)| ≤ |μ-ν|+L*|v-w| := by
    exact (abs_affineGaussian_sub_le μ ν v w u hv.1 hw.1).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right hu (abs_nonneg _)))
  have htime := endpointPowerKernel_time_difference_le t (μ+Real.sqrt v*u) L k ht hy hL hk
  have hspace := endpointPowerKernel_endpoint_difference_le
    (μ+Real.sqrt v*u) (ν+Real.sqrt w*u) L k hy hz hL hk
  have htriangle := abs_sub_le (endpointPowerKernel t (μ+Real.sqrt v*u) k)
    (endpointPowerKernel 0 (μ+Real.sqrt v*u) k)
    (endpointPowerKernel 0 (ν+Real.sqrt w*u) k)
  have hmul := mul_le_mul_of_nonneg_left hd (show 0 ≤ 25*L^5 by positivity)
  have h56 : L^5 ≤ L^6 := pow_le_pow_right₀ hL (by norm_num)
  have hμpow := mul_le_mul_of_nonneg_right h56 (abs_nonneg (μ-ν))
  change _ ≤ 31*L^6*(t+|μ-ν|+|v-w|)
  nlinarith [mul_nonneg (pow_nonneg hL0 6) ht,
    mul_nonneg (pow_nonneg hL0 6) (abs_nonneg (μ-ν)),
    mul_nonneg (pow_nonneg hL0 6) (abs_nonneg (v-w))]

theorem varianceJacobian_kernel_difference_le (t μ v ν w u : ℝ) (k : ℕ)
    (ht : 0 ≤ t) (hμ : |μ| ≤ 2) (hν : |ν| ≤ 2)
    (hv : v ∈ Icc (1/2) 3) (hw : w ∈ Icc (1/2) 3) (hk : k ≤ 5) :
    |endpointPowerKernel t (μ+Real.sqrt v*u) k*varianceSlope v u-
      endpointPowerKernel 0 (ν+Real.sqrt w*u) k*varianceSlope w u| ≤
      41*gaussianEnvelope u^7*(t+|μ-ν|+|v-w|) := by
  let L := gaussianEnvelope u
  let A := endpointPowerKernel t (μ+Real.sqrt v*u) k
  let B := endpointPowerKernel 0 (ν+Real.sqrt w*u) k
  let S := t+|μ-ν|+|v-w|
  have hL : 1 ≤ L := by dsimp [L]; linarith [gaussianEnvelope_ge_two u]
  have hL0 : 0 ≤ L := by linarith
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hu : |u| ≤ L := abs_self_le_gaussianEnvelope u
  have hc : |varianceSlope v u| ≤ L := (abs_varianceSlope_le v u hv.1).trans hu
  have hd : |varianceSlope v u-varianceSlope w u| ≤ 2*L*|v-w| := by
    exact (abs_varianceSlope_sub_le v w u hv.1 hw.1).trans (by gcongr)
  have hA : |A-B| ≤ 31*L^6*S :=
    meanJacobian_kernel_difference_le t μ v ν w u k ht hμ hν hv hw hk
  have hB : |B| ≤ 5*L^4 :=
    abs_endpointPowerKernel_le_envelope 0 (ν+Real.sqrt w*u) L k (by norm_num)
      (abs_affineGaussian_le_envelope ν w u hν hw.2) hL hk
  have heq : A*varianceSlope v u-B*varianceSlope w u =
      (A-B)*varianceSlope v u+B*(varianceSlope v u-varianceSlope w u) := by ring
  change |A*varianceSlope v u-B*varianceSlope w u| ≤ 41*L^7*S
  rw [heq]
  calc
    _ ≤ |(A-B)*varianceSlope v u|+|B*(varianceSlope v u-varianceSlope w u)| := abs_add_le _ _
    _ = |A-B| * |varianceSlope v u|+|B| * |varianceSlope v u-varianceSlope w u| := by
      rw [abs_mul, abs_mul]
    _ ≤ (31*L^6*S)*L+(5*L^4)*(2*L*|v-w|) := by gcongr
    _ ≤ 41*L^7*S := by
      have h57 : L^5 ≤ L^7 := pow_le_pow_right₀ hL (by norm_num)
      have hp := mul_le_mul_of_nonneg_right h57 (abs_nonneg (v-w))
      have hs : |v-w| ≤ S := by dsimp [S]; linarith [abs_nonneg (μ-ν)]
      have hp' := mul_le_mul_of_nonneg_left hs (pow_nonneg hL0 7)
      nlinarith

theorem meanJacobian_kernel_bound (t μ v u : ℝ) (k : ℕ)
    (ht : 0 ≤ t) (hμ : |μ| ≤ 2) (hv : v ≤ 3) (hk : k ≤ 5) :
    |endpointPowerKernel t (μ+Real.sqrt v*u) k| ≤ 5*gaussianEnvelope u^7 := by
  have hL : 1 ≤ gaussianEnvelope u := by linarith [gaussianEnvelope_ge_two u]
  exact (abs_endpointPowerKernel_le_envelope t (μ+Real.sqrt v*u) (gaussianEnvelope u) k
    ht (abs_affineGaussian_le_envelope μ v u hμ hv) hL hk).trans
      (mul_le_mul_of_nonneg_left (gaussianEnvelope_pow_le_seven u 4 (by norm_num)) (by norm_num))

theorem varianceJacobian_kernel_bound (t μ v u : ℝ) (k : ℕ)
    (ht : 0 ≤ t) (hμ : |μ| ≤ 2) (hv : v ∈ Icc (1/2) 3) (hk : k ≤ 5) :
    |endpointPowerKernel t (μ+Real.sqrt v*u) k*varianceSlope v u| ≤
      5*gaussianEnvelope u^7 := by
  let L := gaussianEnvelope u
  have hL : 1 ≤ L := by dsimp [L]; linarith [gaussianEnvelope_ge_two u]
  have hL0 : 0 ≤ L := by linarith
  have hA := abs_endpointPowerKernel_le_envelope t (μ+Real.sqrt v*u) L k ht
    (abs_affineGaussian_le_envelope μ v u hμ hv.2) hL hk
  have hc : |varianceSlope v u| ≤ L :=
    (abs_varianceSlope_le v u hv.1).trans (abs_self_le_gaussianEnvelope u)
  rw [abs_mul]
  calc
    _ ≤ (5*L^4)*L := mul_le_mul hA hc (abs_nonneg _) (by positivity)
    _ = 5*L^5 := by ring
    _ ≤ 5*L^7 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by norm_num)) (by norm_num)

theorem integrable_meanJacobian_kernel (t μ v : ℝ) (k : ℕ)
    (ht : 0 ≤ t) (hμ : |μ| ≤ 2) (hv : v ≤ 3) (hk : k ≤ 5) :
    Integrable (fun u => endpointPowerKernel t (μ+Real.sqrt v*u) k) standardGaussian := by
  apply (integrable_gaussianEnvelope_seven.const_mul (5 : ℝ)).mono'
  · exact ((continuous_endpointPowerKernel t k).comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards [] with u
    simpa only [Real.norm_eq_abs] using meanJacobian_kernel_bound t μ v u k ht hμ hv hk

theorem integrable_varianceJacobian_kernel (t μ v : ℝ) (k : ℕ)
    (ht : 0 ≤ t) (hμ : |μ| ≤ 2) (hv : v ∈ Icc (1/2) 3) (hk : k ≤ 5) :
    Integrable (fun u => endpointPowerKernel t (μ+Real.sqrt v*u) k*varianceSlope v u)
      standardGaussian := by
  apply (integrable_gaussianEnvelope_seven.const_mul (5 : ℝ)).mono'
  · have hc : Continuous (fun u => endpointPowerKernel t (μ+Real.sqrt v*u) k) :=
      (continuous_endpointPowerKernel t k).comp (by fun_prop)
    exact (hc.mul (by unfold varianceSlope; fun_prop)).aestronglyMeasurable
  · filter_upwards [] with u
    simpa only [Real.norm_eq_abs] using varianceJacobian_kernel_bound t μ v u k ht hμ hv hk

theorem abs_integral_le_gaussianEnvelope (f : ℝ → ℝ)
    (hf : Integrable f standardGaussian) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ u, |f u| ≤ C*gaussianEnvelope u^7) :
    |∫ u, f u ∂standardGaussian| ≤ C*876544 := by
  calc
    _ ≤ ∫ u, |f u| ∂standardGaussian := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm f
    _ ≤ ∫ u, C*gaussianEnvelope u^7 ∂standardGaussian :=
      integral_mono hf.norm (integrable_gaussianEnvelope_seven.const_mul C) hbound
    _ = C*(∫ u, gaussianEnvelope u^7 ∂standardGaussian) := integral_const_mul C _
    _ ≤ C*876544 := mul_le_mul_of_nonneg_left integral_gaussianEnvelope_seven_le hC

theorem abs_componentMeanJacobian_le (t μ v : ℝ) (k : ℕ)
    (ht : 0 ≤ t) (hμ : |μ| ≤ 2) (hv : v ≤ 3) (hk : k ≤ 5) :
    |componentMeanJacobian t μ v k| ≤ 10^8 := by
  have hi := integrable_meanJacobian_kernel t μ v k ht hμ hv hk
  have h := abs_integral_le_gaussianEnvelope _ hi 5 (by norm_num)
    (fun u => meanJacobian_kernel_bound t μ v u k ht hμ hv hk)
  unfold componentMeanJacobian
  linarith

theorem abs_componentVarianceJacobian_le (t μ v : ℝ) (k : ℕ)
    (ht : 0 ≤ t) (hμ : |μ| ≤ 2) (hv : v ∈ Icc (1/2) 3) (hk : k ≤ 5) :
    |componentVarianceJacobian t μ v k| ≤ 10^8 := by
  have hi := integrable_varianceJacobian_kernel t μ v k ht hμ hv hk
  have h := abs_integral_le_gaussianEnvelope _ hi 5 (by norm_num)
    (fun u => varianceJacobian_kernel_bound t μ v u k ht hμ hv hk)
  change |∫ u, endpointPowerKernel t (μ+Real.sqrt v*u) k*varianceSlope v u
    ∂standardGaussian| ≤ 10^8
  linarith

theorem componentMeanJacobian_difference_le (t μ v ν w : ℝ) (k : ℕ)
    (ht : 0 ≤ t) (hμ : |μ| ≤ 2) (hν : |ν| ≤ 2)
    (hv : v ∈ Icc (1/2) 3) (hw : w ∈ Icc (1/2) 3) (hk : k ≤ 5) :
    |componentMeanJacobian t μ v k-componentMeanJacobian 0 ν w k| ≤
      10^8*(t+|μ-ν|+|v-w|) := by
  let S := t+|μ-ν|+|v-w|
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hi := integrable_meanJacobian_kernel t μ v k ht hμ hv.2 hk
  have hg := integrable_meanJacobian_kernel 0 ν w k (by norm_num) hν hw.2 hk
  have hb : ∀ u, |endpointPowerKernel t (μ+Real.sqrt v*u) k-
      endpointPowerKernel 0 (ν+Real.sqrt w*u) k| ≤ (31*S)*gaussianEnvelope u^7 := by
    intro u
    have h := meanJacobian_kernel_difference_le t μ v ν w u k ht hμ hν hv hw hk
    have hp := mul_le_mul_of_nonneg_left (gaussianEnvelope_pow_le_seven u 6 (by norm_num))
      (show 0 ≤ 31*S by positivity)
    change _ ≤ (31*S)*gaussianEnvelope u^7
    dsimp [S] at *
    nlinarith
  have h := abs_integral_le_gaussianEnvelope _ (hi.sub hg) (31*S) (by positivity) hb
  simp only [Pi.sub_apply] at h
  unfold componentMeanJacobian
  rw [← integral_sub hi hg]
  change _ ≤ 10^8*S
  nlinarith

theorem componentVarianceJacobian_difference_le (t μ v ν w : ℝ) (k : ℕ)
    (ht : 0 ≤ t) (hμ : |μ| ≤ 2) (hν : |ν| ≤ 2)
    (hv : v ∈ Icc (1/2) 3) (hw : w ∈ Icc (1/2) 3) (hk : k ≤ 5) :
    |componentVarianceJacobian t μ v k-componentVarianceJacobian 0 ν w k| ≤
      10^8*(t+|μ-ν|+|v-w|) := by
  let S := t+|μ-ν|+|v-w|
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hi := integrable_varianceJacobian_kernel t μ v k ht hμ hv hk
  have hg := integrable_varianceJacobian_kernel 0 ν w k (by norm_num) hν hw hk
  have hb : ∀ u, |endpointPowerKernel t (μ+Real.sqrt v*u) k*varianceSlope v u-
      endpointPowerKernel 0 (ν+Real.sqrt w*u) k*varianceSlope w u| ≤
      (41*S)*gaussianEnvelope u^7 := by
    intro u
    have h := varianceJacobian_kernel_difference_le t μ v ν w u k ht hμ hν hv hw hk
    convert h using 1 <;> dsimp [S] <;> ring
  have h := abs_integral_le_gaussianEnvelope _ (hi.sub hg) (41*S) (by positivity) hb
  simp only [Pi.sub_apply] at h
  change |(∫ u, endpointPowerKernel t (μ+Real.sqrt v*u) k*varianceSlope v u ∂standardGaussian)-
    (∫ u, endpointPowerKernel 0 (ν+Real.sqrt w*u) k*varianceSlope w u ∂standardGaussian)| ≤ 10^8*S
  rw [← integral_sub hi hg]
  nlinarith

theorem power_endpoint_difference_le (y z L : ℝ) (k : ℕ)
    (hy : |y| ≤ L) (hz : |z| ≤ L) (hL : 1 ≤ L) (hk : k ≤ 5) :
    |y^k-z^k| ≤ 5*L^4*|y-z| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Icc (-L) L) (f := fun x => hTransform 0 x^k)
    (f' := fun x => endpointPowerKernel 0 x k) (C := 5*L^4)
    (fun x hx => (hasDerivAt_hTransform_pow 0 x k).hasDerivWithinAt)
    (fun x hx => by
      rw [Real.norm_eq_abs]
      exact abs_endpointPowerKernel_le_envelope 0 x L k (by norm_num)
        (abs_le.mpr hx) hL hk)
    (convex_Icc (-L) L) (abs_le.mp hz) (abs_le.mp hy)
  simpa only [Real.norm_eq_abs, hTransform_zero] using h

theorem componentMoment_kernel_difference_le (t μ v ν w u : ℝ) (k : ℕ)
    (ht : 0 ≤ t) (hμ : |μ| ≤ 2) (hν : |ν| ≤ 2)
    (hv : v ∈ Icc (1/2) 3) (hw : w ∈ Icc (1/2) 3) (hk : k ≤ 5) :
    |hTransform t (μ+Real.sqrt v*u)^k-hTransform 0 (ν+Real.sqrt w*u)^k| ≤
      6*gaussianEnvelope u^7*(t+|μ-ν|+|v-w|) := by
  let L := gaussianEnvelope u
  have hL : 1 ≤ L := by dsimp [L]; linarith [gaussianEnvelope_ge_two u]
  have hL0 : 0 ≤ L := by linarith
  have hu : |u| ≤ L := abs_self_le_gaussianEnvelope u
  have hy : |μ+Real.sqrt v*u| ≤ L := abs_affineGaussian_le_envelope μ v u hμ hv.2
  have hz : |ν+Real.sqrt w*u| ≤ L := abs_affineGaussian_le_envelope ν w u hν hw.2
  have hd : |(μ+Real.sqrt v*u)-(ν+Real.sqrt w*u)| ≤ |μ-ν|+L*|v-w| :=
    (abs_affineGaussian_sub_le μ ν v w u hv.1 hw.1).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right hu (abs_nonneg _)))
  have htime := abs_transform_power_sub_power_le t (μ+Real.sqrt v*u) L ht hL hy k hk
  have hspace := power_endpoint_difference_le (μ+Real.sqrt v*u) (ν+Real.sqrt w*u)
    L k hy hz hL hk
  have htriangle := abs_sub_le (hTransform t (μ+Real.sqrt v*u)^k)
    ((μ+Real.sqrt v*u)^k) ((ν+Real.sqrt w*u)^k)
  have hmul := mul_le_mul_of_nonneg_left hd (show 0 ≤ 5*L^4 by positivity)
  have h47 := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL (show 4 ≤ 7 by omega))
    (abs_nonneg (μ-ν))
  have h57 := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL (show 5 ≤ 7 by omega))
    (abs_nonneg (v-w))
  rw [hTransform_zero]
  change _ ≤ 6*L^7*(t+|μ-ν|+|v-w|)
  nlinarith [mul_nonneg (pow_nonneg hL0 7) ht,
    mul_nonneg (pow_nonneg hL0 7) (abs_nonneg (μ-ν)),
    mul_nonneg (pow_nonneg hL0 7) (abs_nonneg (v-w))]

theorem transformedComponentMoment_difference_le (t μ v ν w : ℝ) (k : ℕ)
    (ht : 0 ≤ t) (hμ : |μ| ≤ 2) (hν : |ν| ≤ 2)
    (hv : v ∈ Icc (1/2) 3) (hw : w ∈ Icc (1/2) 3) (hk : k ≤ 5) :
    |transformedComponentMoment t μ v k-transformedComponentMoment 0 ν w k| ≤
      10^8*(t+|μ-ν|+|v-w|) := by
  let S := t+|μ-ν|+|v-w|
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hi := integrable_transformed_affine_pow t μ v k ht (by linarith [hv.1])
  have hg := integrable_transformed_affine_pow 0 ν w k (by norm_num) (by linarith [hw.1])
  have hb : ∀ u, |hTransform t (μ+Real.sqrt v*u)^k-hTransform 0 (ν+Real.sqrt w*u)^k| ≤
      (6*S)*gaussianEnvelope u^7 := by
    intro u
    have h := componentMoment_kernel_difference_le t μ v ν w u k ht hμ hν hv hw hk
    convert h using 1 <;> dsimp [S] <;> ring
  have h := abs_integral_le_gaussianEnvelope _ (hi.sub hg) (6*S) (by positivity) hb
  simp only [Pi.sub_apply] at h
  unfold transformedComponentMoment
  rw [← integral_sub hi hg]
  change _ ≤ 10^8*S
  nlinarith

theorem weighted_scalar_difference_le (a b x y C S : ℝ)
    (ha : |a| ≤ 1) (hxy : |x-y| ≤ C*S) (hy : |y| ≤ C)
    (hC : 0 ≤ C) (hS : 0 ≤ S) :
    |a*x-b*y| ≤ C*(S+|a-b|) := by
  have heq : a*x-b*y = a*(x-y)+(a-b)*y := by ring
  rw [heq]
  calc
    _ ≤ |a*(x-y)|+|(a-b)*y| := abs_add_le _ _
    _ = |a| * |x-y|+|a-b| * |y| := by rw [abs_mul, abs_mul]
    _ ≤ 1*(C*S)+|a-b| * C := by gcongr
    _ = _ := by ring

theorem abs_coordinate_difference_le_sum (θ η : GaussianSpace) (j : Fin 5) :
    |θ j-η j| ≤ ∑ r : Fin 5, |θ r-η r| := by
  exact Finset.single_le_sum (fun r hr => abs_nonneg (θ r-η r)) (Finset.mem_univ j)

/-- Uniform entrywise stability of the actual five-moment Jacobian. -/
theorem momentJacobianEntry_difference_le (t : ℝ) (θ η : GaussianSpace) (k : ℕ) (j : Fin 5)
    (ht : 0 ≤ t) (hθ : PaperBox θ) (hη : PaperBox η) (hk : k ≤ 5) :
    |momentJacobianEntry t θ k j-momentJacobianEntry 0 η k j| ≤
      10^9*(t+∑ r : Fin 5, |θ r-η r|) := by
  let D := ∑ r : Fin 5, |θ r-η r|
  have hD : 0 ≤ D := Finset.sum_nonneg (fun r hr => abs_nonneg _)
  have hd : ∀ r, |θ r-η r| ≤ D := fun r => abs_coordinate_difference_le_sum θ η r
  have hweight : |θ 0| ≤ 1 := by
    rw [abs_of_nonneg (by linarith [hθ.weight_mem.1] : 0 ≤ θ 0)]
    linarith [hθ.weight_mem.2]
  have hweightc : |1-θ 0| ≤ 1 := by
    rw [abs_of_nonneg (by linarith [hθ.weight_mem.2] : 0 ≤ 1-θ 0)]
    linarith [hθ.weight_mem.1]
  have hwd : |(1-θ 0)-(1-η 0)| = |θ 0-η 0| := by
    have heq : (1-θ 0)-(1-η 0) = -(θ 0-η 0) := by ring
    rw [heq, abs_neg]
  have hc0 := transformedComponentMoment_difference_le t (θ 1) (θ 3) (η 1) (η 3) k
    ht hθ.mean0_abs hη.mean0_abs hθ.variance0_mem hη.variance0_mem hk
  have hc1 := transformedComponentMoment_difference_le t (θ 2) (θ 4) (η 2) (η 4) k
    ht hθ.mean1_abs hη.mean1_abs hθ.variance1_mem hη.variance1_mem hk
  have hm0 := componentMeanJacobian_difference_le t (θ 1) (θ 3) (η 1) (η 3) k
    ht hθ.mean0_abs hη.mean0_abs hθ.variance0_mem hη.variance0_mem hk
  have hm1 := componentMeanJacobian_difference_le t (θ 2) (θ 4) (η 2) (η 4) k
    ht hθ.mean1_abs hη.mean1_abs hθ.variance1_mem hη.variance1_mem hk
  have hv0 := componentVarianceJacobian_difference_le t (θ 1) (θ 3) (η 1) (η 3) k
    ht hθ.mean0_abs hη.mean0_abs hθ.variance0_mem hη.variance0_mem hk
  have hv1 := componentVarianceJacobian_difference_le t (θ 2) (θ 4) (η 2) (η 4) k
    ht hθ.mean1_abs hη.mean1_abs hθ.variance1_mem hη.variance1_mem hk
  have hbm0 := abs_componentMeanJacobian_le 0 (η 1) (η 3) k
    (by norm_num) hη.mean0_abs hη.variance0_mem.2 hk
  have hbm1 := abs_componentMeanJacobian_le 0 (η 2) (η 4) k
    (by norm_num) hη.mean1_abs hη.variance1_mem.2 hk
  have hbv0 := abs_componentVarianceJacobian_le 0 (η 1) (η 3) k
    (by norm_num) hη.mean0_abs hη.variance0_mem hk
  have hbv1 := abs_componentVarianceJacobian_le 0 (η 2) (η 4) k
    (by norm_num) hη.mean1_abs hη.variance1_mem hk
  have hw0 := weighted_scalar_difference_le (1-θ 0) (1-η 0) _ _ (10^8)
    (t+|θ 1-η 1|+|θ 3-η 3|) hweightc hm0 hbm0 (by positivity) (by positivity)
  have hw1 := weighted_scalar_difference_le (θ 0) (η 0) _ _ (10^8)
    (t+|θ 2-η 2|+|θ 4-η 4|) hweight hm1 hbm1 (by positivity) (by positivity)
  have hw2 := weighted_scalar_difference_le (1-θ 0) (1-η 0) _ _ (10^8)
    (t+|θ 1-η 1|+|θ 3-η 3|) hweightc hv0 hbv0 (by positivity) (by positivity)
  have hw3 := weighted_scalar_difference_le (θ 0) (η 0) _ _ (10^8)
    (t+|θ 2-η 2|+|θ 4-η 4|) hweight hv1 hbv1 (by positivity) (by positivity)
  rw [hwd] at hw0 hw2
  have hd0 := hd 0
  have hd1 := hd 1
  have hd2 := hd 2
  have hd3 := hd 3
  have hd4 := hd 4
  fin_cases j
  · change |(transformedComponentMoment t (θ 2) (θ 4) k-
        transformedComponentMoment t (θ 1) (θ 3) k)-
      (transformedComponentMoment 0 (η 2) (η 4) k-
        transformedComponentMoment 0 (η 1) (η 3) k)| ≤ 10^9*(t+D)
    have heq : (transformedComponentMoment t (θ 2) (θ 4) k-
        transformedComponentMoment t (θ 1) (θ 3) k)-
      (transformedComponentMoment 0 (η 2) (η 4) k-
        transformedComponentMoment 0 (η 1) (η 3) k) =
      (transformedComponentMoment t (θ 2) (θ 4) k-
        transformedComponentMoment 0 (η 2) (η 4) k)-
      (transformedComponentMoment t (θ 1) (θ 3) k-
        transformedComponentMoment 0 (η 1) (η 3) k) := by ring
    rw [heq]
    have htriangle := abs_sub_le
      (transformedComponentMoment t (θ 2) (θ 4) k-transformedComponentMoment 0 (η 2) (η 4) k)
      0 (transformedComponentMoment t (θ 1) (θ 3) k-transformedComponentMoment 0 (η 1) (η 3) k)
    simp only [sub_zero, zero_sub, abs_neg] at htriangle
    nlinarith
  · change |(1-θ 0)*componentMeanJacobian t (θ 1) (θ 3) k-
      (1-η 0)*componentMeanJacobian 0 (η 1) (η 3) k| ≤ 10^9*(t+D)
    nlinarith
  · change |θ 0*componentMeanJacobian t (θ 2) (θ 4) k-
      η 0*componentMeanJacobian 0 (η 2) (η 4) k| ≤ 10^9*(t+D)
    nlinarith
  · change |(1-θ 0)*componentVarianceJacobian t (θ 1) (θ 3) k-
      (1-η 0)*componentVarianceJacobian 0 (η 1) (η 3) k| ≤ 10^9*(t+D)
    nlinarith
  · change |θ 0*componentVarianceJacobian t (θ 2) (θ 4) k-
      η 0*componentVarianceJacobian 0 (η 2) (η 4) k| ≤ 10^9*(t+D)
    nlinarith

end LCR
