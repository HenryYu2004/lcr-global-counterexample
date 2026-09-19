import LCR.JacobianEntries
import LCR.PolynomialDerivative

/-! The genuine Fréchet derivative of the five transformed Gaussian moments.
The zero-time derivative is identified with the exact polynomial Jacobian
by uniqueness of derivatives, not by an unproved symbolic identification. -/

open MeasureTheory Filter
open scoped Topology BigOperators

noncomputable section
namespace LCR

theorem integrable_componentMeanKernel (t μ v : ℝ) (k : ℕ) (ht : 0 ≤ t) :
    Integrable (fun u => endpointPowerKernel t (μ + Real.sqrt v * u) k)
      standardGaussian := by
  have h := (integrable_affinePairDerivative t (μ, Real.sqrt v) k ht).apply_continuousLinearMap
    (1, 0)
  simpa [affinePairDerivative] using h

theorem integrable_componentVarianceKernel (t μ v : ℝ) (k : ℕ) (ht : 0 ≤ t) :
    Integrable (fun u => endpointPowerKernel t (μ + Real.sqrt v * u) k *
      (u / (2 * Real.sqrt v))) standardGaussian := by
  have h := (integrable_affinePairDerivative t (μ, Real.sqrt v) k ht).apply_continuousLinearMap
    (0, 1)
  have h' : Integrable (fun u => endpointPowerKernel t (μ + Real.sqrt v * u) k * u)
      standardGaussian := by simpa [affinePairDerivative] using h
  simpa only [div_eq_mul_inv, mul_assoc] using h'.mul_const ((2 * Real.sqrt v)⁻¹)

theorem integral_componentParameterDerivative_eq (t : ℝ) (a v : Fin 5) (k : ℕ)
    (θ : GaussianSpace) (ht : 0 ≤ t) :
    (∫ u, componentParameterDerivative t a v k θ u ∂standardGaussian) =
      componentMeanJacobian t (θ a) (θ v) k • ContinuousLinearMap.proj a +
        componentVarianceJacobian t (θ a) (θ v) k • ContinuousLinearMap.proj v := by
  ext d
  rw [ContinuousLinearMap.integral_apply (integrable_componentParameterDerivative t a v k θ ht)]
  simp only [componentParameterDerivative_apply, mul_add, ← mul_assoc]
  rw [integral_add
    ((integrable_componentMeanKernel t (θ a) (θ v) k ht).mul_const (d a))
    ((integrable_componentVarianceKernel t (θ a) (θ v) k ht).mul_const (d v)),
    integral_mul_const, integral_mul_const]
  simp [componentMeanJacobian, componentVarianceJacobian]

/-- Actual Jacobian, represented by its five explicitly integrated entries. -/
def HJacobian (t : ℝ) (θ : GaussianSpace) : GaussianSpace →L[ℝ] GaussianSpace :=
  ContinuousLinearMap.pi fun i => ∑ j : Fin 5,
    momentJacobianEntry t θ (i.val + 1) j • ContinuousLinearMap.proj j

theorem HJacobian_apply (t : ℝ) (θ d : GaussianSpace) (i : Fin 5) :
    HJacobian t θ d i = ∑ j : Fin 5, momentJacobianEntry t θ (i.val + 1) j * d j := by
  simp [HJacobian]

theorem hasFDerivAt_H (t : ℝ) (θ : GaussianSpace) (ht : 0 ≤ t)
    (hv0 : 0 < θ 3) (hv1 : 0 < θ 4) : HasFDerivAt (H t) (HJacobian t θ) θ := by
  have hw := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 5) θ
  have hw0 := (hasFDerivAt_const (1 : ℝ) θ).sub hw
  unfold H HJacobian
  apply hasFDerivAt_pi.mpr
  intro i
  have h0 := hasFDerivAt_transformedComponentMoment_parameters t 1 3 (i.val + 1) θ ht hv0
  have h1 := hasFDerivAt_transformedComponentMoment_parameters t 2 4 (i.val + 1) θ ht hv1
  rw [integral_componentParameterDerivative_eq t 1 3 (i.val + 1) θ ht] at h0
  rw [integral_componentParameterDerivative_eq t 2 4 (i.val + 1) θ ht] at h1
  have h := (hw0.mul h0).add (hw.mul h1)
  convert h using 1
  ext d
  simp [momentJacobianEntry, Fin.sum_univ_succ]
  ring

theorem H_zero_eq_mixtureMomentMap (θ : GaussianSpace)
    (hv0 : 0 ≤ θ 3) (hv1 : 0 ≤ θ 4) : H 0 θ = AlgebraicSeed.mixtureMomentMap θ := by
  ext i
  rw [H_zero]
  exact gaussianMixtureMoment_polynomial θ hv0 hv1 (i.val + 1) (by omega)

theorem H_zero_eventuallyEq_mixtureMomentMap (θ : GaussianSpace)
    (hv0 : 0 < θ 3) (hv1 : 0 < θ 4) :
    H 0 =ᶠ[𝓝 θ] AlgebraicSeed.mixtureMomentMap := by
  have h0 : ∀ᶠ η : GaussianSpace in 𝓝 θ, 0 < η 3 :=
    (continuous_apply 3).continuousAt.eventually (eventually_gt_nhds hv0)
  have h1 : ∀ᶠ η : GaussianSpace in 𝓝 θ, 0 < η 4 :=
    (continuous_apply 4).continuousAt.eventually (eventually_gt_nhds hv1)
  filter_upwards [h0, h1] with η hη0 hη1
  exact H_zero_eq_mixtureMomentMap η hη0.le hη1.le

/-- The polynomial matrix is the actual Gaussian-integral derivative at
every positive-variance parameter, hence in particular at the exact seed. -/
theorem HJacobian_zero_eq_gaussianJacobianCLM (θ : GaussianSpace)
    (hv0 : 0 < θ 3) (hv1 : 0 < θ 4) :
    HJacobian 0 θ = AlgebraicSeed.gaussianJacobianCLM θ := by
  exact (hasFDerivAt_H 0 θ le_rfl hv0 hv1).unique
    ((AlgebraicSeed.hasFDerivAt_mixtureMomentMap θ).congr_of_eventuallyEq
      (H_zero_eventuallyEq_mixtureMomentMap θ hv0 hv1))

theorem HJacobian_zero_gaussianSeedB :
    HJacobian 0 gaussianSeedB = AlgebraicSeed.gaussianJacobianCLM gaussianSeedB :=
  HJacobian_zero_eq_gaussianJacobianCLM gaussianSeedB
    gaussianSeedB_variances_pos.1 gaussianSeedB_variances_pos.2

end LCR
