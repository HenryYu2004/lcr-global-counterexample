import LCR.ComponentDifferentiation

/-! The entries of the actual transformed-moment Jacobian, as Gaussian
integrals. Derivative and stability theorems are proved in separate files. -/

open MeasureTheory ProbabilityTheory

noncomputable section
namespace LCR

def componentMeanJacobian (t μ v : ℝ) (k : ℕ) : ℝ :=
  ∫ u, endpointPowerKernel t (μ+Real.sqrt v*u) k ∂standardGaussian

def componentVarianceJacobian (t μ v : ℝ) (k : ℕ) : ℝ :=
  ∫ u, endpointPowerKernel t (μ+Real.sqrt v*u) k * (u/(2*Real.sqrt v))
    ∂standardGaussian

def momentJacobianEntry (t : ℝ) (θ : GaussianSpace) (k : ℕ) (j : Fin 5) : ℝ :=
  (![transformedComponentMoment t (θ 2) (θ 4) k-
        transformedComponentMoment t (θ 1) (θ 3) k,
      (1-θ 0)*componentMeanJacobian t (θ 1) (θ 3) k,
      θ 0*componentMeanJacobian t (θ 2) (θ 4) k,
      (1-θ 0)*componentVarianceJacobian t (θ 1) (θ 3) k,
      θ 0*componentVarianceJacobian t (θ 2) (θ 4) k] : Fin 5 → ℝ) j

end LCR
