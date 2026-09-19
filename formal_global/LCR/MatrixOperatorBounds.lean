import LCR.CorrectionAssembly

/-! Entrywise bounds imply max-norm operator bounds in five dimensions. -/

noncomputable section
open scoped BigOperators
namespace LCR

def fiveMatrixOperator (A : Fin 5 → Fin 5 → ℝ) : GaussianOperator :=
  ContinuousLinearMap.pi fun i => ∑ j : Fin 5, A i j • ContinuousLinearMap.proj j

theorem fiveMatrixOperator_apply (A : Fin 5 → Fin 5 → ℝ) (x : GaussianSpace) (i : Fin 5) :
    fiveMatrixOperator A x i = ∑ j : Fin 5, A i j*x j := by
  simp [fiveMatrixOperator]

theorem norm_fiveMatrixOperator_le (A : Fin 5 → Fin 5 → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hA : ∀ i j, |A i j| ≤ B) : ‖fiveMatrixOperator A‖ ≤ 5*B := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [fiveMatrixOperator_apply]
  calc
    ‖∑ j : Fin 5, A i j*x j‖ ≤ ∑ j : Fin 5, ‖A i j*x j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 5, B*‖x‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul (hA i j) (norm_le_pi_norm x j) (norm_nonneg _) hB
    _ = 5*B*‖x‖ := by simp; ring

theorem fiveMatrixOperator_sub (A B : Fin 5 → Fin 5 → ℝ) :
    fiveMatrixOperator A-fiveMatrixOperator B = fiveMatrixOperator (fun i j => A i j-B i j) := by
  apply ContinuousLinearMap.ext
  intro x
  funext i
  simp only [ContinuousLinearMap.sub_apply, Pi.sub_apply, fiveMatrixOperator_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem norm_fiveMatrixOperator_sub_le (A B : Fin 5 → Fin 5 → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hAB : ∀ i j, |A i j-B i j| ≤ C) :
    ‖fiveMatrixOperator A-fiveMatrixOperator B‖ ≤ 5*C := by
  rw [fiveMatrixOperator_sub]
  exact norm_fiveMatrixOperator_le _ C hC hAB

end LCR
