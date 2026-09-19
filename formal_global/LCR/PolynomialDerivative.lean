import LCR.GaussianJacobian

namespace LCR.AlgebraicSeed

noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

def mixtureMomentMap (x : Fin 5 → ℝ) (i : Fin 5) : ℝ :=
  mixtureMomentPolynomial (x 0) (x 1) (x 2) (x 3) (x 4) (i.val+1)

def gaussianJacobianCLM (x : Fin 5 → ℝ) : (Fin 5 → ℝ) →L[ℝ] (Fin 5 → ℝ) :=
  ContinuousLinearMap.pi fun i => ∑ j : Fin 5,
    gaussianMomentJacobian (x 0) (x 1) (x 2) (x 3) (x 4) i j • ContinuousLinearMap.proj j

theorem hasFDerivAt_mixtureMomentMap (x : Fin 5 → ℝ) :
    HasFDerivAt mixtureMomentMap (gaussianJacobianCLM x) x := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 5) x
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 5) x
  have h2 := hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 5) x
  have h3 := hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin 5) x
  have h4 := hasFDerivAt_apply (𝕜 := ℝ) (4 : Fin 5) x
  have hw := (hasFDerivAt_const (1 : ℝ) x).sub h0
  unfold mixtureMomentMap gaussianJacobianCLM
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · have h := (hw.mul h1).add (h0.mul h2)
    convert h using 1 <;> ext y <;>
      simp [mixtureMomentPolynomial, normalMomentPolynomial, gaussianMomentJacobian,
        Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
        Matrix.vecHead, Matrix.vecTail] <;> ring
  · have ha := (h1.pow 2).add h3
    have hb := (h2.pow 2).add h4
    have h := (hw.mul ha).add (h0.mul hb)
    convert h using 1 <;> ext y <;>
      simp [mixtureMomentPolynomial, normalMomentPolynomial, gaussianMomentJacobian,
        Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
        Matrix.vecHead, Matrix.vecTail] <;> ring
  · have ha := (h1.pow 3).add ((h1.const_mul 3).mul h3)
    have hb := (h2.pow 3).add ((h2.const_mul 3).mul h4)
    have h := (hw.mul ha).add (h0.mul hb)
    convert h using 1 <;> ext y <;>
      simp [mixtureMomentPolynomial, normalMomentPolynomial, gaussianMomentJacobian,
        Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
        Matrix.vecHead, Matrix.vecTail] <;> ring
  · have ha := ((h1.pow 4).add (((h1.pow 2).const_mul 6).mul h3)).add ((h3.pow 2).const_mul 3)
    have hb := ((h2.pow 4).add (((h2.pow 2).const_mul 6).mul h4)).add ((h4.pow 2).const_mul 3)
    have h := (hw.mul ha).add (h0.mul hb)
    convert h using 1 <;> ext y <;>
      simp [mixtureMomentPolynomial, normalMomentPolynomial, gaussianMomentJacobian,
        Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
        Matrix.vecHead, Matrix.vecTail] <;> ring
  · have ha := ((h1.pow 5).add (((h1.pow 3).const_mul 10).mul h3)).add ((h1.const_mul 15).mul (h3.pow 2))
    have hb := ((h2.pow 5).add (((h2.pow 3).const_mul 10).mul h4)).add ((h2.const_mul 15).mul (h4.pow 2))
    have h := (hw.mul ha).add (h0.mul hb)
    convert h using 1 <;> ext y <;>
      simp [mixtureMomentPolynomial, normalMomentPolynomial, gaussianMomentJacobian,
        Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
        Matrix.vecHead, Matrix.vecTail] <;> ring

end
end LCR.AlgebraicSeed
