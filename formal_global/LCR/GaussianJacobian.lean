import LCR.AlgebraicSeed

namespace LCR.AlgebraicSeed

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def gaussianMomentJacobian (w a b va vb : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![ b-a, 1-w, w, 0, 0;
      b^2+vb-a^2-va, 2*(1-w)*a, 2*w*b, 1-w, w;
      b^3+3*b*vb-a^3-3*a*va, 3*(1-w)*(a^2+va), 3*w*(b^2+vb),
        3*(1-w)*a, 3*w*b;
      b^4+6*b^2*vb+3*vb^2-a^4-6*a^2*va-3*va^2,
        4*(1-w)*(a^3+3*a*va), 4*w*(b^3+3*b*vb),
        6*(1-w)*(a^2+va), 6*w*(b^2+vb);
      b^5+10*b^3*vb+15*b*vb^2-a^5-10*a^3*va-15*a*va^2,
        5*(1-w)*(a^4+6*a^2*va+3*va^2), 5*w*(b^4+6*b^2*vb+3*vb^2),
        10*(1-w)*(a^3+3*a*va), 10*w*(b^3+3*b*vb) ]

def gaussianRowTransform (a v : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![ 1, 0, 0, 0, 0;
      -2*a, 1, 0, 0, 0;
      3*a^2-3*v, -3*a, 1, 0, 0;
      -4*a^3+12*a*v, 6*a^2-6*v, -4*a, 1, 0;
      5*a^4-30*a^2*v+15*v^2, -10*a^3+30*a*v, 10*a^2-10*v, -5*a, 1 ]

theorem gaussianRowTransform_det (a v : ℝ) : (gaussianRowTransform a v).det = 1 := by
  have ht : (gaussianRowTransform a v).BlockTriangular OrderDual.toDual := by
    intro i j hij
    change i < j at hij
    fin_cases i <;> fin_cases j <;> norm_num [gaussianRowTransform] at *
  rw [Matrix.det_of_lowerTriangular _ ht]
  norm_num [Fin.prod_univ_succ, gaussianRowTransform]

theorem gaussianRowTransform_mul (w a b va vb : ℝ) :
    gaussianRowTransform a va * gaussianMomentJacobian w a b va vb =
      gaussianMomentJacobian w 0 (b-a) 0 (vb-va) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gaussianRowTransform, gaussianMomentJacobian, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem gaussianMomentJacobian_normalized_det (w d t : ℝ) :
    (gaussianMomentJacobian w 0 d 0 t).det =
      -w^2*(1-w)^2*d*(d^8+18*d^4*t^2-135*t^4) := by
  unfold gaussianMomentJacobian
  rw [Matrix.det_succ_column _ (1 : Fin 5)]
  norm_num [Fin.sum_univ_succ, Matrix.submatrix_apply, Fin.succAbove, Fin.lt_def, Fin.ext_iff,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]
  rw [Matrix.det_succ_column _ (2 : Fin 4)]
  norm_num [Fin.sum_univ_succ, Matrix.submatrix_apply, Fin.succAbove, Fin.lt_def, Fin.ext_iff,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]
  rw [Matrix.det_fin_three]
  norm_num [Matrix.submatrix_apply, Fin.succAbove, Fin.lt_def, Fin.ext_iff,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]
  ring

theorem gaussianMomentJacobian_det (w a b va vb : ℝ) :
    (gaussianMomentJacobian w a b va vb).det =
      -w^2*(1-w)^2*(b-a)*((b-a)^8+18*(b-a)^4*(vb-va)^2-135*(vb-va)^4) := by
  have hd := congrArg Matrix.det (gaussianRowTransform_mul w a b va vb)
  rw [Matrix.det_mul, gaussianRowTransform_det, one_mul,
    gaussianMomentJacobian_normalized_det] at hd
  exact hd

theorem mean_difference (p : ℝ) : mu1Of p-mu0Of p = deltaOf p := by
  unfold mu1Of mu0Of
  ring

theorem variance_difference (p : ℝ) :
    variance1Of p-variance0Of p = cOf p*deltaOf p := by
  unfold variance1Of variance0Of
  rw [show 5/2-p+cOf p*mu1Of p-(5/2-p+cOf p*mu0Of p) =
    cOf p*(mu1Of p-mu0Of p) by ring]
  rw [mean_difference]

theorem seed_orientation_neg {p : ℝ} (hlo : 634 / 1000 < p) (hhi : p < 635 / 1000) :
    (mu1Of p-mu0Of p)^8+
      18*(mu1Of p-mu0Of p)^4*(variance1Of p-variance0Of p)^2-
      135*(variance1Of p-variance0Of p)^4 < 0 := by
  rw [mean_difference, variance_difference]
  have hc := cOf_bounds hlo hhi
  have hd := deltaOf_bounds hlo hhi
  have hcpos : 0 < cOf p := by linarith [hc.1]
  have hdpos : 0 < deltaOf p := by linarith [hd.1]
  have hc2 : (cOf p)^2 < 5/4 := by nlinarith [hc.1,hc.2]
  have hc4 : 1 < (cOf p)^4 := by nlinarith [sq_nonneg ((cOf p)^2-1),hc.1]
  have hd2 : (deltaOf p)^2 < 4 := by nlinarith [hd.1,hd.2]
  have hd4 : (deltaOf p)^4 < 16 := by nlinarith [sq_nonneg ((deltaOf p)^2-4)]
  have hc2pos : 0 < (cOf p)^2 := sq_pos_of_pos hcpos
  have hprod : (deltaOf p)^2*(cOf p)^2 < 5 := by
    nlinarith [mul_pos (sub_pos.mpr hd2) hc2pos]
  have hbrace : (deltaOf p)^4+18*(deltaOf p)^2*(cOf p)^2-135*(cOf p)^4 < 0 := by
    nlinarith only [hd4,hprod,hc4]
  have hd4pos : 0 < (deltaOf p)^4 := pow_pos hdpos _
  have hmul := mul_neg_of_pos_of_neg hd4pos hbrace
  convert hmul using 1 <;> ring

theorem algebraic_seed_det_pos :
    0 < (gaussianMomentJacobian (piOf pStar) (mu0Of pStar) (mu1Of pStar)
      (variance0Of pStar) (variance1Of pStar)).det := by
  rw [gaussianMomentJacobian_det]
  have hw := piOf_bounds pStar_spec.1 pStar_spec.2.1
  have hw0 : 0 < piOf pStar := by linarith [hw.1]
  have hw1 : 0 < 1-piOf pStar := by linarith [hw.2]
  have hd : 0 < mu1Of pStar-mu0Of pStar := by
    rw [mean_difference]
    linarith [(deltaOf_bounds pStar_spec.1 pStar_spec.2.1).1]
  have ho := seed_orientation_neg pStar_spec.1 pStar_spec.2.1
  have hp : 0 < (piOf pStar)^2*(1-piOf pStar)^2*(mu1Of pStar-mu0Of pStar) := by positivity
  nlinarith only [mul_neg_of_pos_of_neg hp ho]

theorem algebraic_seed_det_ne_zero :
    (gaussianMomentJacobian (piOf pStar) (mu0Of pStar) (mu1Of pStar)
      (variance0Of pStar) (variance1Of pStar)).det ≠ 0 :=
  ne_of_gt algebraic_seed_det_pos

theorem rational_seed_det :
    (gaussianMomentJacobian (1/2) (-1) 1 1 2).det = -(818/16) := by
  rw [gaussianMomentJacobian_det]
  norm_num

end
end LCR.AlgebraicSeed
