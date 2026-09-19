import LCR.GaussianJacobian
import LCR.PolynomialDerivative

namespace LCR.AlgebraicSeed

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

def seedParameters : Fin 5 → ℝ :=
  ![piOf pStar, mu0Of pStar, mu1Of pStar, variance0Of pStar, variance1Of pStar]

def seedJacobian : Matrix (Fin 5) (Fin 5) ℝ :=
  gaussianMomentJacobian (piOf pStar) (mu0Of pStar) (mu1Of pStar)
    (variance0Of pStar) (variance1Of pStar)

def seedJinv : (Fin 5 → ℝ) →L[ℝ] (Fin 5 → ℝ) :=
  (Matrix.toLin' seedJacobian⁻¹).toContinuousLinearMap

theorem seedJacobian_isUnit : IsUnit seedJacobian.det := by
  exact isUnit_iff_ne_zero.mpr algebraic_seed_det_ne_zero

theorem seedJinv_apply (x : Fin 5 → ℝ) : seedJinv x = seedJacobian⁻¹.mulVec x := rfl

theorem gaussianJacobianCLM_apply (x y : Fin 5 → ℝ) :
    gaussianJacobianCLM x y =
      (gaussianMomentJacobian (x 0) (x 1) (x 2) (x 3) (x 4)).mulVec y := by
  ext i
  simp [gaussianJacobianCLM, Matrix.mulVec, dotProduct]

theorem seedJinv_left_inverse (x : Fin 5 → ℝ) :
    seedJinv (seedJacobian.mulVec x) = x := by
  rw [seedJinv_apply, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ seedJacobian_isUnit]
  simp

theorem seedJinv_right_inverse (x : Fin 5 → ℝ) :
    seedJacobian.mulVec (seedJinv x) = x := by
  rw [seedJinv_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ seedJacobian_isUnit]
  simp

theorem seedJacobianCLM_apply (x : Fin 5 → ℝ) :
    gaussianJacobianCLM seedParameters x = seedJacobian.mulVec x := by
  rw [gaussianJacobianCLM_apply]
  simp [seedParameters,seedJacobian,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail]

theorem seedJinv_comp_Jacobian :
    seedJinv.comp (gaussianJacobianCLM seedParameters) = ContinuousLinearMap.id ℝ (Fin 5 → ℝ) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,
    seedJacobianCLM_apply,seedJinv_left_inverse]

theorem seedJacobian_comp_Jinv :
    (gaussianJacobianCLM seedParameters).comp seedJinv = ContinuousLinearMap.id ℝ (Fin 5 → ℝ) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,
    seedJacobianCLM_apply,seedJinv_right_inverse]

theorem seedJinv_injective : Function.Injective seedJinv := by
  intro x y h
  have := congrArg seedJacobian.mulVec h
  simpa only [seedJinv_right_inverse] using this

def coreMatrix (d t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![d^3+3*d*t, 3*d^2+3*t, 3*d;
      d^4+6*d^2*t+3*t^2, 4*d^3+12*d*t, 6*d^2+6*t;
      d^5+10*d^3*t+15*d*t^2, 5*d^4+30*d^2*t+15*t^2, 10*d^3+30*d*t]

theorem coreMatrix_det (d t : ℝ) :
    (coreMatrix d t).det = d*(d^8+18*d^4*t^2-135*t^4) := by
  rw [Matrix.det_fin_three]
  norm_num [coreMatrix, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  ring

def coreAdjugate (d t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![10*d^6+30*d^4*t+90*d^2*t^2-90*t^3,
       -15*d^5-30*d^3*t-45*d*t^2, 6*d^4+18*t^2;
     -4*d^7-24*d^5*t-60*d^3*t^2,
       7*d^6+30*d^4*t+45*d^2*t^2, -3*d^5-6*d^3*t-9*d*t^2;
     d^8+8*d^6*t+30*d^4*t^2+45*t^4,
       -2*d^7-12*d^5*t-30*d^3*t^2, d^6+3*d^4*t+9*d^2*t^2-9*t^3]

theorem coreMatrix_adjugate (d t : ℝ) :
    (coreMatrix d t).adjugate = coreAdjugate d t := by
  rw [Matrix.adjugate_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coreMatrix, coreAdjugate, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] <;> ring

theorem core_adjugate_entry_bound {d t : ℝ} (hd0 : 0 ≤ d) (hd2 : d ≤ 2)
    (ht0 : 0 ≤ t) (ht2 : t ≤ 2) (i j : Fin 3) :
    |(coreMatrix d t).adjugate i j| ≤ 4000 := by
  have hm (k l : ℕ) : 0 ≤ d^k*t^l ∧ d^k*t^l ≤ 2^(k+l) := by
    constructor
    · positivity
    · calc
        d^k*t^l ≤ (2:ℝ)^k*2^l := by gcongr
        _ = _ := by rw [pow_add]
  have h60 := hm 6 0
  have h41 := hm 4 1
  have h22 := hm 2 2
  have h03 := hm 0 3
  have h50 := hm 5 0
  have h31 := hm 3 1
  have h12 := hm 1 2
  have h40 := hm 4 0
  have h02 := hm 0 2
  have h70 := hm 7 0
  have h51 := hm 5 1
  have h32 := hm 3 2
  have h80 := hm 8 0
  have h61 := hm 6 1
  have h42 := hm 4 2
  have h04 := hm 0 4
  norm_num at h60 h41 h22 h03 h50 h31 h12 h40 h02 h70 h51 h32 h80 h61 h42 h04
  rw [coreMatrix_adjugate]
  fin_cases i <;> fin_cases j <;>
    norm_num [coreAdjugate, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] <;>
    apply abs_le.mpr <;> constructor <;>
    nlinarith only [h60.1,h60.2,h41.1,h41.2,h22.1,h22.2,h03.1,h03.2,
      h50.1,h50.2,h31.1,h31.2,h12.1,h12.2,h40.1,h40.2,h02.1,h02.2,
      h70.1,h70.2,h51.1,h51.2,h32.1,h32.2,h80.1,h80.2,h61.1,h61.2,
      h42.1,h42.2,h04.1,h04.2]

theorem norm_mulVec_le_entry_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hA : ∀ i j, |A i j| ≤ B) (x : Fin n → ℝ) :
    ‖A.mulVec x‖ ≤ n*B*‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  change ‖∑ j : Fin n, A i j*x j‖ ≤ _
  calc
    _ ≤ ∑ j : Fin n, ‖A i j*x j‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin n, B*‖x‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul (hA i j) (norm_le_pi_norm x j) (norm_nonneg _) hB
    _ = _ := by simp; ring

theorem core_solve_bound {d t : ℝ} (hd0 : 0 ≤ d) (hd2 : d ≤ 2)
    (ht0 : 0 ≤ t) (ht2 : t ≤ 2) (hdet : 300 ≤ |(coreMatrix d t).det|)
    (z : Fin 3 → ℝ) : ‖z‖ ≤ 40*‖(coreMatrix d t).mulVec z‖ := by
  have hb := norm_mulVec_le_entry_bound (coreMatrix d t).adjugate 4000 (by norm_num)
    (core_adjugate_entry_bound hd0 hd2 ht0 ht2) ((coreMatrix d t).mulVec z)
  have heq : (coreMatrix d t).adjugate.mulVec ((coreMatrix d t).mulVec z) =
      (coreMatrix d t).det • z := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul]
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [heq, norm_smul, Real.norm_eq_abs] at hb
  have hn := norm_nonneg z
  have hh := mul_le_mul_of_nonneg_right hdet hn
  norm_num at hb
  nlinarith

theorem seed_core_bounds :
    (0 ≤ deltaOf pStar ∧ deltaOf pStar ≤ 2) ∧
    (0 ≤ cOf pStar*deltaOf pStar ∧ cOf pStar*deltaOf pStar ≤ 2) ∧
    300 ≤ |(coreMatrix (deltaOf pStar) (cOf pStar*deltaOf pStar)).det| := by
  have hc := cOf_bounds pStar_spec.1 pStar_spec.2.1
  have hd := deltaOf_bounds pStar_spec.1 pStar_spec.2.1
  have hc0 : 0 ≤ cOf pStar := by linarith [hc.1]
  have hd0 : 0 ≤ deltaOf pStar := by linarith [hd.1]
  have ht0 : 0 ≤ cOf pStar*deltaOf pStar := mul_nonneg hc0 hd0
  have ht2 : cOf pStar*deltaOf pStar ≤ 2 := by
    have hm : cOf pStar*deltaOf pStar ≤ (21/20 : ℝ)*(9/5) := by gcongr <;> linarith [hc.2,hd.2]
    linarith
  refine ⟨⟨hd0,by linarith [hd.2]⟩,⟨ht0,ht2⟩,?_⟩
  have hc2 : (cOf pStar)^2 ≤ 5/4 := by nlinarith [hc.1,hc.2]
  have hc4 : 1 ≤ (cOf pStar)^4 := by nlinarith [sq_nonneg ((cOf pStar)^2-1),hc.1]
  have hd2 : (deltaOf pStar)^2 ≤ 4 := by nlinarith [hd.1,hd.2]
  have hd4 : (deltaOf pStar)^4 ≤ 16 := by nlinarith [sq_nonneg ((deltaOf pStar)^2-4)]
  have hprod : (deltaOf pStar)^2*(cOf pStar)^2 ≤ 5 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hd2) (sq_nonneg (cOf pStar))]
  have hbrace : (deltaOf pStar)^4+18*(deltaOf pStar)^2*(cOf pStar)^2-
      135*(cOf pStar)^4 ≤ -29 := by nlinarith only [hd4,hprod,hc4]
  have hd5 : (8/5 : ℝ)^5 ≤ (deltaOf pStar)^5 := by gcongr; linarith [hd.1]
  have hmul := mul_le_mul_of_nonneg_left hbrace (pow_nonneg hd0 5)
  have hdet : (coreMatrix (deltaOf pStar) (cOf pStar*deltaOf pStar)).det ≤ -300 := by
    rw [coreMatrix_det]
    have heq : deltaOf pStar*((deltaOf pStar)^8+
        18*(deltaOf pStar)^4*(cOf pStar*deltaOf pStar)^2-
        135*(cOf pStar*deltaOf pStar)^4) =
        (deltaOf pStar)^5*((deltaOf pStar)^4+18*(deltaOf pStar)^2*(cOf pStar)^2-
          135*(cOf pStar)^4) := by ring
    rw [heq]
    nlinarith only [hmul,hd5]
  rw [abs_of_nonpos (by linarith : (coreMatrix (deltaOf pStar) (cOf pStar*deltaOf pStar)).det ≤ 0)]
  linarith

theorem variance0_seed_lt : variance0Of pStar < 4/5 := by
  have hc := cOf_bounds pStar_spec.1 pStar_spec.2.1
  have hm := means_bounds pStar_spec.1 pStar_spec.2.1
  have hp := pStar_spec
  have hmneg : 0 < -mu0Of pStar := by linarith [hm.1.2]
  have hmul := mul_pos (sub_pos.mpr hc.1) hmneg
  unfold variance0Of
  nlinarith [hm.1.2,hp.1]

theorem rowTransform_entry_bound {a v : ℝ} (ha0 : 0 ≤ -a) (ha1 : -a ≤ 13/10)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 4/5) (i j : Fin 5) :
    |gaussianRowTransform a v i j| ≤ 65 := by
  have hm (k l : ℕ) : 0 ≤ (-a)^k*v^l ∧ (-a)^k*v^l ≤ (13/10 : ℝ)^k*(4/5)^l := by
    constructor
    · positivity
    · gcongr
  have h10 := hm 1 0
  have h20 := hm 2 0
  have h30 := hm 3 0
  have h40 := hm 4 0
  have h11 := hm 1 1
  have h21 := hm 2 1
  have h01 := hm 0 1
  have h02 := hm 0 2
  norm_num at h10 h20 h30 h40 h11 h21 h01 h02
  have haa : |a| = -a := abs_of_nonpos (by linarith)
  fin_cases i <;> fin_cases j <;>
    norm_num [gaussianRowTransform, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail,haa]
  all_goals try (apply abs_le.mpr; constructor)
  all_goals
    nlinarith only [h10.1,h10.2,h20.1,h20.2,h30.1,h30.2,h40.1,h40.2,
      h11.1,h11.2,h21.1,h21.2,h01.1,h01.2,h02.1,h02.2]

theorem seed_rowTransform_norm_bound (x : Fin 5 → ℝ) :
    ‖(gaussianRowTransform (mu0Of pStar) (variance0Of pStar)).mulVec x‖ ≤ 325*‖x‖ := by
  have hm := means_bounds pStar_spec.1 pStar_spec.2.1
  have hv := variances_bounds pStar_spec.1 pStar_spec.2.1
  have hb := norm_mulVec_le_entry_bound (gaussianRowTransform (mu0Of pStar) (variance0Of pStar))
    65 (by norm_num)
    (rowTransform_entry_bound (by linarith [hm.1.2]) (by linarith [hm.1.1])
      (by linarith [hv.1.1]) (le_of_lt variance0_seed_lt)) x
  norm_num at hb
  exact hb

theorem normalized_solve_bound {w d t : ℝ}
    (hwlo : 1/2 ≤ w) (hwhi : w ≤ 3/4) (hdlo : 0 ≤ d) (hdhi : d ≤ 2)
    (htlo : 0 ≤ t) (hthi : t ≤ 2) (hdet : 300 ≤ |(coreMatrix d t).det|)
    (x : Fin 5 → ℝ) :
    ‖x‖ ≤ 3000*‖(gaussianMomentJacobian w 0 d 0 t).mulVec x‖ := by
  let y := (gaussianMomentJacobian w 0 d 0 t).mulVec x
  let z : Fin 3 → ℝ := ![x 0,w*x 2,w*x 4]
  let r : Fin 3 → ℝ := ![y 2,y 3,y 4]
  have hfin : ((2 : Fin 3).succ).succ = (4 : Fin 5) := rfl
  have heq : (coreMatrix d t).mulVec z = r := by
    ext i
    fin_cases i <;> norm_num [coreMatrix,z,r,y,gaussianMomentJacobian,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,hfin] <;> ring
  have hr : ‖r‖ ≤ ‖y‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    fin_cases i
    · simpa [r,Real.norm_eq_abs] using norm_le_pi_norm y 2
    · simpa [r,Real.norm_eq_abs] using norm_le_pi_norm y 3
    · simpa [r,Real.norm_eq_abs,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail] using norm_le_pi_norm y 4
  have hz : ‖z‖ ≤ 40*‖y‖ := by
    have hb := core_solve_bound hdlo hdhi htlo hthi hdet z
    rw [heq] at hb
    linarith
  have hw0 : 0 ≤ w := by linarith
  have hw1 : 0 ≤ 1-w := by linarith
  have hy (i : Fin 5) : |y i| ≤ ‖y‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm y i
  have hz0 : |x 0| ≤ 40*‖y‖ := by
    have hh := (norm_le_pi_norm z 0).trans hz
    simpa [z,Real.norm_eq_abs] using hh
  have hz2 : |x 2| ≤ 80*‖y‖ := by
    have hh := (norm_le_pi_norm z 1).trans hz
    simp [z,Real.norm_eq_abs,abs_mul,abs_of_nonneg hw0] at hh
    have hmul := mul_le_mul_of_nonneg_right hwlo (abs_nonneg (x 2))
    nlinarith
  have hz4 : |x 4| ≤ 80*‖y‖ := by
    have hh := (norm_le_pi_norm z 2).trans hz
    simp [z,Real.norm_eq_abs,abs_mul,abs_of_nonneg hw0,Matrix.cons_val_two,
      Matrix.vecHead,Matrix.vecTail] at hh
    have hmul := mul_le_mul_of_nonneg_right hwlo (abs_nonneg (x 4))
    nlinarith
  have hy0 : y 0 = d*x 0+(1-w)*x 1+w*x 2 := by
    simp [y,gaussianMomentJacobian,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
    ring
  have hx1eq : (1-w)*x 1 = y 0-d*x 0-w*x 2 := by linarith only [hy0]
  have hx1 : |x 1| ≤ 564*‖y‖ := by
    have h1 : |y 0-d*x 0-w*x 2| ≤ |y 0-d*x 0|+|w*x 2| := by simpa using abs_sub_le (y 0-d*x 0) 0 (w*x 2)
    have h2 : |y 0-d*x 0| ≤ |y 0|+|d*x 0| := by simpa using abs_sub_le (y 0) 0 (d*x 0)
    rw [← hx1eq,abs_mul,abs_of_nonneg hw1,abs_mul,abs_of_nonneg hw0] at h1
    rw [abs_mul,abs_of_nonneg hdlo] at h2
    have hdprod : d*|x 0| ≤ 2*(40*‖y‖) := mul_le_mul hdhi hz0 (abs_nonneg _) (by norm_num)
    have hwprod : w*|x 2| ≤ (3/4)*(80*‖y‖) := mul_le_mul hwhi hz2 (abs_nonneg _) (by norm_num)
    have hlow := mul_le_mul_of_nonneg_right (show (1/4 : ℝ) ≤ 1-w by linarith) (abs_nonneg (x 1))
    nlinarith [hy 0]
  have hy1 : y 1 = (d^2+t)*x 0+2*w*d*x 2+(1-w)*x 3+w*x 4 := by
    simp [y,gaussianMomentJacobian,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
    ring
  have hx3eq : (1-w)*x 3 = y 1-(d^2+t)*x 0-(2*w*d)*x 2-w*x 4 := by linarith only [hy1]
  have hx3 : |x 3| ≤ 2164*‖y‖ := by
    have hcoef0 : 0 ≤ d^2+t := by positivity
    have hcoef1 : 0 ≤ 2*w*d := by positivity
    have hcoef0hi : d^2+t ≤ 6 := by nlinarith [sq_nonneg (d-2)]
    have hcoef1hi : 2*w*d ≤ 3 := by
      have hh := mul_le_mul hwhi hdhi hdlo (by norm_num : (0:ℝ) ≤ 3/4)
      nlinarith
    have h1 : |y 1-(d^2+t)*x 0-(2*w*d)*x 2-w*x 4| ≤
        |y 1-(d^2+t)*x 0-(2*w*d)*x 2|+|w*x 4| := by
      simpa using abs_sub_le (y 1-(d^2+t)*x 0-(2*w*d)*x 2) 0 (w*x 4)
    have h2 : |y 1-(d^2+t)*x 0-(2*w*d)*x 2| ≤ |y 1-(d^2+t)*x 0|+|(2*w*d)*x 2| := by
      simpa using abs_sub_le (y 1-(d^2+t)*x 0) 0 ((2*w*d)*x 2)
    have h3 := abs_sub_le (y 1) 0 ((d^2+t)*x 0)
    simp only [sub_zero,zero_sub,abs_neg] at h3
    rw [← hx3eq,abs_mul,abs_of_nonneg hw1,abs_mul,abs_of_nonneg hw0] at h1
    rw [abs_mul,abs_of_nonneg hcoef1] at h2
    rw [abs_mul,abs_of_nonneg hcoef0] at h3
    have hp0 : (d^2+t)*|x 0| ≤ 6*(40*‖y‖) := mul_le_mul hcoef0hi hz0 (abs_nonneg _) (by norm_num)
    have hp1 : (2*w*d)*|x 2| ≤ 3*(80*‖y‖) := mul_le_mul hcoef1hi hz2 (abs_nonneg _) (by norm_num)
    have hp2 : w*|x 4| ≤ (3/4)*(80*‖y‖) := mul_le_mul hwhi hz4 (abs_nonneg _) (by norm_num)
    have hlow := mul_le_mul_of_nonneg_right (show (1/4:ℝ) ≤ 1-w by linarith) (abs_nonneg (x 3))
    nlinarith [hy 1]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  change |x i| ≤ 3000*‖y‖
  fin_cases i
  · change |x 0| ≤ 3000*‖y‖; nlinarith [norm_nonneg y]
  · change |x 1| ≤ 3000*‖y‖; nlinarith [norm_nonneg y]
  · change |x 2| ≤ 3000*‖y‖; nlinarith [norm_nonneg y]
  · change |x 3| ≤ 3000*‖y‖; nlinarith [norm_nonneg y]
  · change |x 4| ≤ 3000*‖y‖; nlinarith [norm_nonneg y]

theorem seedJacobian_solve_bound (x : Fin 5 → ℝ) :
    ‖x‖ ≤ 1000000*‖seedJacobian.mulVec x‖ := by
  have hw := piOf_bounds pStar_spec.1 pStar_spec.2.1
  obtain ⟨hd,ht,hm⟩ := seed_core_bounds
  have hb := normalized_solve_bound (le_of_lt hw.1) (le_of_lt hw.2) hd.1 hd.2 ht.1 ht.2 hm x
  have heq : (gaussianRowTransform (mu0Of pStar) (variance0Of pStar)).mulVec (seedJacobian.mulVec x) =
      (gaussianMomentJacobian (piOf pStar) 0 (deltaOf pStar) 0 (cOf pStar*deltaOf pStar)).mulVec x := by
    rw [Matrix.mulVec_mulVec]
    unfold seedJacobian
    rw [gaussianRowTransform_mul,mean_difference,variance_difference]
  rw [← heq] at hb
  have ht := seed_rowTransform_norm_bound (seedJacobian.mulVec x)
  nlinarith [norm_nonneg (seedJacobian.mulVec x)]

theorem seedJinv_bound (x : Fin 5 → ℝ) : ‖seedJinv x‖ ≤ 1000000*‖x‖ := by
  have hh := seedJacobian_solve_bound (seedJinv x)
  simpa only [seedJinv_right_inverse] using hh

theorem seedJinv_opNorm_bound : ‖seedJinv‖ ≤ 1000000 := by
  exact ContinuousLinearMap.opNorm_le_bound _ (by norm_num) seedJinv_bound

end
end LCR.AlgebraicSeed
