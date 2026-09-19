import LCR.InitialResidual
import LCR.CertifiedCorrection
import LCR.GaussianJacobian

/-! Explicit positive margins around the algebraic seed. -/

noncomputable section
open Set Metric
namespace LCR

private theorem seed_c_upper : AlgebraicSeed.cOf AlgebraicSeed.pStar < 26/25 := by
  have hlo := AlgebraicSeed.pStar_spec.1
  have hhi := AlgebraicSeed.pStar_spec.2.1
  obtain ⟨hp, h2, h3⟩ := AlgebraicSeed.basic_bounds hlo hhi
  have hd := AlgebraicSeed.denBase_bounds hlo hhi
  have hdpos : 0 < AlgebraicSeed.denBase AlgebraicSeed.pStar := by linarith [hd.1]
  have hden : 0 < 2*AlgebraicSeed.pStar*AlgebraicSeed.denBase AlgebraicSeed.pStar := by positivity
  have hdenLo : 2*(634/1000)*43 <
      2*AlgebraicSeed.pStar*AlgebraicSeed.denBase AlgebraicSeed.pStar := by
    nlinarith [mul_pos (sub_pos.mpr hlo) (sub_pos.mpr hd.1)]
  rw [AlgebraicSeed.cOf, div_lt_iff₀ hden]
  unfold AlgebraicSeed.numC
  nlinarith [h2.1, h3.2]

theorem gaussianSeedB_margins :
    (3/5 < gaussianSeedB 0 ∧ gaussianSeedB 0 < 149/200) ∧
    (-(13/10) < gaussianSeedB 1 ∧ gaussianSeedB 1 < -(11/10)) ∧
    (2/5 < gaussianSeedB 2 ∧ gaussianSeedB 2 < 3/5) ∧
    (51/100 < gaussianSeedB 3 ∧ gaussianSeedB 3 < 5/2) ∧
    (1 < gaussianSeedB 4 ∧ gaussianSeedB 4 < 5/2) ∧
    8/5 < gaussianSeedB 4-gaussianSeedB 3 := by
  have hp := AlgebraicSeed.pStar_spec
  have hm := AlgebraicSeed.means_bounds hp.1 hp.2.1
  have hc := AlgebraicSeed.cOf_bounds hp.1 hp.2.1
  have hd := AlgebraicSeed.deltaOf_bounds hp.1 hp.2.1
  have hc' := seed_c_upper
  have hcpos : 0 < AlgebraicSeed.cOf AlgebraicSeed.pStar := by linarith [hc.1]
  have hdpos : 0 < AlgebraicSeed.deltaOf AlgebraicSeed.pStar := by linarith [hd.1]
  have hs : -(77/100) < AlgebraicSeed.sOf AlgebraicSeed.pStar := by
    have hr : (47/20 : ℝ) < 3/(2*AlgebraicSeed.pStar) := by
      rw [lt_div_iff₀ (by linarith [hp.1])]
      linarith [hp.2.1]
    unfold AlgebraicSeed.sOf
    linarith
  have hwlo : 3/5 < AlgebraicSeed.piOf AlgebraicSeed.pStar := by
    rw [AlgebraicSeed.piOf, lt_div_iff₀ hdpos]
    linarith [hm.1.2, hd.2]
  have hwhi : AlgebraicSeed.piOf AlgebraicSeed.pStar < 149/200 := by
    rw [AlgebraicSeed.piOf, div_lt_iff₀ hdpos]
    unfold AlgebraicSeed.mu0Of
    linarith [hd.1]
  have hprod0lo := mul_pos hcpos (sub_pos.mpr hm.1.1)
  have hprod0hi := mul_neg_of_pos_of_neg hcpos (show AlgebraicSeed.mu0Of AlgebraicSeed.pStar < 0 by linarith [hm.1.2])
  have hprod1lo := mul_pos hcpos (show 0 < AlgebraicSeed.mu1Of AlgebraicSeed.pStar by linarith [hm.2.1])
  have hprod1hi := mul_pos hcpos (sub_pos.mpr hm.2.2)
  have hv0 : 51/100 < AlgebraicSeed.variance0Of AlgebraicSeed.pStar ∧
      AlgebraicSeed.variance0Of AlgebraicSeed.pStar < 5/2 := by
    unfold AlgebraicSeed.variance0Of
    constructor <;> nlinarith [hp.1, hp.2.1]
  have hv1 : 1 < AlgebraicSeed.variance1Of AlgebraicSeed.pStar ∧
      AlgebraicSeed.variance1Of AlgebraicSeed.pStar < 5/2 := by
    unfold AlgebraicSeed.variance1Of
    constructor <;> nlinarith [hp.1, hp.2.1]
  have hvdiff : 8/5 < AlgebraicSeed.variance1Of AlgebraicSeed.pStar-
      AlgebraicSeed.variance0Of AlgebraicSeed.pStar := by
    rw [AlgebraicSeed.variance_difference]
    nlinarith [mul_pos (sub_pos.mpr hc.1) hdpos]
  exact ⟨⟨hwlo,hwhi⟩, hm.1, hm.2, hv0, hv1, hvdiff⟩

theorem coordinate_close_of_mem_seedBall {θ : GaussianSpace}
    (hθ : θ ∈ closedBall gaussianSeedB Correction.radius) (i : Fin 5) :
    |θ i-gaussianSeedB i| ≤ Correction.radius := by
  have hn : ‖θ-gaussianSeedB‖ ≤ Correction.radius := by
    simpa only [mem_closedBall, dist_eq_norm] using hθ
  have hcoord := (pi_norm_le_iff_of_nonneg Correction.radius_pos.le).mp hn i
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using hcoord

theorem seedBall_paperBox {θ : GaussianSpace}
    (hθ : θ ∈ closedBall gaussianSeedB Correction.radius) : PaperBox θ := by
  obtain ⟨hw,hm0,hm1,hv0,hv1,hd⟩ := gaussianSeedB_margins
  have h0 := abs_le.mp (coordinate_close_of_mem_seedBall hθ 0)
  have h1 := abs_le.mp (coordinate_close_of_mem_seedBall hθ 1)
  have h2 := abs_le.mp (coordinate_close_of_mem_seedBall hθ 2)
  have h3 := abs_le.mp (coordinate_close_of_mem_seedBall hθ 3)
  have h4 := abs_le.mp (coordinate_close_of_mem_seedBall hθ 4)
  have hr : Correction.radius < 1/1000 := by norm_num [Correction.radius]
  constructor
  · constructor <;> linarith [hw.1,hw.2,h0.1,h0.2]
  · rw [abs_le]; constructor <;> linarith [hm0.1,hm0.2,h1.1,h1.2]
  · rw [abs_le]; constructor <;> linarith [hm1.1,hm1.2,h2.1,h2.2]
  · constructor <;> linarith [hv0.1,hv0.2,h3.1,h3.2]
  · constructor <;> linarith [hv1.1,hv1.2,h4.1,h4.2]

theorem seedBall_admissible {θ : GaussianSpace}
    (hθ : θ ∈ closedBall gaussianSeedB Correction.radius) : GaussianAdmissible θ := by
  obtain ⟨hw,hm0,hm1,hv0,hv1,hd⟩ := gaussianSeedB_margins
  have h0 := abs_le.mp (coordinate_close_of_mem_seedBall hθ 0)
  have h1 := abs_le.mp (coordinate_close_of_mem_seedBall hθ 1)
  have h2 := abs_le.mp (coordinate_close_of_mem_seedBall hθ 2)
  have h3 := abs_le.mp (coordinate_close_of_mem_seedBall hθ 3)
  have h4 := abs_le.mp (coordinate_close_of_mem_seedBall hθ 4)
  have hr : Correction.radius < 1/1000 := by norm_num [Correction.radius]
  unfold GaussianAdmissible
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;>
    linarith [hw.1,hw.2,hm0.2,hm1.1,hv0.1,h0.1,h0.2,h1.2,h2.1,h3.1,h3.2,h4.1]

theorem seedBall_weight_ne_A {θ : GaussianSpace}
    (hθ : θ ∈ closedBall gaussianSeedB Correction.radius) : θ 0 ≠ gaussianSeedA 0 := by
  have hw := gaussianSeedB_margins.1.1
  have h0 := abs_le.mp (coordinate_close_of_mem_seedBall hθ 0)
  have hr : Correction.radius < 1/1000 := by norm_num [Correction.radius]
  change θ 0 ≠ (1/2 : ℝ)
  linarith [h0.1]

end LCR
