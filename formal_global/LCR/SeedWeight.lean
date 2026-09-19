import LCR.SeedNeighborhood

/-! The mixing-weight separation stated in the manuscript. -/

noncomputable section
namespace LCR

private theorem seed_c_narrow :
    51/50 < AlgebraicSeed.cOf AlgebraicSeed.pStar ∧
    AlgebraicSeed.cOf AlgebraicSeed.pStar < 103/100 := by
  let p := AlgebraicSeed.pStar
  have hlo : (634/1000 : ℝ) < p := AlgebraicSeed.pStar_spec.1
  have hhi : p < (635/1000 : ℝ) := AlgebraicSeed.pStar_spec.2.1
  have hp : 0 < p := by linarith
  have h2l : (634/1000 : ℝ)^2 < p^2 := by nlinarith
  have h2u : p^2 < (635/1000 : ℝ)^2 := by nlinarith
  have h3l : (634/1000 : ℝ)^3 < p^3 := by nlinarith [mul_pos hp (sub_pos.mpr h2l)]
  have h3u : p^3 < (635/1000 : ℝ)^3 := by nlinarith [mul_pos hp (sub_pos.mpr h2u)]
  have hdlo : 4346/100 < AlgebraicSeed.denBase p := by
    unfold AlgebraicSeed.denBase
    nlinarith
  have hdhi : AlgebraicSeed.denBase p < 4349/100 := by
    unfold AlgebraicSeed.denBase
    nlinarith
  have hdenlo : (551/10 : ℝ) < 2*p*AlgebraicSeed.denBase p := by
    nlinarith [mul_pos (sub_pos.mpr hlo) (sub_pos.mpr hdlo)]
  have hdenhi : 2*p*AlgebraicSeed.denBase p < (221/4 : ℝ) := by
    nlinarith [mul_pos (sub_pos.mpr hhi) (sub_pos.mpr hdhi)]
  have hdenpos : 0 < 2*p*AlgebraicSeed.denBase p := by linarith
  have hnlo : (2819/50 : ℝ) < AlgebraicSeed.numC p := by
    unfold AlgebraicSeed.numC
    nlinarith
  have hnhi : AlgebraicSeed.numC p < (5657/100 : ℝ) := by
    unfold AlgebraicSeed.numC
    nlinarith
  change 51/50 < AlgebraicSeed.cOf p ∧ AlgebraicSeed.cOf p < 103/100
  unfold AlgebraicSeed.cOf
  constructor
  · rw [lt_div_iff₀ hdenpos]
    linarith
  · rw [div_lt_iff₀ hdenpos]
    linarith

theorem gaussianSeedB_weight_narrow :
    691/1000 < gaussianSeedB 0 ∧ gaussianSeedB 0 < 719/1000 := by
  have hp := AlgebraicSeed.pStar_spec
  have hc := seed_c_narrow
  have hrlo : (59/25 : ℝ) < 3/(2*AlgebraicSeed.pStar) := by
    rw [lt_div_iff₀ (by linarith [hp.1])]
    linarith [hp.2.1]
  have hrhi : 3/(2*AlgebraicSeed.pStar) < (2367/1000 : ℝ) := by
    rw [div_lt_iff₀ (by linarith [hp.1])]
    linarith [hp.1]
  have hslo : -(73/100) < AlgebraicSeed.sOf AlgebraicSeed.pStar := by
    unfold AlgebraicSeed.sOf
    linarith [hc.2]
  have hshi : AlgebraicSeed.sOf AlgebraicSeed.pStar < -(693/1000) := by
    unfold AlgebraicSeed.sOf
    linarith [hc.1]
  have hd := AlgebraicSeed.deltaOf_bounds hp.1 hp.2.1
  have hdlo : 17/10 < AlgebraicSeed.deltaOf AlgebraicSeed.pStar := by
    have hd2 : (AlgebraicSeed.deltaOf AlgebraicSeed.pStar)^2 =
        (AlgebraicSeed.sOf AlgebraicSeed.pStar)^2+4*AlgebraicSeed.pStar :=
      Real.sq_sqrt (by have h := AlgebraicSeed.seed_p_pos; positivity)
    nlinarith [sq_nonneg (AlgebraicSeed.sOf AlgebraicSeed.pStar+693/1000),hp.1,hd.1]
  have hdpos : 0 < AlgebraicSeed.deltaOf AlgebraicSeed.pStar := by linarith [hd.1]
  change 691/1000 < AlgebraicSeed.piOf AlgebraicSeed.pStar ∧
    AlgebraicSeed.piOf AlgebraicSeed.pStar < 719/1000
  unfold AlgebraicSeed.piOf
  constructor
  · rw [lt_div_iff₀ hdpos]
    unfold AlgebraicSeed.mu0Of
    linarith [hd.2]
  · rw [div_lt_iff₀ hdpos]
    unfold AlgebraicSeed.mu0Of
    linarith

theorem seedBall_weight_interval {θ : GaussianSpace}
    (hθ : θ ∈ Metric.closedBall gaussianSeedB Correction.radius) :
    69/100 < θ 0 ∧ θ 0 < 72/100 := by
  have h := gaussianSeedB_weight_narrow
  have hc := abs_le.mp (coordinate_close_of_mem_seedBall hθ 0)
  have hr : Correction.radius < 1/1000 := by norm_num [Correction.radius]
  constructor <;> linarith [h.1,h.2,hc.1,hc.2]

end LCR
