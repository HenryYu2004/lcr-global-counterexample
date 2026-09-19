import LCR.MatrixOperatorBounds
import LCR.JacobianStability
import LCR.HDerivative
import LCR.JacobianInverse
import LCR.IndicatorReduction
import LCR.SeedUniqueness
import LCR.SeedWeight
import LCR.FullModelEmbedding

/-!
# An unconditional, exact global counterexample

The actual Gaussian-CDF probability model, the isolated algebraic seed,
the positive-scale analytic correction, strict admissibility, distinctness,
and equality of all observable cells are connected in this file.

The final theorems have no analytic or identification hypotheses.
-/

noncomputable section
open Set Metric Function Filter
open scoped Topology BigOperators NNReal
namespace LCR

theorem paper_inverse_bound : ‖AlgebraicSeed.seedJinv‖ ≤ Correction.inverseBound := by
  norm_num [Correction.inverseBound]
  exact AlgebraicSeed.seedJinv_opNorm_bound

theorem paper_inverse_identity :
    AlgebraicSeed.seedJinv.comp (AlgebraicSeed.gaussianJacobianCLM gaussianSeedB) =
      ContinuousLinearMap.id ℝ GaussianSpace :=
  AlgebraicSeed.seedJinv_comp_Jacobian

theorem paper_H_derivative (θ : GaussianSpace)
    (hθ : θ ∈ closedBall gaussianSeedB Correction.radius) :
    HasFDerivAt (H Correction.probitTime) (HJacobian Correction.probitTime θ) θ := by
  have hbox := seedBall_paperBox hθ
  exact hasFDerivAt_H Correction.probitTime θ
    (by norm_num [Correction.probitTime])
    (by linarith [hbox.variance0_mem.1]) (by linarith [hbox.variance1_mem.1])

theorem paper_Jacobian_variation (θ : GaussianSpace)
    (hθ : θ ∈ closedBall gaussianSeedB Correction.radius) :
    ‖HJacobian Correction.probitTime θ-AlgebraicSeed.gaussianJacobianCLM gaussianSeedB‖ ≤
      5*Correction.derivativeBound*(Correction.probitTime+5*Correction.radius) := by
  rw [← HJacobian_zero_gaussianSeedB]
  have ht : 0 ≤ Correction.probitTime := by norm_num [Correction.probitTime]
  have hsum : (∑ j : Fin 5, |θ j-gaussianSeedB j|) ≤ 5*Correction.radius := by
    calc
      _ ≤ ∑ _j : Fin 5, Correction.radius :=
        Finset.sum_le_sum (fun j _ => coordinate_close_of_mem_seedBall hθ j)
      _ = _ := by simp
  change ‖fiveMatrixOperator (fun i j => momentJacobianEntry Correction.probitTime θ (i.val+1) j)-
      fiveMatrixOperator (fun i j => momentJacobianEntry 0 gaussianSeedB (i.val+1) j)‖ ≤ _
  calc
    _ ≤ 5*(10^9*(Correction.probitTime+5*Correction.radius)) := by
      apply norm_fiveMatrixOperator_sub_le
      · have hr := Correction.radius_pos
        positivity
      · intro i j
        have h := momentJacobianEntry_difference_le Correction.probitTime θ gaussianSeedB
          (i.val+1) j ht (seedBall_paperBox hθ) gaussianSeedB_paperBox (by omega)
        exact h.trans (by gcongr)
    _ = _ := by unfold Correction.derivativeBound; ring

theorem paper_correction_lipschitz :
    LipschitzOnWith (1/2 : ℝ≥0) (actualCorrection AlgebraicSeed.seedJinv)
      (closedBall gaussianSeedB Correction.radius) :=
  actualCorrection_half_lipschitz AlgebraicSeed.seedJinv
    (AlgebraicSeed.gaussianJacobianCLM gaussianSeedB) (HJacobian Correction.probitTime)
    paper_inverse_bound paper_inverse_identity paper_H_derivative paper_Jacobian_variation

/-- Existence, exact equality, displacement, convergence, certified error,
and uniqueness for the specified positive-scale correction. -/
theorem exists_corrected_gaussian_seed :
    ∃ star ∈ closedBall gaussianSeedB Correction.radius,
      H Correction.probitTime star = H Correction.probitTime gaussianSeedA ∧
      dist star gaussianSeedB ≤ Correction.finalError ∧
      (∀ n : ℕ, ((actualCorrection AlgebraicSeed.seedJinv)^[n]) gaussianSeedB ∈
        closedBall gaussianSeedB Correction.radius) ∧
      (∀ n : ℕ, dist (((actualCorrection AlgebraicSeed.seedJinv)^[n]) gaussianSeedB) star ≤
        Correction.finalError*(1/2 : ℝ)^n) ∧
      Tendsto (fun n : ℕ => ((actualCorrection AlgebraicSeed.seedJinv)^[n]) gaussianSeedB)
        atTop (𝓝 star) ∧
      (∀ y ∈ closedBall gaussianSeedB Correction.radius,
        H Correction.probitTime y = H Correction.probitTime gaussianSeedA → y = star) := by
  exact Correction.exists_certifiedCorrection H (H Correction.probitTime gaussianSeedA)
    gaussianSeedB AlgebraicSeed.seedJinv.toLinearMap AlgebraicSeed.seedJinv_injective
    paper_correction_lipschitz (actualCorrection_initial_residual _ paper_inverse_bound)

def correctedGaussianSeed : GaussianSpace := Classical.choose exists_corrected_gaussian_seed

theorem correctedGaussianSeed_mem :
    correctedGaussianSeed ∈ closedBall gaussianSeedB Correction.radius :=
  (Classical.choose_spec exists_corrected_gaussian_seed).1

theorem correctedGaussianSeed_exact :
    H Correction.probitTime correctedGaussianSeed = H Correction.probitTime gaussianSeedA :=
  (Classical.choose_spec exists_corrected_gaussian_seed).2.1

theorem correctedGaussianSeed_displacement :
    dist correctedGaussianSeed gaussianSeedB ≤ (4 : ℝ)/10^25 :=
  (Classical.choose_spec exists_corrected_gaussian_seed).2.2.1

theorem correctedGaussianSeed_error (n : ℕ) :
    dist (((actualCorrection AlgebraicSeed.seedJinv)^[n]) gaussianSeedB) correctedGaussianSeed ≤
      ((4 : ℝ)/10^25)*(1/2 : ℝ)^n :=
  (Classical.choose_spec exists_corrected_gaussian_seed).2.2.2.2.1 n

theorem correctedGaussianSeed_limit :
    Tendsto (fun n : ℕ => ((actualCorrection AlgebraicSeed.seedJinv)^[n]) gaussianSeedB)
      atTop (𝓝 correctedGaussianSeed) :=
  (Classical.choose_spec exists_corrected_gaussian_seed).2.2.2.2.2.1

def paperScale : ℝ := 1/10^20

theorem paperScale_pos : 0 < paperScale := by norm_num [paperScale]

theorem sqrt_paperTime : Real.sqrt Correction.probitTime = paperScale := by
  rw [show Correction.probitTime = paperScale^2 by norm_num [Correction.probitTime,paperScale]]
  exact Real.sqrt_sq paperScale_pos.le

def exactThetaA : ProbitParams := probitFromGaussian paperScale gaussianSeedA
def exactThetaB : ProbitParams := probitFromGaussian paperScale correctedGaussianSeed

theorem exactThetaA_admissible : exactThetaA.Admissible :=
  probitFromGaussian_admissible paperScale gaussianSeedA paperScale_pos gaussianSeedA_admissible

theorem exactThetaB_admissible : exactThetaB.Admissible :=
  probitFromGaussian_admissible paperScale correctedGaussianSeed paperScale_pos
    (seedBall_admissible correctedGaussianSeed_mem)

theorem exactThetaB_weight : 69/100 < exactThetaB.weight ∧ exactThetaB.weight < 72/100 :=
  seedBall_weight_interval correctedGaussianSeed_mem

theorem exact_parameters_distinct : exactThetaA ≠ exactThetaB :=
  probitFromGaussian_ne_of_weight_ne paperScale paperScale gaussianSeedA correctedGaussianSeed
    (Ne.symm (seedBall_weight_ne_A correctedGaussianSeed_mem))

/-- All observable cell probabilities are exactly equal, for every n≤5. -/
theorem exact_cells_equal (n : ℕ) (hn : n ≤ 5) (x : Fin n → Bool) :
    probitCell exactThetaA x = probitCell exactThetaB x := by
  have ha := gaussianSeedA_admissible
  have hb := seedBall_admissible correctedGaussianSeed_mem
  have h := equal_H_implies_equal_probitCells_le_five Correction.probitTime gaussianSeedA
    correctedGaussianSeed (by norm_num [Correction.probitTime])
    ha.2.2.2.2.1.le (lt_trans ha.2.2.2.2.1 ha.2.2.2.2.2).le
    hb.2.2.2.2.1.le (lt_trans hb.2.2.2.2.1 hb.2.2.2.2.2).le
    correctedGaussianSeed_exact.symm n hn x
  simpa only [sqrt_paperTime] using h

/-- Main unconditional result: five indicators, strict conventions, and a
genuine exact collision of the actual Gaussian-CDF observation map. -/
theorem global_probit_counterexample : GlobalProbitCounterexample :=
  ⟨exactThetaA,exactThetaB,exactThetaA_admissible,exactThetaB_admissible,
    exact_parameters_distinct,exact_cells_equal 5 le_rfl⟩

theorem global_four_indicator_counterexample :
    ∃ θ η : ProbitParams, θ.Admissible ∧ η.Admissible ∧ θ ≠ η ∧
      ∀ x : Fin 4 → Bool, probitCell θ x = probitCell η x :=
  ⟨exactThetaA,exactThetaB,exactThetaA_admissible,exactThetaB_admissible,
    exact_parameters_distinct,exact_cells_equal 4 (by norm_num)⟩

theorem not_injective_five_indicator_observation :
    ¬Set.InjOn (fun θ : ProbitParams => (probitCell θ : (Fin 5 → Bool) → ℝ))
      {θ | θ.Admissible} := by
  intro hinj
  exact exact_parameters_distinct (hinj exactThetaA_admissible exactThetaB_admissible
    (funext (exact_cells_equal 5 le_rfl)))

/-- This property already supplies a counterexample for 2LCR1 (equal
loadings within each class), hence also for unrestricted 2LCR. -/
def FullModelCounterexample (n : ℕ) : Prop :=
  ∃ ξ ζ : FullProbitParams n,
    ξ.Admissible ∧ ζ.Admissible ∧ ξ.EqualLoadings ∧ ζ.EqualLoadings ∧
    ξ ≠ ζ ∧ ∀ x : Fin n → Bool, fullProbitCell ξ x = fullProbitCell ζ x

theorem full_model_counterexample (n : ℕ) (hn0 : 0 < n) (hn5 : n ≤ 5) :
    FullModelCounterexample n :=
  fullModel_pair_of_probit_pair n hn0 exactThetaA exactThetaB
    exactThetaA_admissible exactThetaB_admissible exact_parameters_distinct
    (exact_cells_equal n hn5)

theorem full_model_five_counterexample : FullModelCounterexample 5 :=
  full_model_counterexample 5 (by norm_num) le_rfl

theorem full_model_four_counterexample : FullModelCounterexample 4 :=
  full_model_counterexample 4 (by norm_num) (by norm_num)

theorem not_injective_2LCR_five :
    ¬Set.InjOn (fun θ : FullProbitParams 5 => fullProbitCell θ) {θ | θ.Admissible} :=
  not_injOn_fullProbitCell_of_probit_pair 5 (by norm_num) exactThetaA exactThetaB
    exactThetaA_admissible exactThetaB_admissible exact_parameters_distinct
    (exact_cells_equal 5 le_rfl)

theorem not_injective_2LCR1_five :
    ¬Set.InjOn (fun θ : FullProbitParams 5 => fullProbitCell θ)
      {θ | θ.Admissible ∧ θ.EqualLoadings} :=
  not_injOn_equalLoading_probitCell_of_probit_pair 5 (by norm_num) exactThetaA exactThetaB
    exactThetaA_admissible exactThetaB_admissible exact_parameters_distinct
    (exact_cells_equal 5 le_rfl)

theorem not_injective_2LCR_four :
    ¬Set.InjOn (fun θ : FullProbitParams 4 => fullProbitCell θ) {θ | θ.Admissible} :=
  not_injOn_fullProbitCell_of_probit_pair 4 (by norm_num) exactThetaA exactThetaB
    exactThetaA_admissible exactThetaB_admissible exact_parameters_distinct
    (exact_cells_equal 4 (by norm_num))

theorem not_injective_2LCR1_four :
    ¬Set.InjOn (fun θ : FullProbitParams 4 => fullProbitCell θ)
      {θ | θ.Admissible ∧ θ.EqualLoadings} :=
  not_injOn_equalLoading_probitCell_of_probit_pair 4 (by norm_num) exactThetaA exactThetaB
    exactThetaA_admissible exactThetaB_admissible exact_parameters_distinct
    (exact_cells_equal 4 (by norm_num))

end LCR
