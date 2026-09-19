import LCR.SeedNeighborhood

/-!
# Assembly of the statistical conclusion from explicitly listed analytic bounds

The remaining hypotheses in this module are analytic bounds, not a putative
solution or a probit alias. This is an intermediate assembly theorem. The
unconditional manuscript theorem requires verified instantiations of them.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Metric Function
open scoped NNReal
namespace LCR

abbrev GaussianOperator := GaussianSpace →L[ℝ] GaussianSpace

def actualCorrection (K : GaussianOperator) (x : GaussianSpace) : GaussianSpace :=
  x-K (H Correction.probitTime x-H Correction.probitTime gaussianSeedA)

theorem actualCorrection_initial_residual (K : GaussianOperator)
    (hK : ‖K‖ ≤ Correction.inverseBound) :
    dist (actualCorrection K gaussianSeedB) gaussianSeedB ≤ Correction.initialError := by
  have ht : 0 ≤ Correction.probitTime := by norm_num [Correction.probitTime]
  have hK0 : 0 ≤ Correction.inverseBound := by norm_num [Correction.inverseBound]
  have hr := gaussian_seeds_H_initial_residual_le Correction.probitTime ht
  rw [dist_eq_norm]
  have heq : actualCorrection K gaussianSeedB-gaussianSeedB =
      -K (H Correction.probitTime gaussianSeedB-H Correction.probitTime gaussianSeedA) := by
    unfold actualCorrection
    abel
  rw [heq, norm_neg]
  calc
    _ ≤ ‖K‖*‖H Correction.probitTime gaussianSeedB-H Correction.probitTime gaussianSeedA‖ := K.le_opNorm _
    _ ≤ Correction.inverseBound*(2*10^9*Correction.probitTime) := by gcongr
    _ = Correction.initialError := by
      norm_num [Correction.inverseBound, Correction.probitTime, Correction.initialError]

theorem actualCorrection_half_lipschitz (K J : GaussianOperator)
    (D : GaussianSpace → GaussianOperator)
    (hK : ‖K‖ ≤ Correction.inverseBound)
    (hKJ : K.comp J = ContinuousLinearMap.id ℝ GaussianSpace)
    (hder : ∀ x ∈ closedBall gaussianSeedB Correction.radius,
      HasFDerivAt (H Correction.probitTime) (D x) x)
    (hvariation : ∀ x ∈ closedBall gaussianSeedB Correction.radius,
      ‖D x-J‖ ≤ 5*Correction.derivativeBound*(Correction.probitTime+5*Correction.radius)) :
    LipschitzOnWith (1/2 : ℝ≥0) (actualCorrection K)
      (closedBall gaussianSeedB Correction.radius) := by
  have hK0 : 0 ≤ Correction.inverseBound := by norm_num [Correction.inverseBound]
  let TD : GaussianSpace → GaussianOperator := fun x =>
    ContinuousLinearMap.id ℝ GaussianSpace-K.comp (D x)
  have hd : ∀ x ∈ closedBall gaussianSeedB Correction.radius,
      HasFDerivAt (actualCorrection K) (TD x) x := by
    intro x hx
    exact (hasFDerivAt_id x).sub
      (K.hasFDerivAt.comp x ((hder x hx).sub_const (H Correction.probitTime gaussianSeedA)))
  have hb : ∀ x ∈ closedBall gaussianSeedB Correction.radius, ‖TD x‖ ≤ (1/2 : ℝ) := by
    intro x hx
    have heq : TD x = -(K.comp (D x-J)) := by
      apply ContinuousLinearMap.ext
      intro y
      have hid := congrArg (fun L : GaussianOperator => L y) hKJ
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hid
      simp only [TD, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply, map_sub, hid]
      abel
    rw [heq, norm_neg]
    calc
      _ ≤ ‖K‖*‖D x-J‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ Correction.inverseBound*(5*Correction.derivativeBound*
          (Correction.probitTime+5*Correction.radius)) :=
        mul_le_mul hK (hvariation x hx) (norm_nonneg _) hK0
      _ ≤ 1/2 := by
        have h := Correction.paper_contraction_factor_lt_half
        nlinarith
  exact (convex_closedBall gaussianSeedB Correction.radius).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun x hx => (hd x hx).hasFDerivWithinAt)
    (fun x hx => by exact_mod_cast hb x hx)

/-- The requested statistical statement, with actual standard-Gaussian CDF
cell probabilities and strict ordering/sign restrictions. -/
def GlobalProbitCounterexample : Prop :=
  ∃ θ η : ProbitParams, θ.Admissible ∧ η.Admissible ∧ θ ≠ η ∧
    ∀ x : Fin 5 → Bool, probitCell θ x = probitCell η x

/-- An intermediate assembly theorem: all analytic premises are visible.
It must not be reported as an unconditional counterexample theorem. -/
theorem globalProbitCounterexample_of_analytic_bounds (K J : GaussianOperator)
    (D : GaussianSpace → GaussianOperator)
    (hK : ‖K‖ ≤ Correction.inverseBound)
    (hinj : Injective K)
    (hKJ : K.comp J = ContinuousLinearMap.id ℝ GaussianSpace)
    (hder : ∀ x ∈ closedBall gaussianSeedB Correction.radius,
      HasFDerivAt (H Correction.probitTime) (D x) x)
    (hvariation : ∀ x ∈ closedBall gaussianSeedB Correction.radius,
      ‖D x-J‖ ≤ 5*Correction.derivativeBound*(Correction.probitTime+5*Correction.radius)) :
    GlobalProbitCounterexample := by
  have hLip := actualCorrection_half_lipschitz K J D hK hKJ hder hvariation
  have hres := actualCorrection_initial_residual K hK
  obtain ⟨star,hstar,heq,_,_,_,_,_⟩ := Correction.exists_certifiedCorrection H
    (H Correction.probitTime gaussianSeedA) gaussianSeedB K.toLinearMap hinj hLip hres
  have hstar_adm := seedBall_admissible hstar
  have ht : 0 < Correction.probitTime := by norm_num [Correction.probitTime]
  let ε := Real.sqrt Correction.probitTime
  have hε : 0 < ε := Real.sqrt_pos.mpr ht
  refine ⟨probitFromGaussian ε gaussianSeedA, probitFromGaussian ε star,
    probitFromGaussian_admissible ε gaussianSeedA hε gaussianSeedA_admissible,
    probitFromGaussian_admissible ε star hε hstar_adm, ?_, ?_⟩
  · exact probitFromGaussian_ne_of_weight_ne ε ε gaussianSeedA star
      (Ne.symm (seedBall_weight_ne_A hstar))
  · apply equal_H_implies_equal_probitCells Correction.probitTime gaussianSeedA star ht.le
      gaussianSeedA_admissible.2.2.2.2.1.le
      (lt_trans gaussianSeedA_admissible.2.2.2.2.1 gaussianSeedA_admissible.2.2.2.2.2).le
      hstar_adm.2.2.2.2.1.le (lt_trans hstar_adm.2.2.2.2.1 hstar_adm.2.2.2.2.2).le
    exact heq.symm

end LCR
