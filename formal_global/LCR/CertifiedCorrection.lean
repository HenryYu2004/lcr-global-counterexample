import Mathlib

/-!
# A reusable certified correction theorem

This module formalizes the Banach-correction step on the **sup-norm** space
`Fin 5 → ℝ`, with the exact constants in the global-counterexample note.

It is an INTERMEDIATE theorem, not the statistical global-counterexample
theorem.  In particular, applications still have to prove the Lipschitz and
initial-residual hypotheses for their actual Gaussian/probit integral map,
and injectivity of the chosen linear correction operator.  No hypothesis
postulates an exact solution or convergence of the iteration.
-/

noncomputable section

open Filter Function Metric Set
open scoped Topology NNReal

namespace LCR.Correction

/-- The standard Pi norm on this finite product is the infinity norm. -/
abbrev Space := Fin 5 → ℝ

def radius : ℝ := 1 / 10 ^ 18
def initialError : ℝ := 2 / 10 ^ 25
def finalError : ℝ := 4 / 10 ^ 25
def probitTime : ℝ := 1 / 10 ^ 40
def derivativeBound : ℝ := 10 ^ 9
def inverseBound : ℝ := 10 ^ 6

lemma radius_pos : 0 < radius := by norm_num [radius]
lemma initialError_nonneg : 0 ≤ initialError := by norm_num [initialError]
lemma finalError_nonneg : 0 ≤ finalError := by norm_num [finalError]
lemma half_radius_add_initialError_lt : radius / 2 + initialError < radius := by
  norm_num [radius, initialError]
lemma twice_initialError : 2 * initialError = finalError := by
  norm_num [initialError, finalError]

/-- The numerical implication used after the actual derivative estimates
have been established.  This lemma establishes only the exact arithmetic. -/
lemma paper_contraction_factor_lt_half :
    5 * inverseBound * derivativeBound * (probitTime + 5 * radius) < (1 / 2 : ℝ) := by
  norm_num [inverseBound, derivativeBound, probitTime, radius]

lemma paper_initial_residual_eq :
    2 * inverseBound * derivativeBound * probitTime = initialError := by
  norm_num [inverseBound, derivativeBound, probitTime, initialError]

/-- The initial residual and half-Lipschitz estimate imply the required
self-map property.  Thus self-mapping is a conclusion, not an assumption. -/
theorem mapsTo_closedBall_of_half_lipschitz
    (T : Space → Space) (seed : Space)
    (hLip : LipschitzOnWith (1 / 2 : ℝ≥0) T (closedBall seed radius))
    (hres : dist (T seed) seed ≤ initialError) :
    MapsTo T (closedBall seed radius) (closedBall seed radius) := by
  have hseed : seed ∈ closedBall seed radius := by
    simpa only [mem_closedBall, dist_self] using radius_pos.le
  intro x hx
  rw [mem_closedBall] at hx ⊢
  have hxy := hLip.dist_le_mul x (by simpa only [mem_closedBall] using hx) seed hseed
  norm_num at hxy
  calc
    dist (T x) seed ≤ dist (T x) (T seed) + dist (T seed) seed := dist_triangle _ _ _
    _ ≤ (1 / 2 : ℝ) * dist x seed + initialError := add_le_add hxy hres
    _ ≤ radius / 2 + initialError := by linarith
    _ ≤ radius := half_radius_add_initialError_lt.le

/-- Banach's theorem on a complete closed infinity ball, together with the
paper's quantitative displacement and iteration bounds.

The result includes uniqueness only inside the specified ball. -/
theorem exists_fixedPoint_half_lipschitz
    (T : Space → Space) (seed : Space)
    (hLip : LipschitzOnWith (1 / 2 : ℝ≥0) T (closedBall seed radius))
    (hres : dist (T seed) seed ≤ initialError) :
    ∃ star ∈ closedBall seed radius,
      T star = star ∧
      dist star seed ≤ finalError ∧
      (∀ n : ℕ, (T^[n]) seed ∈ closedBall seed radius) ∧
      (∀ n : ℕ, dist ((T^[n]) seed) star ≤ finalError * (1 / 2 : ℝ) ^ n) ∧
      Tendsto (fun n : ℕ => (T^[n]) seed) atTop (𝓝 star) ∧
      (∀ y ∈ closedBall seed radius, T y = y → y = star) := by
  let S := closedBall seed radius
  have hseed : seed ∈ S := by
    simpa only [S, mem_closedBall, dist_self] using radius_pos.le
  have hmaps : MapsTo T S S := mapsTo_closedBall_of_half_lipschitz T seed hLip hres
  let start : S := ⟨seed, hseed⟩
  letI : Nonempty S := ⟨start⟩
  letI : CompleteSpace S := (isClosed_closedBall : IsClosed S).isComplete.completeSpace_coe
  let f : S → S := fun x => ⟨T x, hmaps x.property⟩
  have hf : ContractingWith (1 / 2 : ℝ≥0) f := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    exact hLip.dist_le_mul x x.property y y.property
  let starSub : S := hf.fixedPoint f
  let star : Space := starSub.val
  have hstar : star ∈ S := starSub.property
  have hfixSub : f starSub = starSub := hf.fixedPoint_isFixedPt
  have hfix : T star = star := congrArg Subtype.val hfixSub
  have hdist : dist star seed ≤ finalError := by
    have hcontract := hLip.dist_le_mul star hstar seed hseed
    norm_num at hcontract
    rw [hfix] at hcontract
    have htriangle := dist_triangle star (T seed) seed
    have herr := twice_initialError
    linarith
  have hmem : ∀ n : ℕ, (T^[n]) seed ∈ S := by
    intro n
    exact hmaps.iterate n hseed
  have hiter : ∀ n : ℕ,
      dist ((T^[n]) seed) star ≤ finalError * (1 / 2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => simpa only [iterate_zero, id_eq, pow_zero, mul_one, dist_comm] using hdist
    | succ n ih =>
        have hcontract := hLip.dist_le_mul ((T^[n]) seed) (hmem n) star hstar
        norm_num at hcontract
        rw [hfix] at hcontract
        rw [iterate_succ_apply']
        calc
          dist (T ((T^[n]) seed)) star ≤ (1 / 2 : ℝ) * dist ((T^[n]) seed) star := hcontract
          _ ≤ (1 / 2 : ℝ) * (finalError * (1 / 2 : ℝ) ^ n) := by gcongr
          _ = finalError * (1 / 2 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring
  have hconverges : Tendsto (fun n : ℕ => (T^[n]) seed) atTop (𝓝 star) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun n => dist_nonneg) hiter
    have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using hpow.const_mul finalError
  have hunique : ∀ y ∈ S, T y = y → y = star := by
    intro y hy hfy
    have hcontract := hLip.dist_le_mul y hy star hstar
    norm_num at hcontract
    rw [hfy, hfix] at hcontract
    apply dist_eq_zero.mp
    linarith [dist_nonneg (x := y) (y := star)]
  exact ⟨star, hstar, hfix, hdist, hmem, hiter, hconverges, hunique⟩

/-- The fixed linear preconditioner used by the correction iteration. -/
def correctionMap (G : Space → Space) (target : Space)
    (Jinv : Space →ₗ[ℝ] Space) (x : Space) : Space :=
  x - Jinv (G x - target)

/-- Injectivity of the linear preconditioner makes fixed points exactly
solutions of the target equation.  No invertibility of `G` is assumed. -/
theorem correctionMap_eq_self_iff
    (G : Space → Space) (target : Space) (Jinv : Space →ₗ[ℝ] Space)
    (hJ : Injective Jinv) (x : Space) :
    correctionMap G target Jinv x = x ↔ G x = target := by
  constructor
  · intro h
    have hzero : Jinv (G x - target) = 0 := by
      simpa only [correctionMap, sub_eq_self] using h
    have harg : G x - target = 0 := hJ (by simpa using hzero)
    exact sub_eq_zero.mp harg
  · intro h
    simp [correctionMap, h]

/-- Reusable, conditional correction theorem at the exact positive scale
`10⁻⁴⁰`.  To apply it to the paper, one must discharge `hLip`, `hres` and
`hJ` for the actual probit moment integral and the certified inverse.

This theorem does NOT assume the target equation has a solution. -/
theorem exists_certifiedCorrection
    (H : ℝ → Space → Space) (target seed : Space) (Jinv : Space →ₗ[ℝ] Space)
    (hJ : Injective Jinv)
    (hLip : LipschitzOnWith (1 / 2 : ℝ≥0)
      (correctionMap (H probitTime) target Jinv) (closedBall seed radius))
    (hres : dist (correctionMap (H probitTime) target Jinv seed) seed ≤ initialError) :
    ∃ star ∈ closedBall seed radius,
      H probitTime star = target ∧
      dist star seed ≤ finalError ∧
      (∀ n : ℕ,
        ((correctionMap (H probitTime) target Jinv)^[n]) seed ∈ closedBall seed radius) ∧
      (∀ n : ℕ,
        dist (((correctionMap (H probitTime) target Jinv)^[n]) seed) star ≤
          finalError * (1 / 2 : ℝ) ^ n) ∧
      Tendsto (fun n : ℕ => ((correctionMap (H probitTime) target Jinv)^[n]) seed)
        atTop (𝓝 star) ∧
      (∀ y ∈ closedBall seed radius, H probitTime y = target → y = star) := by
  rcases exists_fixedPoint_half_lipschitz
      (correctionMap (H probitTime) target Jinv) seed hLip hres with
    ⟨star, hstar, hfix, hdist, hmem, hiter, hconverges, hunique⟩
  refine ⟨star, hstar, (correctionMap_eq_self_iff _ _ _ hJ _).mp hfix,
    hdist, hmem, hiter, hconverges, ?_⟩
  intro y hy htarget
  exact hunique y hy ((correctionMap_eq_self_iff _ _ _ hJ _).mpr htarget)

end LCR.Correction
