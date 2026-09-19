import LCR.ProbitModel

/-! Inclusion of the exchangeable construction into the actual finite-product
observation model with indicator-specific intercepts and loadings. The
equal-loading predicate imposes 2LCR1, while leaving intercepts unrestricted.
All claims here are embedding implications; existence of aliases is supplied
by the separately proved positive-scale construction. -/

open MeasureTheory
open scoped BigOperators

noncomputable section
namespace LCR

structure FullProbitParams (n : ℕ) where
  weight : ℝ
  alpha0 : Fin n → ℝ
  alpha1 : Fin n → ℝ
  beta0 : Fin n → ℝ
  beta1 : Fin n → ℝ

/-- Strict label and sign conventions; no equality across indicators. -/
def FullProbitParams.Admissible {n : ℕ} (θ : FullProbitParams n) : Prop :=
  0 < θ.weight ∧ θ.weight < 1 ∧
    ∀ i, θ.alpha0 i < 0 ∧ 0 < θ.alpha1 i ∧ 0 < θ.beta0 i ∧ θ.beta0 i < θ.beta1 i

/-- The within-class equal-loading restriction, not an equal-intercept restriction. -/
def FullProbitParams.EqualLoadings {n : ℕ} (θ : FullProbitParams n) : Prop :=
  ∃ b0 b1 : ℝ, ∀ i, θ.beta0 i = b0 ∧ θ.beta1 i = b1

def fullComponentCell {n : ℕ} (a b : Fin n → ℝ) (x : Fin n → Bool) : ℝ :=
  ∫ u, ∏ i : Fin n, if x i = true then Phi (a i + b i * u)
    else 1 - Phi (a i + b i * u) ∂standardGaussian

/-- The observation law of the full 2LCR model: integrate a product of
conditionally independent Bernoulli probabilities within each class. -/
def fullProbitCell {n : ℕ} (θ : FullProbitParams n) (x : Fin n → Bool) : ℝ :=
  (1 - θ.weight) * fullComponentCell θ.alpha0 θ.beta0 x +
    θ.weight * fullComponentCell θ.alpha1 θ.beta1 x

def constantEmbedding (n : ℕ) (θ : ProbitParams) : FullProbitParams n where
  weight := θ.weight
  alpha0 := fun _ => θ.alpha0
  alpha1 := fun _ => θ.alpha1
  beta0 := fun _ => θ.beta0
  beta1 := fun _ => θ.beta1

theorem bernoulli_product_eq_successCount {n : ℕ} (x : Fin n → Bool) (q : ℝ) :
    (∏ i : Fin n, if x i = true then q else 1 - q) =
      q ^ successCount x * (1 - q) ^ (n - successCount x) := by
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  have hcard := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun i => x i = true)
  have hnot : (Finset.univ.filter fun i : Fin n => ¬ x i = true).card = n - successCount x := by
    simp only [Finset.card_univ, Fintype.card_fin] at hcard
    unfold successCount
    omega
  rw [hnot]
  rfl

theorem fullComponentCell_constant {n : ℕ} (a b : ℝ) (x : Fin n → Bool) :
    fullComponentCell (fun _ => a) (fun _ => b) x =
      componentCell a b (successCount x) (n - successCount x) := by
  unfold fullComponentCell componentCell
  apply integral_congr_ae
  filter_upwards [] with u
  exact bernoulli_product_eq_successCount x (Phi (a + b * u))

theorem fullProbitCell_constantEmbedding {n : ℕ} (θ : ProbitParams) (x : Fin n → Bool) :
    fullProbitCell (constantEmbedding n θ) x = probitCell θ x := by
  simp [fullProbitCell, constantEmbedding, fullComponentCell_constant, probitCell]

theorem constantEmbedding_admissible {n : ℕ} {θ : ProbitParams} (hθ : θ.Admissible) :
    (constantEmbedding n θ).Admissible := by
  exact ⟨hθ.1, hθ.2.1, fun _ => hθ.2.2⟩

theorem constantEmbedding_equalLoadings (n : ℕ) (θ : ProbitParams) :
    (constantEmbedding n θ).EqualLoadings :=
  ⟨θ.beta0, θ.beta1, fun _ => ⟨rfl, rfl⟩⟩

/-- Nonempty indicator sets preserve every parameter under the embedding. -/
theorem constantEmbedding_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (constantEmbedding n) := by
  intro θ η h
  let i : Fin n := ⟨0, hn⟩
  have hw := congrArg FullProbitParams.weight h
  have h0 := congrArg (fun z : FullProbitParams n => z.alpha0 i) h
  have h1 := congrArg (fun z : FullProbitParams n => z.alpha1 i) h
  have hb0 := congrArg (fun z : FullProbitParams n => z.beta0 i) h
  have hb1 := congrArg (fun z : FullProbitParams n => z.beta1 i) h
  cases θ
  cases η
  simp only [constantEmbedding] at hw h0 h1 hb0 hb1
  simp_all

/-- An exchangeable alias becomes an alias in both 2LCR1 and 2LCR, with
the same strict inequalities, through the actual finite-product cell law. -/
theorem fullModel_pair_of_probit_pair (n : ℕ) (hn : 0 < n) (θ η : ProbitParams)
    (hθ : θ.Admissible) (hη : η.Admissible) (hne : θ ≠ η)
    (hcells : ∀ x : Fin n → Bool, probitCell θ x = probitCell η x) :
    ∃ ξ ζ : FullProbitParams n,
      ξ.Admissible ∧ ζ.Admissible ∧ ξ.EqualLoadings ∧ ζ.EqualLoadings ∧
      ξ ≠ ζ ∧ ∀ x : Fin n → Bool, fullProbitCell ξ x = fullProbitCell ζ x := by
  refine ⟨constantEmbedding n θ, constantEmbedding n η,
    constantEmbedding_admissible hθ, constantEmbedding_admissible hη,
    constantEmbedding_equalLoadings n θ, constantEmbedding_equalLoadings n η,
    (constantEmbedding_injective n hn).ne hne, ?_⟩
  intro x
  simpa only [fullProbitCell_constantEmbedding] using hcells x

theorem not_injOn_fullProbitCell_of_probit_pair (n : ℕ) (hn : 0 < n) (θ η : ProbitParams)
    (hθ : θ.Admissible) (hη : η.Admissible) (hne : θ ≠ η)
    (hcells : ∀ x : Fin n → Bool, probitCell θ x = probitCell η x) :
    ¬ Set.InjOn (fun ξ : FullProbitParams n => fullProbitCell ξ)
      {ξ | ξ.Admissible} := by
  intro hinj
  apply (constantEmbedding_injective n hn).ne hne
  apply hinj (constantEmbedding_admissible hθ) (constantEmbedding_admissible hη)
  funext x
  simpa only [fullProbitCell_constantEmbedding] using hcells x

theorem not_injOn_equalLoading_probitCell_of_probit_pair
    (n : ℕ) (hn : 0 < n) (θ η : ProbitParams)
    (hθ : θ.Admissible) (hη : η.Admissible) (hne : θ ≠ η)
    (hcells : ∀ x : Fin n → Bool, probitCell θ x = probitCell η x) :
    ¬ Set.InjOn (fun ξ : FullProbitParams n => fullProbitCell ξ)
      {ξ | ξ.Admissible ∧ ξ.EqualLoadings} := by
  intro hinj
  apply (constantEmbedding_injective n hn).ne hne
  apply hinj ⟨constantEmbedding_admissible hθ, constantEmbedding_equalLoadings n θ⟩
    ⟨constantEmbedding_admissible hη, constantEmbedding_equalLoadings n η⟩
  funext x
  simpa only [fullProbitCell_constantEmbedding] using hcells x

end LCR
