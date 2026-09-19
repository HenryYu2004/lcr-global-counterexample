import LCR.TransformedMoments

/-! A five-moment collision yields the same observable binary-cell law
for every number of indicators at most five. This uses the exact integral
and binomial identities, without an assumed marginalization theorem. -/

noncomputable section
namespace LCR

theorem equal_H_implies_equal_transformedMoments_le_five
    (t : ℝ) (θ η : GaussianSpace) (heq : H t θ = H t η) :
    ∀ k ≤ 5, transformedMoment t θ k = transformedMoment t η k := by
  intro k hk
  by_cases hzero : k = 0
  · subst k
    rw [transformedMoment_zero, transformedMoment_zero]
  · have hi : k - 1 < 5 := by omega
    have h := congrFun heq (⟨k - 1, hi⟩ : Fin 5)
    have hk' : k - 1 + 1 = k := by omega
    simpa only [H, hk'] using h

theorem equal_H_implies_equal_probitCells_le_five
    (t : ℝ) (θ η : GaussianSpace) (ht : 0 ≤ t)
    (hvθ0 : 0 ≤ θ 3) (hvθ1 : 0 ≤ θ 4)
    (hvη0 : 0 ≤ η 3) (hvη1 : 0 ≤ η 4)
    (heq : H t θ = H t η) (n : ℕ) (hn : n ≤ 5) :
    ∀ x : Fin n → Bool,
      probitCell (probitFromGaussian (Real.sqrt t) θ) x =
      probitCell (probitFromGaussian (Real.sqrt t) η) x := by
  apply equal_transformedMoments_implies_equal_probitCells t θ η ht
    hvθ0 hvθ1 hvη0 hvη1 n
  intro k hk
  exact equal_H_implies_equal_transformedMoments_le_five t θ η heq k (hk.trans hn)

end LCR
