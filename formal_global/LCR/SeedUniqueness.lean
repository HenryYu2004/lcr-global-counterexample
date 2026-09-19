import LCR.AlgebraicSeed

/-! The isolating interval specifies a unique real algebraic root. -/

noncomputable section
namespace LCR.AlgebraicSeed

def pearsonDerivative (p : ℝ) : ℝ :=
  4608*p^8-15680*p^6-10368*p^5-100200*p^4+260160*p^3-
    39663*p^2-94230*p+12960

theorem hasDerivAt_pearson (p : ℝ) : HasDerivAt pearson (pearsonDerivative p) p := by
  have hi := hasDerivAt_id p
  have h0 := (hi.pow 9).const_mul (512 : ℝ)
  have h1 := h0.sub ((hi.pow 7).const_mul 2240)
  have h2 := h1.sub ((hi.pow 6).const_mul 1728)
  have h3 := h2.sub ((hi.pow 5).const_mul 20040)
  have h4 := h3.add ((hi.pow 4).const_mul 65040)
  have h5 := h4.sub ((hi.pow 3).const_mul 13221)
  have h6 := h5.sub ((hi.pow 2).const_mul 47115)
  have h7 := h6.add (hi.const_mul 12960)
  convert h7.add_const 5832 using 1
  dsimp [pearsonDerivative]
  ring

theorem pearsonDerivative_neg {p : ℝ}
    (hlo : 634/1000 < p) (hhi : p < 635/1000) : pearsonDerivative p < 0 := by
  obtain ⟨hp,hp2,hp3⟩ := basic_bounds hlo hhi
  have hp1 : p ≤ 1 := by linarith
  have hp8 : p^8 ≤ 1 := pow_le_one₀ hp.le hp1
  have hp4 : (4/25 : ℝ) < p^4 := by
    nlinarith [sq_nonneg (p^2-2/5)]
  have hp5 : 0 ≤ p^5 := pow_nonneg hp.le _
  have hp6 : 0 ≤ p^6 := pow_nonneg hp.le _
  unfold pearsonDerivative
  nlinarith [hp2.1,hp3.2]

theorem pearson_strictAntiOn_interval :
    StrictAntiOn pearson (Set.Ioo (634/1000) (635/1000)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo _ _)
  · exact (by unfold pearson; fun_prop : Continuous pearson).continuousOn
  · intro p hp
    have hp' : p ∈ Set.Ioo (634/1000 : ℝ) (635/1000) := by simpa using hp
    rw [(hasDerivAt_pearson p).deriv]
    exact pearsonDerivative_neg hp'.1 hp'.2

theorem seed_root_unique {p : ℝ}
    (hlo : 634/1000 < p) (hhi : p < 635/1000) (hroot : pearson p = 0) : p = pStar := by
  exact pearson_strictAntiOn_interval.injOn ⟨hlo,hhi⟩
    ⟨pStar_spec.1,pStar_spec.2.1⟩ (hroot.trans pStar_spec.2.2.symm)

theorem existsUnique_seed_root :
    ∃! p : ℝ, 634/1000 < p ∧ p < 635/1000 ∧ pearson p = 0 := by
  exact ⟨pStar,pStar_spec, fun p hp => seed_root_unique hp.1 hp.2.1 hp.2.2⟩

end LCR.AlgebraicSeed
