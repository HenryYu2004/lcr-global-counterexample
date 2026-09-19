import Mathlib

/-! Exact real-algebraic seed for the five-moment two-normal-mixture alias. -/

namespace LCR.AlgebraicSeed

noncomputable section

def pearson (p : ℝ) : ℝ :=
  512*p^9 - 2240*p^7 - 1728*p^6 - 20040*p^5 + 65040*p^4
    - 13221*p^3 - 47115*p^2 + 12960*p + 5832

def otherFactor (p : ℝ) : ℝ :=
  512*p^8 + 512*p^7 - 1728*p^6 - 3456*p^5 - 23496*p^4
    + 41544*p^3 + 28323*p^2 - 18792*p - 5832

theorem pearson_factorization (p : ℝ) :
    pearson p = (p - 1) * otherFactor p := by
  unfold pearson otherFactor
  ring

theorem pearson_cleared (p : ℝ) :
    pearson p =
      6*(24*p^3 - 80*p^2 + 45*p + 54)^2
      - (9 + 5*p - 8*p^3)*(36 - 8*p^3 + 15*p)^2 := by
  unfold pearson
  ring

theorem pearson_left_pos : 0 < pearson (634 / 1000) := by
  norm_num [pearson]

theorem pearson_right_neg : pearson (635 / 1000) < 0 := by
  norm_num [pearson]

theorem exists_seed_root :
    ∃ p : ℝ, 634 / 1000 < p ∧ p < 635 / 1000 ∧ pearson p = 0 := by
  have hc : Continuous pearson := by unfold pearson; fun_prop
  have hab : (634 / 1000 : ℝ) ≤ 635 / 1000 := by norm_num
  have hzero : (0 : ℝ) ∈ Set.Icc (pearson (635 / 1000)) (pearson (634 / 1000)) :=
    ⟨le_of_lt pearson_right_neg, le_of_lt pearson_left_pos⟩
  obtain ⟨p, hp, hz⟩ := intermediate_value_Icc' hab hc.continuousOn hzero
  refine ⟨p, ?_, ?_, hz⟩
  · have hne : p ≠ 634 / 1000 := by
      intro h
      subst p
      linarith [pearson_left_pos]
    exact lt_of_le_of_ne hp.1 (Ne.symm hne)
  · have hne : p ≠ 635 / 1000 := by
      intro h
      subst p
      linarith [pearson_right_neg]
    exact lt_of_le_of_ne hp.2 hne

noncomputable def pStar : ℝ := Classical.choose exists_seed_root

theorem pStar_spec :
    634 / 1000 < pStar ∧ pStar < 635 / 1000 ∧ pearson pStar = 0 :=
  Classical.choose_spec exists_seed_root

def numC (p : ℝ) : ℝ := 24*p^3 - 80*p^2 + 45*p + 54
def denBase (p : ℝ) : ℝ := 36 - 8*p^3 + 15*p
def cOf (p : ℝ) : ℝ := numC p / (2*p*denBase p)
def sOf (p : ℝ) : ℝ := 3/(2*p) - 3*cOf p
noncomputable def deltaOf (p : ℝ) : ℝ := Real.sqrt ((sOf p)^2 + 4*p)
noncomputable def mu0Of (p : ℝ) : ℝ := (sOf p - deltaOf p)/2
noncomputable def mu1Of (p : ℝ) : ℝ := (sOf p + deltaOf p)/2
noncomputable def piOf (p : ℝ) : ℝ := -mu0Of p / deltaOf p
noncomputable def variance0Of (p : ℝ) : ℝ := 5/2-p+cOf p*mu0Of p
noncomputable def variance1Of (p : ℝ) : ℝ := 5/2-p+cOf p*mu1Of p

theorem seed_p_pos : 0 < pStar := by linarith [pStar_spec.1]

theorem basic_bounds {p : ℝ} (hlo : 634 / 1000 < p) (hhi : p < 635 / 1000) :
    (0 < p) ∧ (401 / 1000 < p^2 ∧ p^2 < 404 / 1000) ∧
    (254 / 1000 < p^3 ∧ p^3 < 257 / 1000) := by
  have hp : 0 < p := by linarith
  have h2l : (634 / 1000 : ℝ)^2 < p^2 := by nlinarith
  have h2u : p^2 < (635 / 1000 : ℝ)^2 := by nlinarith
  have h3l : (634 / 1000 : ℝ)^3 < p^3 := by nlinarith [mul_pos hp (sub_pos.mpr h2l)]
  have h3u : p^3 < (635 / 1000 : ℝ)^3 := by nlinarith [mul_pos hp (sub_pos.mpr h2u)]
  exact ⟨hp, by constructor <;> nlinarith, by constructor <;> nlinarith⟩

theorem denBase_bounds {p : ℝ} (hlo : 634 / 1000 < p) (hhi : p < 635 / 1000) :
    43 < denBase p ∧ denBase p < 44 := by
  obtain ⟨_, _, h3⟩ := basic_bounds hlo hhi
  unfold denBase
  constructor <;> nlinarith [h3.1, h3.2]

theorem cOf_bounds {p : ℝ} (hlo : 634 / 1000 < p) (hhi : p < 635 / 1000) :
    1 < cOf p ∧ cOf p < 21/20 := by
  obtain ⟨hp, h2, h3⟩ := basic_bounds hlo hhi
  have hd := denBase_bounds hlo hhi
  have hdpos : 0 < denBase p := by linarith [hd.1]
  have hden : 0 < 2*p*denBase p := by positivity
  have hdenLo : 2*(634/1000)*43 < 2*p*denBase p := by nlinarith [mul_pos (sub_pos.mpr hlo) (sub_pos.mpr hd.1)]
  have hdenHi : 2*p*denBase p < 2*(635/1000)*44 := by nlinarith [mul_pos (sub_pos.mpr hhi) (sub_pos.mpr hd.2)]
  constructor
  · rw [cOf, lt_div_iff₀ hden]
    unfold numC
    nlinarith [h2.2, h3.1]
  · rw [cOf, div_lt_iff₀ hden]
    unfold numC
    nlinarith [h2.1, h3.2]

theorem sOf_bounds {p : ℝ} (hlo : 634 / 1000 < p) (hhi : p < 635 / 1000) :
    -(4/5) < sOf p ∧ sOf p < -(3/5) := by
  have hp : 0 < 2*p := by linarith
  have hc := cOf_bounds hlo hhi
  have hrlo : (47/20 : ℝ) < 3/(2*p) := by
    rw [lt_div_iff₀ hp]
    linarith
  have hrhi : 3/(2*p) < (12/5 : ℝ) := by
    rw [div_lt_iff₀ hp]
    linarith
  unfold sOf
  constructor <;> linarith [hc.1, hc.2]

theorem deltaOf_bounds {p : ℝ} (hlo : 634 / 1000 < p) (hhi : p < 635 / 1000) :
    8/5 < deltaOf p ∧ deltaOf p < 9/5 := by
  have hs := sOf_bounds hlo hhi
  have hp : 0 < p := by linarith
  have hn : 0 ≤ (sOf p)^2 + 4*p := by positivity
  have hd : 0 ≤ deltaOf p := Real.sqrt_nonneg _
  have hd2 : (deltaOf p)^2 = (sOf p)^2 + 4*p := Real.sq_sqrt hn
  have hs2lo : (3/5 : ℝ)^2 < (sOf p)^2 := by nlinarith [hs.2]
  have hs2hi : (sOf p)^2 < (4/5 : ℝ)^2 := by nlinarith [hs.1, hs.2]
  constructor <;> nlinarith

theorem means_bounds {p : ℝ} (hlo : 634 / 1000 < p) (hhi : p < 635 / 1000) :
    (-(13/10) < mu0Of p ∧ mu0Of p < -(11/10)) ∧
    (2/5 < mu1Of p ∧ mu1Of p < 3/5) := by
  have hs := sOf_bounds hlo hhi
  have hd := deltaOf_bounds hlo hhi
  unfold mu0Of mu1Of
  constructor <;> constructor <;> linarith [hs.1, hs.2, hd.1, hd.2]

theorem piOf_bounds {p : ℝ} (hlo : 634 / 1000 < p) (hhi : p < 635 / 1000) :
    1/2 < piOf p ∧ piOf p < 3/4 := by
  have hs := sOf_bounds hlo hhi
  have hd := deltaOf_bounds hlo hhi
  have hdpos : 0 < deltaOf p := by linarith [hd.1]
  unfold piOf
  constructor
  · rw [lt_div_iff₀ hdpos]
    unfold mu0Of
    linarith [hs.2]
  · rw [div_lt_iff₀ hdpos]
    unfold mu0Of
    linarith [hs.1, hd.1]

theorem variances_bounds {p : ℝ} (hlo : 634 / 1000 < p) (hhi : p < 635 / 1000) :
    (1/2 < variance0Of p ∧ variance0Of p < 3) ∧
    (1/2 < variance1Of p ∧ variance1Of p < 3) := by
  have hc := cOf_bounds hlo hhi
  have hm := means_bounds hlo hhi
  have hcpos : 0 < cOf p := by linarith [hc.1]
  have hm0neg : mu0Of p < 0 := by linarith [hm.1.2]
  have hm1pos : 0 < mu1Of p := by linarith [hm.2.1]
  have hprod0lo := mul_pos hcpos (sub_pos.mpr hm.1.1)
  have hprod0hi := mul_neg_of_pos_of_neg hcpos hm0neg
  have hprod1lo := mul_pos hcpos hm1pos
  have hprod1hi := mul_pos hcpos (sub_pos.mpr hm.2.2)
  unfold variance0Of variance1Of
  constructor <;> constructor <;> nlinarith [hc.1, hc.2]

theorem seed_admissible :
    (1/2 < piOf pStar ∧ piOf pStar < 3/4) ∧
    (mu0Of pStar < 0 ∧ 0 < mu1Of pStar) ∧
    (1/2 < variance0Of pStar ∧ variance0Of pStar < 3) ∧
    (1/2 < variance1Of pStar ∧ variance1Of pStar < 3) := by
  have hp := pStar_spec
  have hm := means_bounds hp.1 hp.2.1
  exact ⟨piOf_bounds hp.1 hp.2.1, ⟨by linarith [hm.1.2], by linarith [hm.2.1]⟩,
    variances_bounds hp.1 hp.2.1⟩

def cumulant3 (p s c : ℝ) : ℝ := p*(s+3*c)
def cumulant4 (p s c : ℝ) : ℝ := p*(s^2-2*p+6*c*s+3*c^2)
def cumulant5 (p s c : ℝ) : ℝ := p*(s^3-8*p*s+10*c*(s^2-2*p)+15*c^2*s)

theorem fourth_identity (p s c : ℝ) :
    (cumulant3 p s c)^2 - 2*p^3 - p*cumulant4 p s c = 6*p^2*c^2 := by
  unfold cumulant3 cumulant4
  ring

theorem fifth_identity (p s c : ℝ) :
    c*p*(4*(cumulant3 p s c)^2-2*p^3-3*cumulant4 p s c*p) =
    cumulant5 p s c*p^2 + 2*(cumulant3 p s c)^3 +
      2*cumulant3 p s c*p^3 - 3*cumulant3 p s c*cumulant4 p s c*p := by
  unfold cumulant3 cumulant4 cumulant5
  ring

theorem cOf_mul_den {p : ℝ} (hlo : 634 / 1000 < p) (hhi : p < 635 / 1000) :
    cOf p * (2*p*denBase p) = numC p := by
  have hp : p ≠ 0 := by linarith
  have hd : denBase p ≠ 0 := by linarith [(denBase_bounds hlo hhi).1]
  unfold cOf
  field_simp

theorem seed_cumulants {p : ℝ} (hlo : 634 / 1000 < p) (hhi : p < 635 / 1000)
    (hroot : pearson p = 0) :
    cumulant3 p (sOf p) (cOf p) = 3/2 ∧
    cumulant4 p (sOf p) (cOf p) = -(5/4) ∧
    cumulant5 p (sOf p) (cOf p) = -10 := by
  have hp : p ≠ 0 := by linarith
  have hd : denBase p ≠ 0 := by linarith [(denBase_bounds hlo hhi).1]
  have hcden := cOf_mul_den hlo hhi
  have hc2 : 24*p^2*(cOf p)^2 = 9+5*p-8*p^3 := by
    have hfac : (24*p^2*(cOf p)^2-(9+5*p-8*p^3))*(denBase p)^2 = 0 := by
      calc
        _ = 6*(cOf p*(2*p*denBase p))^2 - (9+5*p-8*p^3)*(denBase p)^2 := by ring
        _ = pearson p := by rw [hcden, pearson_cleared]; unfold numC denBase; ring
        _ = 0 := hroot
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_right (pow_ne_zero 2 hd))
  have hk : cumulant3 p (sOf p) (cOf p) = 3/2 := by
    unfold cumulant3 sOf
    field_simp
    ring
  have hl : cumulant4 p (sOf p) (cOf p) = -(5/4) := by
    have hid := fourth_identity p (sOf p) (cOf p)
    rw [hk] at hid
    have hf : p*(cumulant4 p (sOf p) (cOf p)+5/4) = 0 := by nlinarith only [hid, hc2]
    have := (mul_eq_zero.mp hf).resolve_left hp
    linarith
  have hr : cumulant5 p (sOf p) (cOf p) = -10 := by
    have hid := fifth_identity p (sOf p) (cOf p)
    rw [hk, hl] at hid
    unfold numC denBase at hcden
    have hf : p^2*(cumulant5 p (sOf p) (cOf p)+10) = 0 := by nlinarith only [hid, hcden]
    have := (mul_eq_zero.mp hf).resolve_left (pow_ne_zero 2 hp)
    linarith
  exact ⟨hk, hl, hr⟩

def discreteMoment (w a b : ℝ) (n : ℕ) : ℝ := (1-w)*a^n+w*b^n

theorem discreteMoment_zero (w a b : ℝ) : discreteMoment w a b 0 = 1 := by
  unfold discreteMoment
  ring

theorem discreteMoment_recurrence (w a b p s : ℝ)
    (ha : a^2 = s*a+p) (hb : b^2 = s*b+p) (n : ℕ) :
    discreteMoment w a b (n+2) =
      s*discreteMoment w a b (n+1)+p*discreteMoment w a b n := by
  have hpa : a^(n+2) = s*a^(n+1)+p*a^n := by
    rw [pow_add, ha, pow_succ]
    ring
  have hpb : b^(n+2) = s*b^(n+1)+p*b^n := by
    rw [pow_add, hb, pow_succ]
    ring
  unfold discreteMoment
  rw [hpa, hpb]
  ring

theorem root_means_quadratic {p : ℝ} (hlo : 634 / 1000 < p) :
    (mu0Of p)^2 = sOf p*mu0Of p+p ∧
    (mu1Of p)^2 = sOf p*mu1Of p+p := by
  have hp : 0 < p := by linarith
  have hn : 0 ≤ (sOf p)^2+4*p := by positivity
  have hd2 : (deltaOf p)^2 = (sOf p)^2+4*p := Real.sq_sqrt hn
  unfold mu0Of mu1Of
  constructor <;> nlinarith only [hd2]

theorem root_discrete_first {p : ℝ} (hlo : 634 / 1000 < p) (hhi : p < 635 / 1000) :
    discreteMoment (piOf p) (mu0Of p) (mu1Of p) 1 = 0 := by
  have hd : deltaOf p ≠ 0 := by linarith [(deltaOf_bounds hlo hhi).1]
  unfold discreteMoment piOf
  simp only [pow_one]
  field_simp
  unfold mu0Of mu1Of
  ring

theorem discreteMoment_values (w a b p s : ℝ)
    (ha : a^2 = s*a+p) (hb : b^2 = s*b+p)
    (h1 : discreteMoment w a b 1 = 0) :
    discreteMoment w a b 2 = p ∧
    discreteMoment w a b 3 = p*s ∧
    discreteMoment w a b 4 = p*(s^2+p) ∧
    discreteMoment w a b 5 = p*s*(s^2+2*p) := by
  have h0 := discreteMoment_zero w a b
  have h2 := discreteMoment_recurrence w a b p s ha hb 0
  norm_num only [Nat.reduceAdd] at h2
  rw [h0, h1] at h2
  ring_nf at h2
  have h3 := discreteMoment_recurrence w a b p s ha hb 1
  norm_num only [Nat.reduceAdd] at h3
  rw [h1, h2] at h3
  have h4 := discreteMoment_recurrence w a b p s ha hb 2
  norm_num only [Nat.reduceAdd] at h4
  rw [h2, h3] at h4
  have h5 := discreteMoment_recurrence w a b p s ha hb 3
  norm_num only [Nat.reduceAdd] at h5
  rw [h3, h4] at h5
  refine ⟨h2, ?_, ?_, ?_⟩ <;> nlinarith only [h3, h4, h5]

/-- Normal raw-moment polynomials through order five; higher orders are unused. -/
def normalMomentPolynomial (μ v : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => μ
  | 2 => μ^2+v
  | 3 => μ^3+3*μ*v
  | 4 => μ^4+6*μ^2*v+3*v^2
  | 5 => μ^5+10*μ^3*v+15*μ*v^2
  | _ => 0

def mixtureMomentPolynomial (w a b va vb : ℝ) (n : ℕ) : ℝ :=
  (1-w)*normalMomentPolynomial a va n+w*normalMomentPolynomial b vb n

theorem mixture_moments_from_discrete (w a b p s c v : ℝ)
    (ha : a^2 = s*a+p) (hb : b^2 = s*b+p)
    (h1 : discreteMoment w a b 1 = 0) :
    mixtureMomentPolynomial w a b (v+c*a) (v+c*b) 1 = 0 ∧
    mixtureMomentPolynomial w a b (v+c*a) (v+c*b) 2 = p+v ∧
    mixtureMomentPolynomial w a b (v+c*a) (v+c*b) 3 = cumulant3 p s c ∧
    mixtureMomentPolynomial w a b (v+c*a) (v+c*b) 4 = cumulant4 p s c+3*(p+v)^2 ∧
    mixtureMomentPolynomial w a b (v+c*a) (v+c*b) 5 =
      cumulant5 p s c+10*(p+v)*cumulant3 p s c := by
  obtain ⟨h2,h3,h4,h5⟩ := discreteMoment_values w a b p s ha hb h1
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa [mixtureMomentPolynomial, normalMomentPolynomial, discreteMoment] using h1
  · calc
      _ = discreteMoment w a b 2+c*discreteMoment w a b 1+v := by
        unfold mixtureMomentPolynomial discreteMoment
        simp only [normalMomentPolynomial]
        ring
      _ = _ := by rw [h2,h1]; ring
  · calc
      _ = discreteMoment w a b 3+3*v*discreteMoment w a b 1+
          3*c*discreteMoment w a b 2 := by
        unfold mixtureMomentPolynomial discreteMoment
        simp only [normalMomentPolynomial]
        ring
      _ = _ := by rw [h3,h2,h1]; unfold cumulant3; ring
  · calc
      _ = discreteMoment w a b 4+6*v*discreteMoment w a b 2+
          6*c*discreteMoment w a b 3+3*v^2+
          6*v*c*discreteMoment w a b 1+3*c^2*discreteMoment w a b 2 := by
        unfold mixtureMomentPolynomial discreteMoment
        simp only [normalMomentPolynomial]
        ring
      _ = _ := by rw [h4,h3,h2,h1]; unfold cumulant4; ring
  · calc
      _ = discreteMoment w a b 5+10*v*discreteMoment w a b 3+
          10*c*discreteMoment w a b 4+15*v^2*discreteMoment w a b 1+
          30*v*c*discreteMoment w a b 2+15*c^2*discreteMoment w a b 3 := by
        unfold mixtureMomentPolynomial discreteMoment
        simp only [normalMomentPolynomial]
        ring
      _ = _ := by rw [h5,h4,h3,h2,h1]; unfold cumulant5 cumulant3; ring

theorem algebraic_seed_moments :
    mixtureMomentPolynomial (piOf pStar) (mu0Of pStar) (mu1Of pStar)
      (variance0Of pStar) (variance1Of pStar) 1 = 0 ∧
    mixtureMomentPolynomial (piOf pStar) (mu0Of pStar) (mu1Of pStar)
      (variance0Of pStar) (variance1Of pStar) 2 = 5/2 ∧
    mixtureMomentPolynomial (piOf pStar) (mu0Of pStar) (mu1Of pStar)
      (variance0Of pStar) (variance1Of pStar) 3 = 3/2 ∧
    mixtureMomentPolynomial (piOf pStar) (mu0Of pStar) (mu1Of pStar)
      (variance0Of pStar) (variance1Of pStar) 4 = 35/2 ∧
    mixtureMomentPolynomial (piOf pStar) (mu0Of pStar) (mu1Of pStar)
      (variance0Of pStar) (variance1Of pStar) 5 = 55/2 := by
  obtain ⟨hlo,hhi,hroot⟩ := pStar_spec
  obtain ⟨ha,hb⟩ := root_means_quadratic hlo
  have h1 := root_discrete_first hlo hhi
  have hm := mixture_moments_from_discrete (piOf pStar) (mu0Of pStar) (mu1Of pStar)
    pStar (sOf pStar) (cOf pStar) (5/2-pStar) ha hb h1
  obtain ⟨hk,hl,hr⟩ := seed_cumulants hlo hhi hroot
  change _ ∧ _ ∧ _ ∧ _ ∧ _ at hm
  dsimp only [variance0Of, variance1Of]
  rcases hm with ⟨hm1,hm2,hm3,hm4,hm5⟩
  refine ⟨hm1,?_,?_,?_,?_⟩
  · linarith
  · simpa only [hk] using hm3
  · rw [hl] at hm4
    convert hm4 using 1 <;> ring
  · rw [hr,hk] at hm5
    convert hm5 using 1 <;> ring

theorem rational_seed_moments :
    mixtureMomentPolynomial (1/2) (-1) 1 1 2 1 = 0 ∧
    mixtureMomentPolynomial (1/2) (-1) 1 1 2 2 = 5/2 ∧
    mixtureMomentPolynomial (1/2) (-1) 1 1 2 3 = 3/2 ∧
    mixtureMomentPolynomial (1/2) (-1) 1 1 2 4 = 35/2 ∧
    mixtureMomentPolynomial (1/2) (-1) 1 1 2 5 = 55/2 := by
  norm_num [mixtureMomentPolynomial, normalMomentPolynomial]

end
end LCR.AlgebraicSeed
