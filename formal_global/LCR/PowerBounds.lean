import LCR.ComponentDifferentiation
import LCR.GaussianEnvelope

/-! Pointwise derivative bounds used to control the Gaussian moment Jacobian. -/

noncomputable section
namespace LCR

def endpointPowerY (t y : ℝ) (k : ℕ) : ℝ :=
  (k:ℝ)*((k-1:ℕ):ℝ)*hTransform t y^(k-2)*Real.exp (-t*y^2/2)^2 -
    (k:ℝ)*t*y*hTransform t y^(k-1)*Real.exp (-t*y^2/2)

def endpointPowerTime (t y : ℝ) (k : ℕ) : ℝ :=
  (k:ℝ)*((k-1:ℕ):ℝ)*hTransform t y^(k-2)*hTransformTime t y*Real.exp (-t*y^2/2) -
    (k:ℝ)*hTransform t y^(k-1)*(y^2/2)*Real.exp (-t*y^2/2)

theorem hasDerivAt_endpointPowerKernel_y (t y : ℝ) (k : ℕ) :
    HasDerivAt (fun x => endpointPowerKernel t x k) (endpointPowerY t y k) y := by
  have he : HasDerivAt (fun x : ℝ => Real.exp (-t*x^2/2))
      (-t*y*Real.exp (-t*y^2/2)) y := by
    convert ((((hasDerivAt_id y).pow 2).const_mul (-t)).div_const 2).exp using 1 <;>
      dsimp <;> ring
  have hp := (((hasDerivAt_hTransform t y).pow (k-1)).const_mul (k:ℝ)).mul he
  have hk : k-1-1 = k-2 := by omega
  convert hp using 1
  dsimp only [endpointPowerY, endpointPowerKernel, Pi.pow_apply]
  rw [hk]
  ring

theorem hasDerivAt_endpointPowerKernel_time (t y : ℝ) (k : ℕ) :
    HasDerivAt (fun s => endpointPowerKernel s y k) (endpointPowerTime t y k) t := by
  have hp := (((hasDerivAt_hTransform_time t y).pow (k-1)).const_mul (k:ℝ)).mul
    (hasDerivAt_transform_integrand_time t y)
  have hk : k-1-1 = k-2 := by omega
  convert hp using 1
  dsimp only [endpointPowerTime, endpointPowerKernel, transformTimeKernel, Pi.pow_apply]
  rw [hk]
  ring

theorem abs_endpointPowerKernel_le_envelope (t y L : ℝ) (k : ℕ)
    (ht : 0 ≤ t) (hy : |y| ≤ L) (hL : 1 ≤ L) (hk : k ≤ 5) :
    |endpointPowerKernel t y k| ≤ 5*L^4 := by
  have hL0 : 0 ≤ L := by linarith
  have hpow : |y|^(k-1) ≤ L^4 :=
    (pow_le_pow_left₀ (abs_nonneg _) hy (k-1)).trans (pow_le_pow_right₀ hL (by omega))
  calc
    |endpointPowerKernel t y k| ≤ (k:ℝ)*|y|^(k-1) := abs_endpointPowerKernel_le t y k ht
    _ ≤ 5*L^4 := by gcongr; exact_mod_cast hk

theorem abs_endpointPowerY_le_envelope (t y L : ℝ) (k : ℕ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hy : |y| ≤ L) (hL : 1 ≤ L) (hk : k ≤ 5) :
    |endpointPowerY t y k| ≤ 25*L^5 := by
  have hL0 : 0 ≤ L := by linarith
  have hh : |hTransform t y| ≤ L := (abs_hTransform_le t y ht).trans hy
  have he := exp_transform_le_one t y ht
  have he0 : 0 ≤ Real.exp (-t*y^2/2) := (Real.exp_pos _).le
  have hkR : (k:ℝ) ≤ 5 := by exact_mod_cast hk
  have hk1R : ((k-1:ℕ):ℝ) ≤ 4 := by exact_mod_cast (show k-1 ≤ 4 by omega)
  have hp2 : |hTransform t y|^(k-2) ≤ L^3 :=
    (pow_le_pow_left₀ (abs_nonneg _) hh _).trans (pow_le_pow_right₀ hL (by omega))
  have hp1 : |hTransform t y|^(k-1) ≤ L^4 :=
    (pow_le_pow_left₀ (abs_nonneg _) hh _).trans (pow_le_pow_right₀ hL (by omega))
  have hfirst : |(k:ℝ)*((k-1:ℕ):ℝ)*hTransform t y^(k-2)*Real.exp (-t*y^2/2)^2| ≤ 20*L^3 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_nonneg (Nat.cast_nonneg _), abs_pow, abs_pow, abs_of_nonneg he0]
    calc
      _ ≤ 5*4*L^3*1^2 := by gcongr
      _ = _ := by ring
  have hsecond : |(k:ℝ)*t*y*hTransform t y^(k-1)*Real.exp (-t*y^2/2)| ≤ 5*L^5 := by
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_nonneg ht, abs_pow, abs_of_nonneg he0]
    calc
      _ ≤ 5*1*L*L^4*1 := by gcongr
      _ = _ := by ring
  have h35 : L^3 ≤ L^5 := pow_le_pow_right₀ hL (by norm_num)
  calc
    |endpointPowerY t y k| ≤
      |(k:ℝ)*((k-1:ℕ):ℝ)*hTransform t y^(k-2)*Real.exp (-t*y^2/2)^2| +
      |(k:ℝ)*t*y*hTransform t y^(k-1)*Real.exp (-t*y^2/2)| := abs_sub _ _
    _ ≤ 25*L^5 := by linarith

theorem abs_endpointPowerTime_le_envelope (t y L : ℝ) (k : ℕ)
    (ht : 0 ≤ t) (hy : |y| ≤ L) (hL : 1 ≤ L) (hk : k ≤ 5) :
    |endpointPowerTime t y k| ≤ (35/6)*L^6 := by
  have hL0 : 0 ≤ L := by linarith
  have hh : |hTransform t y| ≤ L := (abs_hTransform_le t y ht).trans hy
  have he := exp_transform_le_one t y ht
  have he0 : 0 ≤ Real.exp (-t*y^2/2) := (Real.exp_pos _).le
  have hkR : (k:ℝ) ≤ 5 := by exact_mod_cast hk
  have hk1R : ((k-1:ℕ):ℝ) ≤ 4 := by exact_mod_cast (show k-1 ≤ 4 by omega)
  have hp2 : |hTransform t y|^(k-2) ≤ L^3 :=
    (pow_le_pow_left₀ (abs_nonneg _) hh _).trans (pow_le_pow_right₀ hL (by omega))
  have hp1 : |hTransform t y|^(k-1) ≤ L^4 :=
    (pow_le_pow_left₀ (abs_nonneg _) hh _).trans (pow_le_pow_right₀ hL (by omega))
  have htime : |hTransformTime t y| ≤ L^3/6 := by
    calc
      _ ≤ |y|^3/6 := abs_hTransformTime_le t y ht
      _ ≤ _ := by gcongr
  have hfirst :
      |(k:ℝ)*((k-1:ℕ):ℝ)*hTransform t y^(k-2)*hTransformTime t y*Real.exp (-t*y^2/2)| ≤
        (10/3)*L^6 := by
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_nonneg (Nat.cast_nonneg _), abs_pow, abs_of_nonneg he0]
    calc
      _ ≤ 5*4*L^3*(L^3/6)*1 := by gcongr
      _ = _ := by ring
  have hy2 : |y^2/2| ≤ L^2/2 := by
    rw [abs_div, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    gcongr
  have hsecond :
      |(k:ℝ)*hTransform t y^(k-1)*(y^2/2)*Real.exp (-t*y^2/2)| ≤ (5/2)*L^6 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _),
      abs_pow, abs_of_nonneg he0]
    calc
      _ ≤ 5*L^4*(L^2/2)*1 := by gcongr
      _ = _ := by ring
  calc
    |endpointPowerTime t y k| ≤
      |(k:ℝ)*((k-1:ℕ):ℝ)*hTransform t y^(k-2)*hTransformTime t y*Real.exp (-t*y^2/2)| +
      |(k:ℝ)*hTransform t y^(k-1)*(y^2/2)*Real.exp (-t*y^2/2)| := abs_sub _ _
    _ ≤ (35/6)*L^6 := by linarith

end LCR
