import Mathlib

namespace Work.LadderP

/-- `(a^n)^P = a^(P*n)` (the exponent ordering is normalised so that the numerical
exponent sits on the left, as it does in the transfer statement). -/
private lemma pow_pow_P (P : ℕ) (a : ℝ) (n : ℕ) : (a^n)^P = a^(P*n) := by
  rw [← pow_mul, Nat.mul_comm]

/-- `(a*b*c)^n = a^n*b^n*c^n`. -/
private lemma mul_pow_three (a b c : ℝ) (n : ℕ) : (a*b*c)^n = a^n*b^n*c^n := by
  rw [mul_pow, mul_pow]

/-- Transfer of the ladder data from the `(C_t, γ, P·e)` normalisation to the
`(C_h, γr, e)` normalisation.  The two shape facts used are
`C_t ≤ C_h·2^{-e}` (so `C_t·γ^{P·e} ≤ C_h·γr^e` once `γ^P/2 ≤ γr`) and the *consistency*
of the two `P·e`-bounds `hDs`, `hNd`, which forces `C_h·γr^e·M₂ ≥ 1`; that last bound is
what converts the `P·e`-power hypothesis `hNd` into the `e`-power conclusion. -/
theorem pTransfer {P : ℕ} (hP : 1 ≤ P) {M₁ M₂ D e : ℕ} {C_t C_h γ η γr : ℝ}
    (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂) (hD : 1 ≤ D)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hη0 : 0 < η)
    (hCt0 : 0 < C_t) (hCh0 : 0 < C_h) (hCh1 : C_h ≤ 1) (he : 1 ≤ e)
    (hCt : C_t ≤ C_h * (1 / 2 : ℝ) ^ e)
    (hη : η ≤ C_t * γ ^ (P * e))
    (hDs : (D : ℝ) ≤ C_t * (γ * η) ^ (P * e) * ((M₁ : ℝ) * (M₂ : ℝ)))
    (hNd : ((M₁ : ℝ) * (M₂ : ℝ)) ^ (P * e) ≤ C_t * (γ * η * (D : ℝ)) ^ (P * e) * (M₂ : ℝ))
    (hgr : γ ^ P / 2 ≤ γr) (hgr1 : γr ≤ 1) :
    0 < γr ∧ η ≤ C_h * γr ^ e ∧
      (D : ℝ) ≤ C_h * (γr * η) ^ e * ((M₁ : ℝ) * (M₂ : ℝ)) ∧
      ((M₁ : ℝ) * (M₂ : ℝ)) ^ e ≤ C_h * (γr * η * (D : ℝ)) ^ e * (M₂ : ℝ) := by
  have hM2nn : (0:ℝ) ≤ (M₂:ℝ) := Nat.cast_nonneg M₂
  have hM2pos : (0:ℝ) < (M₂:ℝ) := by exact_mod_cast hM₂
  have hDnn : (0:ℝ) ≤ (D:ℝ) := Nat.cast_nonneg D
  have hγnn : (0:ℝ) ≤ γ := le_of_lt hγ0
  have hηnn : (0:ℝ) ≤ η := le_of_lt hη0
  have hγηnn : (0:ℝ) ≤ γ*η := by positivity
  have hSnn : (0:ℝ) ≤ (M₁:ℝ)*(M₂:ℝ) := by positivity
  have hSpos : (0:ℝ) < (M₁:ℝ)*(M₂:ℝ) := by positivity
  have hSexpPos : (0:ℝ) < ((M₁:ℝ)*(M₂:ℝ))^(P*e) := pow_pos hSpos _
  have hPne : P ≠ 0 := by omega
  -- γr is positive
  have hγrpos : 0 < γr := by
    have : 0 < γ ^ P / 2 := by positivity
    linarith
  -- the shape fact: `C_t·γ^{P·e} ≤ C_h·γr^e`
  have hCtγ : C_t * γ^(P*e) ≤ C_h * γr^e := by
    have hγPe : γ ^ (P*e) = (γ^P)^e := by rw [pow_mul]
    have hhalf_γ : (1/2:ℝ)^e * γ^(P*e) = ((1/2)*γ^P)^e := by rw [hγPe, ← mul_pow]
    have h2 : (1/2)*γ^P ≤ γr := by linarith
    have hγr_e : ((1/2)*γ^P)^e ≤ γr^e := pow_le_pow_left₀ (by positivity) h2 e
    calc C_t * γ^(P*e)
        ≤ (C_h * (1/2)^e) * γ^(P*e) := mul_le_mul_of_nonneg_right hCt (pow_nonneg hγnn (P*e))
      _ = C_h * ((1/2)^e * γ^(P*e)) := by ring
      _ = C_h * ((1/2)*γ^P)^e := by rw [hhalf_γ]
      _ ≤ C_h * γr^e := mul_le_mul_of_nonneg_left hγr_e (le_of_lt hCh0)
  have hηCB : η ≤ C_h * γr^e := le_trans hη hCtγ
  have hγre1 : γr^e ≤ 1 := pow_le_one₀ (le_of_lt hγrpos) hgr1
  have hCm1 : C_h * γr^e ≤ 1 := by nlinarith [hCh0, hCh1, hγre1]
  have hη1 : η ≤ 1 := by linarith
  have hηPe1 : η^(P*e) ≤ 1 := pow_le_one₀ hηnn hη1
  have hXnn : 0 ≤ C_t*(γ*η)^(P*e) := by positivity
  have hX1 : C_t * (γ*η)^(P*e) ≤ C_h * γr^e := by
    rw [mul_pow]
    calc C_t * (γ^(P*e)*η^(P*e)) = (C_t*γ^(P*e))*η^(P*e) := by ring
      _ ≤ (C_h*γr^e)*η^(P*e) := mul_le_mul_of_nonneg_right hCtγ (pow_nonneg hηnn _)
      _ ≤ (C_h*γr^e)*1 := mul_le_mul_of_nonneg_left hηPe1 (by positivity)
      _ = C_h*γr^e := by ring
  have hXle : C_t * (γ*η)^(P*e) ≤ 1 := le_trans hX1 hCm1
  have hXpow_le : (C_t*(γ*η)^(P*e))^(P*e+1) ≤ C_t*(γ*η)^(P*e) := by
    rw [pow_succ]
    have h1 : (C_t*(γ*η)^(P*e))^(P*e) ≤ 1 := pow_le_one₀ hXnn hXle
    have h := mul_le_mul_of_nonneg_right h1 hXnn
    simpa using h
  -- the consistency of `hDs` with `hNd`
  have hDpow : (D:ℝ)^(P*e) ≤ (C_t*(γ*η)^(P*e)*((M₁:ℝ)*(M₂:ℝ)))^(P*e) :=
    pow_le_pow_left₀ hDnn hDs _
  have hkey : ((M₁:ℝ)*(M₂:ℝ))^(P*e)
      ≤ (C_t*(γ*η)^(P*e))^(P*e+1) * ((M₁:ℝ)*(M₂:ℝ))^(P*e) * (M₂:ℝ) := by
    calc ((M₁:ℝ)*(M₂:ℝ))^(P*e)
        ≤ C_t * (γ*η*(D:ℝ))^(P*e) * (M₂:ℝ) := hNd
      _ = C_t * ((γ*η)^(P*e) * (D:ℝ)^(P*e)) * (M₂:ℝ) := by rw [mul_pow]
      _ ≤ C_t * ((γ*η)^(P*e) * (C_t*(γ*η)^(P*e)*((M₁:ℝ)*(M₂:ℝ)))^(P*e)) * (M₂:ℝ) := by
            have h1 : (γ*η)^(P*e) * (D:ℝ)^(P*e)
                ≤ (γ*η)^(P*e) * (C_t*(γ*η)^(P*e)*((M₁:ℝ)*(M₂:ℝ)))^(P*e) :=
              mul_le_mul_of_nonneg_left hDpow (pow_nonneg hγηnn _)
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (le_of_lt hCt0)) (le_of_lt hM2pos)
      _ = (C_t*(γ*η)^(P*e))^(P*e+1) * ((M₁:ℝ)*(M₂:ℝ))^(P*e) * (M₂:ℝ) := by
            rw [mul_pow, pow_succ]
            ring
  have hraw : 1 ≤ (C_t*(γ*η)^(P*e))^(P*e+1) * (M₂:ℝ) := by
    have hkey' : ((M₁:ℝ)*(M₂:ℝ))^(P*e)
        ≤ (C_t*(γ*η)^(P*e))^(P*e+1) * (M₂:ℝ) * ((M₁:ℝ)*(M₂:ℝ))^(P*e) := by
      calc ((M₁:ℝ)*(M₂:ℝ))^(P*e)
          ≤ (C_t*(γ*η)^(P*e))^(P*e+1) * ((M₁:ℝ)*(M₂:ℝ))^(P*e) * (M₂:ℝ) := hkey
        _ = (C_t*(γ*η)^(P*e))^(P*e+1) * (M₂:ℝ) * ((M₁:ℝ)*(M₂:ℝ))^(P*e) := by ring
    have hone : (1:ℝ) * ((M₁:ℝ)*(M₂:ℝ))^(P*e)
        ≤ (C_t*(γ*η)^(P*e))^(P*e+1) * (M₂:ℝ) * ((M₁:ℝ)*(M₂:ℝ))^(P*e) := by
      simpa using hkey'
    exact le_of_mul_le_mul_right hone hSexpPos
  have hXM2 : 1 ≤ C_t*(γ*η)^(P*e) * (M₂:ℝ) :=
    le_trans hraw (mul_le_mul_of_nonneg_right hXpow_le hM2nn)
  -- the crux: `1 ≤ C_h·γr^e·M₂`
  have hCmγrM2 : 1 ≤ C_h*γr^e*(M₂:ℝ) := by
    have h1 : C_t*(γ*η)^(P*e)*(M₂:ℝ) ≤ C_h*γr^e*(M₂:ℝ) :=
      mul_le_mul_of_nonneg_right hX1 hM2nn
    linarith
  have hηPe_le : η^(P*e) ≤ η^e := by
    have hPe_ge : e ≤ P*e := by
      calc e = 1*e := by rw [one_mul]
        _ ≤ P*e := Nat.mul_le_mul_right e hP
    exact pow_le_pow_of_le_one hηnn hη1 hPe_ge
  have hWP : (C_h*γr^e*(M₂:ℝ))^P = C_h^P*γr^(P*e)*(M₂:ℝ)^P := by
    simp only [mul_pow, pow_pow_P]
  have hZP : (C_h*γr^e*η^e*(D:ℝ)^e*(M₂:ℝ))^P
      = C_h^P*γr^(P*e)*η^(P*e)*(D:ℝ)^(P*e)*(M₂:ℝ)^P := by
    simp only [mul_pow, pow_pow_P]
  have hmain : ((M₁:ℝ)*(M₂:ℝ))^(P*e)
      ≤ C_h^P*γr^(P*e)*η^(P*e)*(D:ℝ)^(P*e)*(M₂:ℝ)^P := by
    calc ((M₁:ℝ)*(M₂:ℝ))^(P*e)
        ≤ C_t*(γ*η*(D:ℝ))^(P*e)*(M₂:ℝ) := hNd
      _ = C_t*γ^(P*e)*η^(P*e)*(D:ℝ)^(P*e)*(M₂:ℝ) := by rw [mul_pow_three]; ring
      _ ≤ C_h*γr^e*η^(P*e)*(D:ℝ)^(P*e)*(M₂:ℝ) := by gcongr
      _ = (C_h*γr^e*(M₂:ℝ))*(η^(P*e)*(D:ℝ)^(P*e)) := by ring
      _ ≤ (C_h*γr^e*(M₂:ℝ))^P*(η^(P*e)*(D:ℝ)^(P*e)) :=
            mul_le_mul_of_nonneg_right (le_self_pow₀ hCmγrM2 hPne) (by positivity)
      _ = C_h^P*γr^(P*e)*(M₂:ℝ)^P*(η^(P*e)*(D:ℝ)^(P*e)) := by rw [hWP]
      _ = C_h^P*γr^(P*e)*η^(P*e)*(D:ℝ)^(P*e)*(M₂:ℝ)^P := by ring
  have hfact : C_h*(γr*η*(D:ℝ))^e*(M₂:ℝ) = C_h*γr^e*η^e*(D:ℝ)^e*(M₂:ℝ) := by
    rw [mul_pow, mul_pow]; ring
  have hconj3 : ((M₁:ℝ)*(M₂:ℝ))^e ≤ C_h*(γr*η*(D:ℝ))^e*(M₂:ℝ) := by
    rw [hfact]
    refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) hPne).mp ?_
    rw [pow_pow_P, hZP]
    exact hmain
  have hfact2 : C_h*(γr*η)^e*((M₁:ℝ)*(M₂:ℝ)) = C_h*γr^e*η^e*((M₁:ℝ)*(M₂:ℝ)) := by
    rw [mul_pow]; ring
  have hconj2 : (D:ℝ) ≤ C_h*(γr*η)^e*((M₁:ℝ)*(M₂:ℝ)) := by
    rw [hfact2]
    calc (D:ℝ)
        ≤ C_t*(γ*η)^(P*e)*((M₁:ℝ)*(M₂:ℝ)) := hDs
      _ = C_t*γ^(P*e)*η^(P*e)*((M₁:ℝ)*(M₂:ℝ)) := by rw [mul_pow]; ring
      _ ≤ C_h*γr^e*η^(P*e)*((M₁:ℝ)*(M₂:ℝ)) := by gcongr
      _ ≤ C_h*γr^e*η^e*((M₁:ℝ)*(M₂:ℝ)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hηPe_le (by positivity)) hSnn
  exact ⟨hγrpos, hηCB, hconj2, hconj3⟩

end Work.LadderP
