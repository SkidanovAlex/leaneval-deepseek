import Mathlib

namespace Work.WilkiesH.Interp.V2master

/-- `(μ+1)! ≤ ((μ:ℝ)+2)^(μ+1)`. -/
lemma af_factorial (μ : ℕ) : (((μ+1).factorial : ℕ) : ℝ) ≤ ((μ:ℝ)+2)^(μ+1) := by
  have h1 : ((μ+1).factorial : ℕ) ≤ (μ+1)^(μ+1) := Nat.factorial_le_pow (μ+1)
  have h1R : (((μ+1).factorial : ℕ) : ℝ) ≤ (((μ+1 : ℕ) : ℝ))^(μ+1) := by
    exact_mod_cast h1
  have h2 : (((μ+1:ℕ):ℝ)) ≤ (μ:ℝ)+2 := by push_cast; linarith
  have h3 : (((μ+1:ℕ):ℝ))^(μ+1) ≤ ((μ:ℝ)+2)^(μ+1) :=
    pow_le_pow_left₀ (by positivity) h2 (μ+1)
  linarith [h1R, h3]

/-- The constant/numeric part: `14850225·(μ+1)!·h^6 ≤ (1/4)·h^(40(μ+1))` for `h = (μ:ℝ)+2`. -/
lemma af_const (μ : ℕ) :
    14850225 * (((μ+1).factorial : ℕ) : ℝ) * ((μ:ℝ)+2)^6
      ≤ (1/4) * ((μ:ℝ)+2)^(40*(μ+1)) := by
  set h : ℝ := (μ:ℝ)+2 with hh
  have hh2 : (2:ℝ) ≤ h := by rw [hh]; linarith
  have hf : (((μ+1).factorial : ℕ) : ℝ) ≤ h^(μ+1) := by
    rw [hh]; exact af_factorial μ
  have hpow : (2:ℝ)^33 ≤ h^(39*μ+33) := by
    have a : (2:ℝ)^33 ≤ (2:ℝ)^(39*μ+33) := pow_le_pow_right₀ (by norm_num) (by omega)
    have b : (2:ℝ)^(39*μ+33) ≤ h^(39*μ+33) := pow_le_pow_left₀ (by norm_num) hh2 _
    linarith
  have hnum : (14850225:ℝ) ≤ (1/4) * h^(39*μ+33) := by
    have hh4 : (1/4)*(2:ℝ)^33 ≤ (1/4) * h^(39*μ+33) := by nlinarith [hpow]
    norm_num at hh4
    linarith
  have hexp : (39*μ+33) + (μ+7) = 40*(μ+1) := by omega
  calc 14850225 * (((μ+1).factorial : ℕ) : ℝ) * h^6
      ≤ 14850225 * h^(μ+1) * h^6 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hf (by norm_num)
    _ = 14850225 * (h^(μ+1) * h^6) := by rw [mul_assoc]
    _ = 14850225 * h^(μ+7) := by rw [← pow_add, show (μ+1)+6 = μ+7 by omega]
    _ ≤ (1/4) * h^(39*μ+33) * h^(μ+7) := mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = (1/4) * h^(40*(μ+1)) := by rw [mul_assoc, ← pow_add, hexp]

/-- Polynomial bound for the bracket's leading factor. -/
lemma af_bracket_poly (m : ℝ) (hm : 0 ≤ m) :
    300*(10*(m+2)^2+100)*(m+3)*(m+1)^3 + (m+2) ≤ 66001*(m+2)^6 := by
  have h2 : (0:ℝ) ≤ m+2 := by linarith
  nlinarith [hm, pow_nonneg h2 1, pow_nonneg h2 2, pow_nonneg h2 3, pow_nonneg h2 4,
    pow_nonneg h2 5, pow_nonneg h2 6]

/-- Bound on the inner sum `S` by `300·((μ:ℝ)+1)^3·Q·Lg`. -/
lemma af_S1 (m Q Lg : ℝ) (hm : 0 ≤ m) (hQ : 1 ≤ Q) (hLg : 1 ≤ Lg) :
    17 + (m+1)^2 + Q + 80*(m+1)^2*m + 100*(m+1)^2*m*Q + 100*(m+1)^2*m*Lg
      ≤ 300 * (m+1)^3 * Q * Lg := by
  have hb1 : (1:ℝ) ≤ m+1 := by linarith
  have hb0 : (0:ℝ) ≤ m+1 := by linarith
  have hQ0 : (0:ℝ) ≤ Q := by linarith
  have hL0 : (0:ℝ) ≤ Lg := by linarith
  have hb3 : (1:ℝ) ≤ (m+1)^3 := one_le_pow₀ hb1
  have hb3Q : (1:ℝ) ≤ (m+1)^3 * Q := by nlinarith [hb3, hQ]
  have hb3L : (1:ℝ) ≤ (m+1)^3 * Lg := by nlinarith [hb3, hLg]
  have hbQL : (1:ℝ) ≤ (m+1) * Q * Lg :=
    le_trans (by nlinarith [hb1, hQ] : (1:ℝ) ≤ (m+1)*Q)
      (le_mul_of_one_le_right (mul_nonneg hb0 hQ0) hLg)
  have hP1 : (1:ℝ) ≤ (m+1)^3 * Q * Lg :=
    le_trans hb3Q (le_mul_of_one_le_right (mul_nonneg (pow_nonneg hb0 3) hQ0) hLg)
  have hfac2 : m ≤ (m+1) * Q * Lg :=
    le_trans (le_trans (by linarith : m ≤ m+1) (le_mul_of_one_le_right hb0 hQ))
      (le_mul_of_one_le_right (mul_nonneg hb0 hQ0) hLg)
  have hfac3 : m ≤ (m+1) * Lg := by nlinarith [hm, hb1, hLg]
  have hfac4 : m ≤ (m+1) * Q := by nlinarith [hm, hb1, hQ]
  have t1 : (17:ℝ) ≤ 17 * ((m+1)^3 * Q * Lg) := by nlinarith [hP1]
  have t2 : (m+1)^2 ≤ (m+1)^3 * Q * Lg := by
    have h := mul_le_mul_of_nonneg_left hbQL (by positivity : (0:ℝ) ≤ (m+1)^2)
    nlinarith [h]
  have t3 : Q ≤ (m+1)^3 * Q * Lg := by
    have h := mul_le_mul_of_nonneg_left hb3L hQ0
    nlinarith [h]
  have t4 : 80*(m+1)^2*m ≤ 80*((m+1)^3 * Q * Lg) := by
    have h := mul_le_mul_of_nonneg_left hfac2 (by positivity : (0:ℝ) ≤ (m+1)^2)
    nlinarith [h]
  have t5 : 100*(m+1)^2*m*Q ≤ 100*((m+1)^3 * Q * Lg) := by
    have h := mul_le_mul_of_nonneg_left hfac3 (by positivity : (0:ℝ) ≤ (m+1)^2 * Q)
    nlinarith [h]
  have t6 : 100*(m+1)^2*m*Lg ≤ 100*((m+1)^3 * Q * Lg) := by
    have h := mul_le_mul_of_nonneg_left hfac4 (by positivity : (0:ℝ) ≤ (m+1)^2 * Lg)
    nlinarith [h]
  linarith [t1, t2, t3, t4, t5, t6]

/-- Exponent upgrade for `Q`. -/
lemma af_Qpow (μ : ℕ) (Q : ℝ) (hQ : 1 ≤ Q) : Q^3 ≤ Q^(100*(μ+1)^2) := by
  apply pow_le_pow_right₀ hQ
  have : 1 ≤ (μ+1)^2 := Nat.one_le_pow _ _ (by omega)
  nlinarith

/-- Exponent upgrade for `Lg`. -/
lemma af_Lgpow (μ : ℕ) (Lg : ℝ) (hLg : 1 ≤ Lg) : Lg ≤ Lg^(100*(μ+1)^2) := by
  have h : Lg^1 ≤ Lg^(100*(μ+1)^2) := by
    apply pow_le_pow_right₀ hLg
    have : 1 ≤ (μ+1)^2 := Nat.one_le_pow _ _ (by omega)
    nlinarith
  simpa using h

lemma arith_final (μ : ℕ) (Q Lg : ℝ) (hQ : 1 ≤ Q) (hLg : 1 ≤ Lg) :
    25 * (((μ+1).factorial : ℕ) : ℝ) * (8*Q+1) *
      ((10*((μ:ℝ)+2)^2+100) * Q * ((μ:ℝ)+3) *
          (17 + ((μ:ℝ)+1)^2 + Q + 80*((μ:ℝ)+1)^2*(μ:ℝ)
             + 100*((μ:ℝ)+1)^2*(μ:ℝ)*Q + 100*((μ:ℝ)+1)^2*(μ:ℝ)*Lg)
        + ((μ:ℝ)+2) * Q^2 * Lg)
    ≤ (1/4) * (((μ:ℝ)+2)^(40*(μ+1)) * Q^(100*(μ+1)^2) * Lg^(100*(μ+1)^2)) := by
  have hm0 : (0:ℝ) ≤ (μ:ℝ) := Nat.cast_nonneg μ
  set S : ℝ := 17 + ((μ:ℝ)+1)^2 + Q + 80*((μ:ℝ)+1)^2*(μ:ℝ)
        + 100*((μ:ℝ)+1)^2*(μ:ℝ)*Q + 100*((μ:ℝ)+1)^2*(μ:ℝ)*Lg with hS
  set br : ℝ := (10*((μ:ℝ)+2)^2+100)*Q*((μ:ℝ)+3)*S + ((μ:ℝ)+2)*Q^2*Lg with hbr
  set f : ℝ := (((μ+1).factorial : ℕ) : ℝ) with hfdef
  have hS0 : (0:ℝ) ≤ S := by rw [hS]; positivity
  have hf0 : (0:ℝ) ≤ f := by rw [hfdef]; positivity
  have hSle : S ≤ 300*((μ:ℝ)+1)^3*Q*Lg := by
    rw [hS]; exact af_S1 (μ:ℝ) Q Lg hm0 hQ hLg
  have hbrle : br ≤ 66001*((μ:ℝ)+2)^6*Q^2*Lg := by
    rw [hbr]
    have ht1 : (10*((μ:ℝ)+2)^2+100)*Q*((μ:ℝ)+3)*S
        ≤ 300*(10*((μ:ℝ)+2)^2+100)*((μ:ℝ)+3)*((μ:ℝ)+1)^3*Q^2*Lg := by
      have h := mul_le_mul_of_nonneg_left hSle
        (by positivity : (0:ℝ) ≤ (10*((μ:ℝ)+2)^2+100)*Q*((μ:ℝ)+3))
      calc (10*((μ:ℝ)+2)^2+100)*Q*((μ:ℝ)+3)*S
          ≤ (10*((μ:ℝ)+2)^2+100)*Q*((μ:ℝ)+3)*(300*((μ:ℝ)+1)^3*Q*Lg) := h
        _ = 300*(10*((μ:ℝ)+2)^2+100)*((μ:ℝ)+3)*((μ:ℝ)+1)^3*Q^2*Lg := by ring
    calc (10*((μ:ℝ)+2)^2+100)*Q*((μ:ℝ)+3)*S + ((μ:ℝ)+2)*Q^2*Lg
        ≤ 300*(10*((μ:ℝ)+2)^2+100)*((μ:ℝ)+3)*((μ:ℝ)+1)^3*Q^2*Lg
            + ((μ:ℝ)+2)*Q^2*Lg := add_le_add ht1 (le_refl _)
      _ = (300*(10*((μ:ℝ)+2)^2+100)*((μ:ℝ)+3)*((μ:ℝ)+1)^3 + ((μ:ℝ)+2))*Q^2*Lg := by ring
      _ ≤ 66001*((μ:ℝ)+2)^6*Q^2*Lg := by
          apply mul_le_mul_of_nonneg_right _ (by positivity : (0:ℝ) ≤ Lg)
          apply mul_le_mul_of_nonneg_right (af_bracket_poly (μ:ℝ) hm0)
            (by positivity : (0:ℝ) ≤ Q^2)
  have hLHS : 25 * f * (8*Q+1) * br ≤ 14850225 * f * ((μ:ℝ)+2)^6 * Q^3 * Lg := by
    have h89 : 8*Q+1 ≤ 9*Q := by linarith
    have h25f : (0:ℝ) ≤ 25*f := by positivity
    have hbr0 : (0:ℝ) ≤ br := by rw [hbr]; positivity
    calc 25 * f * (8*Q+1) * br
        ≤ 25 * f * (9*Q) * br := by
            apply mul_le_mul_of_nonneg_right _ hbr0
            exact mul_le_mul_of_nonneg_left h89 h25f
      _ = 225 * f * Q * br := by ring
      _ ≤ 225 * f * Q * (66001*((μ:ℝ)+2)^6*Q^2*Lg) := by
            apply mul_le_mul_of_nonneg_left hbrle (by positivity : (0:ℝ) ≤ 225*f*Q)
      _ = 14850225 * f * ((μ:ℝ)+2)^6 * Q^3 * Lg := by ring
  have hconst : 14850225 * f * ((μ:ℝ)+2)^6 ≤ (1/4)*((μ:ℝ)+2)^(40*(μ+1)) := by
    rw [hfdef]; exact af_const μ
  calc 25 * f * (8*Q+1) * br
      ≤ 14850225 * f * ((μ:ℝ)+2)^6 * Q^3 * Lg := hLHS
    _ = (14850225 * f * ((μ:ℝ)+2)^6) * (Q^3*Lg) := by ring
    _ ≤ ((1/4)*((μ:ℝ)+2)^(40*(μ+1))) * (Q^3*Lg) :=
        mul_le_mul_of_nonneg_right hconst (by positivity : (0:ℝ) ≤ Q^3*Lg)
    _ = (1/4)*((μ:ℝ)+2)^(40*(μ+1)) * Q^3 * Lg := by ring
    _ ≤ (1/4)*((μ:ℝ)+2)^(40*(μ+1)) * Q^(100*(μ+1)^2) * Lg^(100*(μ+1)^2) := by
        have hA : (0:ℝ) ≤ (1/4)*((μ:ℝ)+2)^(40*(μ+1)) := by positivity
        calc (1/4)*((μ:ℝ)+2)^(40*(μ+1)) * Q^3 * Lg
            = ((1/4)*((μ:ℝ)+2)^(40*(μ+1))) * (Q^3*Lg) := by ring
          _ ≤ ((1/4)*((μ:ℝ)+2)^(40*(μ+1))) * (Q^(100*(μ+1)^2)*Lg^(100*(μ+1)^2)) := by
              apply mul_le_mul_of_nonneg_left _ hA
              exact mul_le_mul (af_Qpow μ Q hQ) (af_Lgpow μ Lg hLg)
                (by positivity) (by positivity)
          _ = (1/4)*((μ:ℝ)+2)^(40*(μ+1)) * Q^(100*(μ+1)^2) * Lg^(100*(μ+1)^2) := by ring
    _ = (1/4) * (((μ:ℝ)+2)^(40*(μ+1)) * Q^(100*(μ+1)^2) * Lg^(100*(μ+1)^2)) := by ring

end Work.WilkiesH.Interp.V2master
