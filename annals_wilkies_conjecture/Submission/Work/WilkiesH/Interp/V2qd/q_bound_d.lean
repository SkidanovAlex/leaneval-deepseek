import Mathlib
import Submission.Work.WilkiesH.Interp.V2Params
import Submission.Work.WilkiesH.Interp.V2dV.dV_upper
import Submission.Work.WilkiesH.Interp.V2qb.q_bound_b_succ
import Submission.Work.WilkiesH.Interp.V2qd.const_le_CCc

set_option maxHeartbeats 1000000

namespace Work.WilkiesH.Interp.V2qd

open Work.WilkiesH.Interp

/-- `bV μ g H + 2 ≤ (EE μ + 2)·(1+g)^(AA μ)·Lg^(BB μ)`: the `+2` is absorbed by the
product of powers, which is `≥ 1`. -/
lemma bV_add_two_le' (μ g H : ℕ) :
    ((bV μ g H : ℕ) : ℝ) + 2 ≤
      ((EE μ : ℝ) + 2) * (1 + (g : ℝ)) ^ (AA μ) * ((lgNat H : ℕ) : ℝ) ^ (BB μ) := by
  have hb : ((bV μ g H : ℕ) : ℝ) =
      (EE μ : ℝ) * (1 + (g : ℝ)) ^ (AA μ) * ((lgNat H : ℕ) : ℝ) ^ (BB μ) := by
    simp only [bV, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    ring
  rw [hb]
  set P : ℝ := (1 + (g : ℝ)) ^ (AA μ) with hP
  set Q : ℝ := ((lgNat H : ℕ) : ℝ) ^ (BB μ) with hQ
  have hP1 : 1 ≤ P := by
    rw [hP]
    exact one_le_pow₀ (by have h : (0:ℝ) ≤ (g:ℝ) := Nat.cast_nonneg g; linarith)
  have hQ1 : 1 ≤ Q := by
    rw [hQ]
    exact one_le_pow₀ (by exact_mod_cast lgNat_pos H)
  have hPQ1 : 1 ≤ P * Q := by
    calc (1:ℝ) = 1 * 1 := by ring
      _ ≤ P * Q := mul_le_mul hP1 hQ1 (by norm_num) (by linarith)
  calc (EE μ : ℝ) * P * Q + 2 ≤ (EE μ : ℝ) * P * Q + 2 * (P * Q) := by linarith
    _ = ((EE μ : ℝ) + 2) * (P * Q) := by ring
    _ = ((EE μ : ℝ) + 2) * P * Q := by ring

/-- `AA μ + 1 ≤ Ec μ`, i.e. `100(μ+1)^3 + 1 ≤ 1000(μ+1)^4`. -/
lemma AA_add_one_le_Ec (μ : ℕ) : AA μ + 1 ≤ Ec μ := by
  rw [AA, Ec]
  have h3 : (μ+1)^3 ≤ (μ+1)^4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h1 : (1:ℕ) ≤ (μ+1)^3 := Nat.one_le_pow 3 (μ+1) (by omega)
  nlinarith [h3, h1]

-- `⌈1/ρ⌉^μ · d ≤ q`, where `⌈1/rhoV μ⌉ = KK μ = 2μ+4` and
-- `qPoly` evaluates to `CCc μ (1+D) (1+g)^(Ec μ) (1+log H)^(Fc μ)`.
-- From `dV_upper`, `d ≤ 8 ((μ+1)!(8g+9))^(1/(μ+1)) (bV+2)^(μ/(μ+1))`, and
-- `bV+2 ≤ (EE μ + 2) (g+1)^A Lg^B`; the exponents `Ec μ = Fc μ = 1000(μ+1)^4` dominate
-- `A·μ/(μ+1) + 1 = 100μ(μ+1)^2 + 1` and `B·μ/(μ+1)`, and
-- `CCc μ = (μ+2)^(100(μ+1)^2)` dominates `K^μ · 8 ((μ+1)!·17) · (EE μ + 2)^(μ/(μ+1))`.
theorem q_bound_d (μ D g H : ℕ) (hH : 1 ≤ H)
    (hd : ((Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H) : ℕ) : ℝ) ≤
      8 * ((((μ + 1).factorial : ℕ) : ℝ) * (8 * (g : ℝ) + 9)) ^ (1 / ((μ : ℝ) + 1)) *
        (((Work.WilkiesH.Interp.bV μ g H : ℕ) : ℝ) + 2) ^ ((μ : ℝ) / ((μ : ℝ) + 1))) :
    ((((Nat.ceil (1 / Work.WilkiesH.Interp.rhoV μ)) ^ μ) *
        Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H) : ℕ) : ℝ) ≤
      MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] (Work.WilkiesH.Interp.qPoly μ) := by
  -- `⌈1/ρ⌉ = KK μ`
  have hceil : Nat.ceil (1 / rhoV μ) = KK μ := by
    rw [show 1 / rhoV μ = (KK μ : ℝ) by rw [rhoV, one_div, inv_inv], Nat.ceil_natCast]
  rw [hceil, V2qb.qPol_eval μ D g H]
  rw [show (((KK μ) ^ μ * dV μ g (bV μ g H) : ℕ) : ℝ)
      = (KK μ : ℝ) ^ μ * ((dV μ g (bV μ g H) : ℕ) : ℝ) by push_cast; ring]
  -- abbreviations for the four quantities appearing in the bound
  set G : ℝ := 1 + (g : ℝ) with hG
  set Lg : ℝ := ((lgNat H : ℕ) : ℝ) with hLg
  set b2 : ℝ := ((bV μ g H : ℕ) : ℝ) + 2 with hb2
  set Dv : ℝ := ((dV μ g (bV μ g H) : ℕ) : ℝ) with hDv
  set A0 : ℝ := (((μ + 1).factorial : ℕ) : ℝ) * (8 * (g : ℝ) + 9) with hA0
  have hG1 : 1 ≤ G := by rw [hG]; have h : (0:ℝ) ≤ (g:ℝ) := Nat.cast_nonneg g; linarith
  have hG0 : 0 ≤ G := le_trans zero_le_one hG1
  have hLg0 : 0 ≤ Lg := by rw [hLg]; exact Nat.cast_nonneg _
  have hb20 : 0 ≤ b2 := by
    rw [hb2]; have h : (0:ℝ) ≤ ((bV μ g H : ℕ) : ℝ) := Nat.cast_nonneg _; linarith
  have hb21 : 1 ≤ b2 := by
    rw [hb2]; have h : (0:ℝ) ≤ ((bV μ g H : ℕ) : ℝ) := Nat.cast_nonneg _; linarith
  have hK0 : 0 ≤ (KK μ : ℝ) := Nat.cast_nonneg _
  have hA01 : 1 ≤ A0 := by
    rw [hA0]
    have h1 : (1:ℝ) ≤ (((μ+1).factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_pos (μ+1)
    have h2 : (1:ℝ) ≤ 8 * (g:ℝ) + 9 := by
      have h : (0:ℝ) ≤ (g:ℝ) := Nat.cast_nonneg g; linarith
    calc (1:ℝ) = 1 * 1 := by ring
      _ ≤ ((((μ+1).factorial : ℕ) : ℝ)) * (8 * (g:ℝ) + 9) :=
          mul_le_mul h1 h2 (by norm_num) (by linarith)
  have hA00 : 0 ≤ A0 := le_trans zero_le_one hA01
  -- `A₀ = (μ+1)!·(8g+9) ≤ (μ+2)^(μ+1)·9·G`
  have hA0le : A0 ≤ ((μ:ℝ)+2)^(μ+1) * (9 * G) := by
    rw [hA0, hG]
    have hf : ((((μ + 1).factorial : ℕ)) : ℝ) ≤ ((μ:ℝ)+2)^(μ+1) := by
      have h1 : (μ+1).factorial ≤ (μ+1)^(μ+1) := Nat.factorial_le_pow (μ+1)
      have h2 : ((((μ+1)^(μ+1) : ℕ)) : ℝ) ≤ ((μ:ℝ)+2)^(μ+1) := by
        rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
        exact pow_le_pow_left₀ (by linarith) (by linarith) (μ+1)
      calc (((μ+1).factorial : ℕ) : ℝ) ≤ (((μ+1)^(μ+1) : ℕ) : ℝ) := by exact_mod_cast h1
        _ ≤ ((μ:ℝ)+2)^(μ+1) := h2
    have hg9 : 8 * (g:ℝ) + 9 ≤ 9 * (1 + (g:ℝ)) := by
      have h : (0:ℝ) ≤ (g:ℝ) := Nat.cast_nonneg g; linarith
    exact mul_le_mul hf hg9 (by linarith) (by positivity)
  -- the constant comparison `72·K^μ·(μ+2)^(μ+1)·(EE μ+2) ≤ CCc μ`
  have hconst : 72 * (KK μ : ℝ) ^ μ * ((μ:ℝ)+2)^(μ+1) * ((EE μ : ℝ) + 2) ≤ (CCc μ : ℝ) := by
    exact_mod_cast const_le_CCc μ
  -- `A₀^(1/(μ+1)) ≤ A₀` and `b₂^(μ/(μ+1)) ≤ b₂`
  have ht1 : 1 / ((μ:ℝ)+1) ≤ 1 := by
    rw [one_div]
    exact inv_le_one_of_one_le₀ (by linarith)
  have hs1 : (μ:ℝ)/((μ:ℝ)+1) ≤ 1 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hA0t : A0 ^ (1 / ((μ:ℝ)+1)) ≤ A0 := Real.rpow_le_self_of_one_le hA01 ht1
  have hb2t : b2 ^ ((μ:ℝ)/((μ:ℝ)+1)) ≤ b2 := Real.rpow_le_self_of_one_le hb21 hs1
  have hpoly : Dv ≤ 8 * A0 * b2 := by
    have h3 : 8 * A0 ^ (1/((μ:ℝ)+1)) * b2 ^ ((μ:ℝ)/((μ:ℝ)+1)) ≤ 8 * A0 * b2 := by
      calc 8 * A0 ^ (1/((μ:ℝ)+1)) * b2 ^ ((μ:ℝ)/((μ:ℝ)+1))
          = 8 * (A0 ^ (1/((μ:ℝ)+1)) * b2 ^ ((μ:ℝ)/((μ:ℝ)+1))) := by ring
        _ ≤ 8 * (A0 * b2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hA0t hb2t (Real.rpow_nonneg hb20 _) hA00)
              (by norm_num)
        _ = 8 * A0 * b2 := by ring
    linarith [hd, h3]
  -- `b₂ = bV + 2 ≤ (EE μ + 2)·G^A·Lg^B`
  have hb2le : b2 ≤ ((EE μ : ℝ) + 2) * G ^ (AA μ) * Lg ^ (BB μ) := by
    rw [hb2, hG, hLg]
    exact bV_add_two_le' μ g H
  have hP0 : 0 ≤ ((μ:ℝ)+2)^(μ+1) := pow_nonneg (by linarith) _
  have h9G0 : 0 ≤ 9 * G := by linarith
  have hmain : (KK μ : ℝ) ^ μ * Dv ≤
      (CCc μ : ℝ) * (1 + (D : ℝ)) * G ^ (Ec μ) * (1 + Real.log H) ^ (Fc μ) := by
    calc (KK μ : ℝ) ^ μ * Dv
        ≤ (KK μ : ℝ) ^ μ * (8 * A0 * b2) := mul_le_mul_of_nonneg_left hpoly (pow_nonneg hK0 _)
      _ ≤ (KK μ : ℝ) ^ μ * (8 * (((μ:ℝ)+2)^(μ+1) * (9 * G))
            * (((EE μ : ℝ) + 2) * G ^ (AA μ) * Lg ^ (BB μ))) := by
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg hK0 _)
            have h4 : A0 * b2 ≤ (((μ:ℝ)+2)^(μ+1) * (9 * G))
                * (((EE μ : ℝ) + 2) * G ^ (AA μ) * Lg ^ (BB μ)) :=
              mul_le_mul hA0le hb2le hb20 (mul_nonneg hP0 h9G0)
            calc 8 * A0 * b2 = 8 * (A0 * b2) := by ring
              _ ≤ 8 * ((((μ:ℝ)+2)^(μ+1) * (9 * G))
                    * (((EE μ : ℝ) + 2) * G ^ (AA μ) * Lg ^ (BB μ))) :=
                  mul_le_mul_of_nonneg_left h4 (by norm_num)
              _ = 8 * (((μ:ℝ)+2)^(μ+1) * (9 * G))
                    * (((EE μ : ℝ) + 2) * G ^ (AA μ) * Lg ^ (BB μ)) := by ring
      _ = (72 * (KK μ : ℝ) ^ μ * ((μ:ℝ)+2)^(μ+1) * ((EE μ : ℝ) + 2))
            * (G ^ (AA μ + 1) * Lg ^ (BB μ)) := by
            have h1 : G ^ (AA μ + 1) = G ^ (AA μ) * G := pow_succ G (AA μ)
            rw [h1]; ring
      _ ≤ (CCc μ : ℝ) * (G ^ (AA μ + 1) * Lg ^ (BB μ)) := by
            exact mul_le_mul_of_nonneg_right hconst (mul_nonneg (pow_nonneg hG0 _) (pow_nonneg hLg0 _))
      _ = (CCc μ : ℝ) * G ^ (AA μ + 1) * Lg ^ (BB μ) := by ring
      _ ≤ (CCc μ : ℝ) * G ^ (Ec μ) * (1 + Real.log H) ^ (Fc μ) := by
            have hGp : G ^ (AA μ + 1) ≤ G ^ (Ec μ) := pow_le_pow_right₀ hG1 (AA_add_one_le_Ec μ)
            have hLp : Lg ^ (BB μ) ≤ (1 + Real.log H) ^ (Fc μ) := by
              rw [hLg]; exact V2qb.lgNat_pow_le μ H hH
            have hCC0 : 0 ≤ (CCc μ : ℝ) := Nat.cast_nonneg _
            calc (CCc μ : ℝ) * G ^ (AA μ + 1) * Lg ^ (BB μ)
                = (CCc μ : ℝ) * (G ^ (AA μ + 1) * Lg ^ (BB μ)) := by ring
              _ ≤ (CCc μ : ℝ) * (G ^ (Ec μ) * (1 + Real.log H) ^ (Fc μ)) :=
                  mul_le_mul_of_nonneg_left
                    (mul_le_mul hGp hLp (pow_nonneg hLg0 _) (pow_nonneg hG0 _)) hCC0
              _ = (CCc μ : ℝ) * G ^ (Ec μ) * (1 + Real.log H) ^ (Fc μ) := by ring
      _ ≤ (CCc μ : ℝ) * (1 + (D : ℝ)) * G ^ (Ec μ) * (1 + Real.log H) ^ (Fc μ) := by
            have hD1 : 1 ≤ 1 + (D:ℝ) := by
              have h : (0:ℝ) ≤ (D:ℝ) := Nat.cast_nonneg D; linarith
            have hnn : 0 ≤ (CCc μ : ℝ) * G ^ (Ec μ) * (1 + Real.log H) ^ (Fc μ) :=
              mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hG0 _))
                (pow_nonneg (by have h := log_nat_nonneg H; linarith) _)
            calc (CCc μ : ℝ) * G ^ (Ec μ) * (1 + Real.log H) ^ (Fc μ)
                = (CCc μ : ℝ) * G ^ (Ec μ) * (1 + Real.log H) ^ (Fc μ) * 1 := by ring
              _ ≤ (CCc μ : ℝ) * G ^ (Ec μ) * (1 + Real.log H) ^ (Fc μ) * (1 + (D:ℝ)) :=
                  mul_le_mul_of_nonneg_left hD1 hnn
              _ = (CCc μ : ℝ) * (1 + (D : ℝ)) * G ^ (Ec μ) * (1 + Real.log H) ^ (Fc μ) := by ring
  exact hmain

end Work.WilkiesH.Interp.V2qd
