/-
Lattice/size inequalities used in the proof of the main theorem.

This file proves `Work.N8.lattice_inequalities` together with two helper
inequalities it is built from:

* `lattice_lhs_bound` bounds the "frequency side" expression
  `2 δ⁻¹ / L + |T| / (2 π x)` by `δ⁻¹ (2 + (10/π) (X^(1/δ))^k)`.
* `lattice_qq_split` splits the largeness hypothesis on `QQ` into the two
  bounds `... ≤ QQ / (k! · Lc^k)` and `... ≤ QQ / Lc`.
-/
import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

/-- Bound on the "frequency side" sum `2 δ⁻¹ / L + |T| / (2 π x)`.

Using `|T| ≤ 2 δ⁻¹ (X/L)^(k+1)` and `x ≥ X/10`, `L ≥ 1`, `X ≥ 1`, `δ ≤ 1`,
this is at most `δ⁻¹ (2 + (10/π) (X^(1/δ))^k)`. -/
theorem lattice_lhs_bound {k : ℕ} {δ X L x T : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hL : 1 ≤ L) (hx : X / 10 ≤ x) (hX : 1 ≤ X)
    (hT : |T| ≤ 2 * δ⁻¹ * (X / L) ^ (k + 1)) :
    2 * δ⁻¹ / L + |T| / (2 * Real.pi * x) ≤
      δ⁻¹ * (2 + (10 / Real.pi) * (X ^ (1 / δ)) ^ k) := by
  have hδinv : 0 < δ⁻¹ := inv_pos.mpr hδ
  have hxpos : 0 < x := by linarith
  have hXpos : 0 < X := by linarith
  have hLpos : 0 < L := by linarith
  -- `X ≤ X^(1/δ)` because `1 ≤ 1/δ`.
  have hXA : X ≤ X ^ (1/δ) := by
    have h : (1:ℝ) ≤ 1/δ := by rw [one_le_div hδ]; exact hδ1
    calc X = X ^ (1:ℝ) := (Real.rpow_one X).symm
      _ ≤ X ^ (1/δ) := Real.rpow_le_rpow_of_exponent_le hX h
  have hXk_le : X^k ≤ (X ^ (1/δ))^k := pow_le_pow_left₀ hXpos.le hXA k
  -- First summand.
  have hterm1 : 2 * δ⁻¹ / L ≤ 2 * δ⁻¹ := by
    rw [div_le_iff₀ hLpos]; nlinarith [hL, hδinv]
  have hNnn : 0 ≤ 2 * δ⁻¹ * (X / L) ^ (k+1) :=
    mul_nonneg (by positivity) (pow_nonneg (div_nonneg hXpos.le hLpos.le) _)
  have hB1 : |T| / (2 * Real.pi * x) ≤ 2 * δ⁻¹ * (X / L) ^ (k + 1) / (2 * Real.pi * x) :=
    div_le_div_of_nonneg_right hT (by positivity)
  have hratio2 : (X/L)^(k+1)/X ≤ (X ^ (1/δ))^k := by
    rw [div_le_iff₀ hXpos]
    have h1 : (X/L)^(k+1) ≤ X^(k+1) := by
      apply pow_le_pow_left₀ (div_nonneg hXpos.le hLpos.le)
      rw [div_le_iff₀ hLpos]; nlinarith [hL, hXpos]
    calc (X/L)^(k+1) ≤ X^(k+1) := h1
      _ = X^k * X := by rw [pow_succ]
      _ ≤ (X^(1/δ))^k * X := mul_le_mul_of_nonneg_right hXk_le hXpos.le
  -- Second summand, converted into `(10/π) δ⁻¹ (X^(1/δ))^k`.
  have hB2 : 2 * δ⁻¹ * (X / L) ^ (k + 1) / (2 * Real.pi * x) ≤
      10 * δ⁻¹ * (X ^ (1/δ)) ^ k / Real.pi := by
    have hcX : (0:ℝ) < 2 * Real.pi * X / 10 := by positivity
    have hle : 2 * Real.pi * X / 10 ≤ 2 * Real.pi * x := by nlinarith [Real.pi_pos]
    have hs := div_le_div_of_nonneg_left hNnn hcX hle
    have heq : 2 * δ⁻¹ * (X/L)^(k+1) / (2*Real.pi*X/10)
        = (10*δ⁻¹/Real.pi) * ((X/L)^(k+1)/X) := by
      field_simp
    have heq2 : 10 * δ⁻¹ * (X^(1/δ))^k / Real.pi = (10*δ⁻¹/Real.pi) * (X^(1/δ))^k := by ring
    rw [heq] at hs
    rw [heq2]
    exact le_trans hs (mul_le_mul_of_nonneg_left hratio2 (by positivity))
  have hgoal_eq : δ⁻¹ * (2 + (10 / Real.pi) * (X ^ (1 / δ)) ^ k)
      = 2 * δ⁻¹ + δ⁻¹ * (10/Real.pi) * (X^(1/δ))^k := by ring
  have hbid : 10 * δ⁻¹ * (X^(1/δ))^k / Real.pi = δ⁻¹ * (10/Real.pi) * (X^(1/δ))^k := by ring
  rw [hgoal_eq]
  linarith [hterm1, hB1, hB2, hbid]

/-- Splits the largeness hypothesis `hbig` on `QQ` into the two estimates
`2(k+1) δ⁻¹ ((X^(1/δ))^(k+1)+1) ≤ QQ/(k! · Lc^k)` and
`2(k+1) δ⁻¹ ((X^(1/δ))^(k+1)+1) ≤ QQ/Lc`. -/
theorem lattice_qq_split {k : ℕ} (hk : 1 ≤ k) {δ X Lc QQ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hX : 1 ≤ X) (hQQ : 0 < QQ) (hLc : 0 < Lc)
    (hbig : (k.factorial : ℝ) * (X ^ (1 / δ)) ^ (2 * k) *
        (2 * ((k : ℝ) + 1) * δ⁻¹ * ((X ^ (1 / δ)) ^ (k + 1) + 1)) ≤ QQ)
    (hlcm : Lc ≤ (X ^ (1 / δ)) ^ 2) :
    2 * ((k : ℝ) + 1) * δ⁻¹ * ((X ^ (1 / δ)) ^ (k + 1) + 1)
        ≤ QQ / ((k.factorial : ℝ) * Lc ^ k) ∧
    2 * ((k : ℝ) + 1) * δ⁻¹ * ((X ^ (1 / δ)) ^ (k + 1) + 1) ≤ QQ / Lc := by
  set A : ℝ := X ^ (1/δ) with hA
  set M : ℝ := 2 * ((k:ℝ)+1) * δ⁻¹ * (A^(k+1)+1) with hM
  have hA1 : 1 ≤ A := by rw [hA]; exact Real.one_le_rpow hX (by positivity)
  have hKpos : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hK1 : (1:ℝ) ≤ (k.factorial : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos k))
  have hMnn : 0 ≤ M := by rw [hM]; positivity
  have hLck_le : Lc^k ≤ A^(2*k) := by
    calc Lc^k ≤ (A^2)^k := pow_le_pow_left₀ hLc.le hlcm k
      _ = A^(2*k) := by rw [pow_mul]
  have hA2_le : A^2 ≤ A^(2*k) := pow_le_pow_right₀ hA1 (by omega)
  have hLc_le : Lc ≤ A^(2*k) := le_trans hlcm hA2_le
  constructor
  · rw [le_div_iff₀ (by positivity : (0:ℝ) < (k.factorial : ℝ) * Lc^k)]
    calc M * ((k.factorial : ℝ) * Lc^k) ≤ M * ((k.factorial : ℝ) * A^(2*k)) := by
          apply mul_le_mul_of_nonneg_left _ hMnn
          exact mul_le_mul_of_nonneg_left hLck_le hKpos.le
      _ = (k.factorial : ℝ) * A^(2*k) * M := by ring
      _ ≤ QQ := hbig
  · rw [le_div_iff₀ hLc]
    calc M * Lc ≤ M * A^(2*k) := mul_le_mul_of_nonneg_left hLc_le hMnn
      _ = A^(2*k) * M := by ring
      _ ≤ (k.factorial : ℝ) * A^(2*k) * M := by
          have hh := mul_le_mul_of_nonneg_right hK1 (by positivity : (0:ℝ) ≤ A^(2*k) * M)
          linarith [hh]
      _ ≤ QQ := hbig

theorem lattice_inequalities {k : ℕ} (hk : 1 ≤ k) {δ X L Lc QQ x T : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hX : 1 ≤ X) (hL : 1 ≤ L) (hx : X / 10 ≤ x)
    (hQQ : 0 < QQ) (hLc : 0 < Lc)
    (hbig : (k.factorial : ℝ) * (X ^ (1 / δ)) ^ (2 * k) *
        (2 * ((k : ℝ) + 1) * δ⁻¹ * ((X ^ (1 / δ)) ^ (k + 1) + 1)) ≤ QQ)
    (hlcm : Lc ≤ (X ^ (1 / δ)) ^ 2)
    (hT : |T| ≤ 2 * δ⁻¹ * (X / L) ^ (k + 1)) :
    2 * δ⁻¹ / L + |T| / (2 * Real.pi * x) < QQ / ((k.factorial : ℝ) * Lc ^ k) ∧
    0 < QQ / ((k.factorial : ℝ) * Lc ^ k) ∧
    (2 * δ⁻¹ / L + |T| / (2 * Real.pi * x)) * (Lc / QQ) < 1 ∧
    (k : ℝ) + 1 ≤ L / (Lc / QQ) := by
  have hLHS_le := lattice_lhs_bound hδ hδ1 hL hx hX hT
  have hQQsplit := lattice_qq_split hk hδ hδ1 hX hQQ hLc hbig hlcm
  set A : ℝ := X ^ (1/δ) with hA
  set M : ℝ := 2*((k:ℝ)+1)*δ⁻¹*(A^(k+1)+1) with hM
  have hA1 : 1 ≤ A := by rw [hA]; exact Real.one_le_rpow hX (by positivity)
  have hδinv : 0 < δ⁻¹ := inv_pos.mpr hδ
  have hk1 : (2:ℝ) ≤ (k:ℝ)+1 := by
    have : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    linarith
  have hpi4 : (10:ℝ)/Real.pi < 4 := by
    rw [div_lt_iff₀ Real.pi_pos]; nlinarith [Real.pi_gt_three]
  have hAkn : 0 ≤ A^k := by positivity
  have hAk1_ge : A^k ≤ A^(k+1) := pow_le_pow_right₀ hA1 (Nat.le_succ k)
  -- The numeric core: `δ⁻¹ (2 + (10/π) A^k) < M`.
  have hnum : δ⁻¹*(2 + (10/Real.pi)*A^k) < M := by
    have hca : (10/Real.pi)*A^k ≤ 4*A^k := mul_le_mul_of_nonneg_right (le_of_lt hpi4) hAkn
    have h2 : 2 + (10/Real.pi)*A^k < 4*A^k + 4 := by linarith
    have h1 : 4*A^k + 4 ≤ 4*A^(k+1) + 4 := by linarith
    have h3 : 4*A^(k+1) + 4 ≤ 2*((k:ℝ)+1)*(A^(k+1)+1) := by
      have h : (4:ℝ) ≤ 2*((k:ℝ)+1) := by linarith
      have hAn : 0 ≤ A^(k+1)+1 := by positivity
      calc 4*A^(k+1) + 4 = 4*(A^(k+1)+1) := by ring
        _ ≤ (2*((k:ℝ)+1))*(A^(k+1)+1) := mul_le_mul_of_nonneg_right h hAn
        _ = 2*((k:ℝ)+1)*(A^(k+1)+1) := by ring
    have hcore : 2 + (10/Real.pi)*A^k < 2*((k:ℝ)+1)*(A^(k+1)+1) :=
      lt_of_lt_of_le h2 (le_trans h1 h3)
    have h := mul_lt_mul_of_pos_left hcore hδinv
    have heq : δ⁻¹*(2*((k:ℝ)+1)*(A^(k+1)+1)) = M := by rw [hM]; ring
    rwa [heq] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (lt_of_le_of_lt hLHS_le hnum) hQQsplit.1
  · exact div_pos hQQ (mul_pos (by exact_mod_cast Nat.factorial_pos k) (pow_pos hLc k))
  · have hLHS_lt2 : 2*δ⁻¹/L + |T|/(2*Real.pi*x) < QQ/Lc :=
      lt_of_lt_of_le (lt_of_le_of_lt hLHS_le hnum) hQQsplit.2
    have hp : 0 < Lc/QQ := div_pos hLc hQQ
    have h := mul_lt_mul_of_pos_right hLHS_lt2 hp
    have heq : (QQ/Lc)*(Lc/QQ) = 1 := by field_simp
    rwa [heq] at h
  · have hMge : 4*((k:ℝ)+1) ≤ M := by
      have hδinv1 : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr hδ1
      have hAbig : (2:ℝ) ≤ A^(k+1) + 1 := by
        have : (1:ℝ) ≤ A^(k+1) := one_le_pow₀ hA1
        linarith
      have hprod : (2:ℝ) ≤ δ⁻¹*(A^(k+1)+1) := by
        calc (2:ℝ) = 1*2 := by ring
          _ ≤ δ⁻¹*(A^(k+1)+1) := mul_le_mul hδinv1 hAbig (by norm_num) (by positivity)
      have h2k : (0:ℝ) ≤ 2*((k:ℝ)+1) := by positivity
      have h := mul_le_mul_of_nonneg_left hprod h2k
      rw [hM]
      calc 4*((k:ℝ)+1) = 2*((k:ℝ)+1)*2 := by ring
        _ ≤ 2*((k:ℝ)+1)*(δ⁻¹*(A^(k+1)+1)) := h
        _ = 2*((k:ℝ)+1)*δ⁻¹*(A^(k+1)+1) := by ring
    have hQQLc : (k:ℝ)+1 ≤ QQ/Lc := by
      have hknn : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
      linarith [hMge, hQQsplit.2, hknn]
    have hLQQ : QQ/Lc ≤ L*QQ/Lc := by
      have h1 : (1:ℝ)*(QQ/Lc) ≤ L*(QQ/Lc) := mul_le_mul_of_nonneg_right hL (by positivity)
      have h2 : (1:ℝ)*(QQ/Lc) = QQ/Lc := by ring
      have h3 : L*(QQ/Lc) = L*QQ/Lc := by ring
      linarith [h1, h2, h3]
    rw [div_div_eq_mul_div]
    exact le_trans hQQLc hLQQ

end Work.N8
