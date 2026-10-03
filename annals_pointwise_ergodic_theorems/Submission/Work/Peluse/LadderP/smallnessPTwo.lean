import Mathlib

namespace Work.Peluse.LadderP

theorem smallnessPTwo {γ γ' A c₀ xk L : ℝ} {K K₁ E ek : ℕ}
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hγ'0 : 0 < γ') (hγ'1 : γ' ≤ 1)
    (hxk0 : 0 < xk) (hxlb : c₀ * γ ^ (K₁ * E) ≤ xk)
    (hc₀0 : 0 < c₀) (hc₀1 : c₀ ≤ 1)
    (hA : 1 ≤ A * (c₀ / 2) ^ (E + 1))
    (hK1 : K₁ * E * ek ≤ K) (hK2 : ek + 1 ≤ K) (hekE : ek ≤ E)
    (hL : A * γ' / 2 ≤ L * (γ * γ') ^ K) :
    1 ≤ c₀ * (xk * γ' / 2) ^ ek * L := by
  -- `0 < c₀/2 ≤ 1`, and `A > 0`, `A ≥ (2/c₀)^(E+1)` (used via `A·(c₀/2)^(E+1) ≥ 1`)
  have hc2pos : (0:ℝ) < c₀ / 2 := by positivity
  have hc2le1 : c₀ / 2 ≤ 1 := by linarith
  have hApos : 0 < A :=
    pos_of_mul_pos_left (lt_of_lt_of_le zero_lt_one hA) (pow_nonneg hc2pos.le _)
  -- `1 ≤ A · (c₀/2)^(ek+1)`, from `hA` and `ek + 1 ≤ E + 1`
  have hA1 : 1 ≤ A * (c₀/2)^(ek+1) := by
    have hp : (c₀/2)^(E+1) ≤ (c₀/2)^(ek+1) :=
      pow_le_pow_of_le_one hc2pos.le hc2le1 (Nat.succ_le_succ hekE)
    exact le_trans hA (mul_le_mul_of_nonneg_left hp hApos.le)
  -- `γ^K ≤ γ^(K₁·E·ek)` and `γ'^K ≤ γ'^(ek+1)`, hence `(γγ')^K ≤ γ^(K₁·E·ek)·γ'^(ek+1)`
  have hγK : γ^K ≤ γ^(K₁*E*ek) := pow_le_pow_of_le_one hγ0.le hγ1 hK1
  have hγ'K : γ'^K ≤ γ'^(ek+1) := pow_le_pow_of_le_one hγ'0.le hγ'1 hK2
  have hggK : (γ*γ')^K ≤ γ^(K₁*E*ek) * γ'^(ek+1) := by
    rw [mul_pow]
    exact mul_le_mul hγK hγ'K (pow_nonneg hγ'0.le _) (pow_nonneg hγ0.le _)
  -- `xk ≥ c₀·γ^(K₁·E)`, so `(xk·γ'/2)^ek ≥ (c₀·γ^(K₁·E)·γ'/2)^ek`
  have hbase : c₀ * γ^(K₁*E) * γ' / 2 ≤ xk * γ' / 2 := by
    have h := mul_le_mul_of_nonneg_right hxlb (by positivity : (0:ℝ) ≤ γ'/2)
    simpa only [mul_div_assoc] using h
  have hpow : (c₀ * γ^(K₁*E) * γ' / 2)^ek ≤ (xk * γ' / 2)^ek :=
    pow_le_pow_left₀ (by positivity) hbase ek
  have hmono1 : c₀ * (c₀ * γ^(K₁*E) * γ' / 2)^ek * (A*γ'/2)
      ≤ c₀ * (xk*γ'/2)^ek * (A*γ'/2) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hc₀0.le) (by positivity)
  have hmono2 : c₀ * (xk*γ'/2)^ek * (A*γ'/2)
      ≤ c₀ * (xk*γ'/2)^ek * (L*(γ*γ')^K) :=
    mul_le_mul_of_nonneg_left hL (by positivity)
  -- the exact algebraic normal form of the middle term
  have hid : c₀ * (c₀ * γ^(K₁*E) * γ' / 2)^ek * (A*γ'/2)
      = A*(c₀/2)^(ek+1)*γ^(K₁*E*ek)*γ'^(ek+1) := by
    ring_nf
  have hmid : γ^(K₁*E*ek) * γ'^(ek+1)
      ≤ A*(c₀/2)^(ek+1) * γ^(K₁*E*ek) * γ'^(ek+1) := by
    have h : γ^(K₁*E*ek) * γ'^(ek+1)
        ≤ (A*(c₀/2)^(ek+1)) * (γ^(K₁*E*ek) * γ'^(ek+1)) :=
      le_mul_of_one_le_left (by positivity) hA1
    simpa only [mul_assoc] using h
  -- the whole chain, with the extra factor `(γγ')^K` kept on both sides
  have hchain : (γ*γ')^K ≤ c₀ * (xk*γ'/2)^ek * (L*(γ*γ')^K) := by
    calc (γ*γ')^K ≤ γ^(K₁*E*ek)*γ'^(ek+1) := hggK
      _ ≤ A*(c₀/2)^(ek+1)*γ^(K₁*E*ek)*γ'^(ek+1) := hmid
      _ = c₀ * (c₀ * γ^(K₁*E) * γ' / 2)^ek * (A*γ'/2) := hid.symm
      _ ≤ c₀ * (xk*γ'/2)^ek * (A*γ'/2) := hmono1
      _ ≤ c₀ * (xk*γ'/2)^ek * (L*(γ*γ')^K) := hmono2
  have hgg_pos : 0 < (γ*γ')^K := pow_pos (mul_pos hγ0 hγ'0) K
  have hfin : (γ*γ')^K ≤ (c₀ * (xk*γ'/2)^ek * L) * (γ*γ')^K := by
    simpa only [mul_assoc] using hchain
  exact (mul_le_mul_iff_of_pos_right hgg_pos).mp (by simpa using hfin)

end Work.Peluse.LadderP
