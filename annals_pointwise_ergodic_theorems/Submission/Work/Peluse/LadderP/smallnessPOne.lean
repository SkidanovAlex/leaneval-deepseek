import Mathlib

namespace Work.Peluse.LadderP

set_option linter.unusedVariables false

/-- Elementary smallness bookkeeping for the ladder step `P1`.

Chaining the two "size" hypotheses `A * γ' ≤ γ ^ K` and
`2 ^ (E+1) / c₀ ^ (E+1) ≤ A` with the window lower bound
`c₀ * γ ^ (K₁ * E) ≤ xk`, the exponent comparison `K₁ * E * ek ≤ K` and
`ek ≤ E` yields `2 * γ' ≤ c₀ * xk ^ ek`.

The proof is pure real arithmetic: `γ ≤ 1` gives `γ ^ K ≤ γ ^ (K₁ * E * ek)`,
`c₀ ≤ 1` gives `c₀ ^ (E+1) ≤ c₀ ^ (ek+1)`, and the constants are arranged so
that the powers of `2`, `c₀` and `γ` telescope. -/
theorem smallnessPOne {γ γ' A c₀ xk : ℝ} {K K₁ E ek : ℕ}
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hγ'0 : 0 < γ') (hA0 : 0 < A)
    (hγ' : A * γ' ≤ γ ^ K)
    (hc₀0 : 0 < c₀) (hc₀1 : c₀ ≤ 1)
    (hAkey : (2:ℝ) ^ (E + 1) / c₀ ^ (E + 1) ≤ A)
    (hK : K₁ * E * ek ≤ K) (hekE : ek ≤ E)
    (hxlb : c₀ * γ ^ (K₁ * E) ≤ xk) :
    2 * γ' ≤ c₀ * xk ^ ek := by
  have hAkey' : (2:ℝ)^(E+1) ≤ c₀^(E+1) * A := by
    rw [mul_comm (c₀^(E+1)) A]
    exact (div_le_iff₀ (pow_pos hc₀0 (E+1))).mp hAkey
  -- `2 * γ' ≤ γ ^ K * (2 / A)`
  have hstep1 : 2 * γ' ≤ γ ^ K * (2 / A) := by
    have hle : γ' ≤ γ ^ K / A := by
      rw [le_div_iff₀ hA0]; linarith [hγ']
    calc 2 * γ' ≤ 2 * (γ ^ K / A) := mul_le_mul_of_nonneg_left hle (by norm_num)
      _ = γ ^ K * (2 / A) := by ring
  -- `2 / A ≤ c₀ ^ (E+1) / 2 ^ E`
  have hstep2 : 2 / A ≤ c₀ ^ (E + 1) / 2 ^ E := by
    rw [div_le_iff₀ hA0, div_mul_eq_mul_div,
      le_div_iff₀ (pow_pos (by norm_num : (0:ℝ) < 2) E)]
    calc (2:ℝ) * 2 ^ E = 2 ^ (E+1) := by rw [pow_succ]; ring
      _ ≤ c₀^(E+1) * A := hAkey'
  have hstep3 : γ ^ K * (2 / A) ≤ γ ^ K * (c₀ ^ (E+1) / 2 ^ E) :=
    mul_le_mul_of_nonneg_left hstep2 (pow_nonneg hγ0.le K)
  -- `c₀ ^ ek * γ ^ (K₁ * E * ek) ≤ xk ^ ek`
  have hstep4 : c₀ ^ ek * γ ^ (K₁ * E * ek) ≤ xk ^ ek := by
    have hbase : 0 ≤ c₀ * γ ^ (K₁ * E) := mul_nonneg hc₀0.le (pow_nonneg hγ0.le _)
    have h := pow_le_pow_left₀ hbase hxlb ek
    rwa [mul_pow, ← pow_mul] at h
  have hcoef : c₀ ^ (E+1) ≤ c₀ ^ (ek+1) :=
    pow_le_pow_of_le_one hc₀0.le hc₀1 (by omega)
  have hgam : γ ^ K ≤ γ ^ (K₁*E*ek) := pow_le_pow_of_le_one hγ0.le hγ1 hK
  have hdiv1 : γ ^ K / 2 ^ E ≤ γ ^ (K₁*E*ek) := by
    have h2E : (1:ℝ) ≤ 2 ^ E := one_le_pow₀ (by norm_num)
    calc γ ^ K / 2 ^ E ≤ γ ^ K := div_le_self (pow_nonneg hγ0.le K) h2E
      _ ≤ γ ^ (K₁*E*ek) := hgam
  -- `γ ^ K * (c₀ ^ (E+1) / 2 ^ E) ≤ c₀ ^ (ek+1) * γ ^ (K₁ * E * ek)`
  have hstep5 : γ^K * (c₀^(E+1)/2^E) ≤ c₀^(ek+1) * γ^(K₁*E*ek) := by
    have e1 : γ^K * (c₀^(E+1)/2^E) = c₀^(E+1) * (γ^K/2^E) := by ring
    rw [e1]
    have hnonneg : 0 ≤ γ^K/2^E := div_nonneg (pow_nonneg hγ0.le K) (by positivity)
    calc c₀^(E+1) * (γ^K/2^E) ≤ c₀^(ek+1) * (γ^K/2^E) :=
          mul_le_mul_of_nonneg_right hcoef hnonneg
      _ ≤ c₀^(ek+1) * γ^(K₁*E*ek) := mul_le_mul_of_nonneg_left hdiv1 (pow_nonneg hc₀0.le _)
  have hstep6 : c₀^(ek+1) * γ^(K₁*E*ek) = c₀ * (c₀^ek * γ^(K₁*E*ek)) := by
    rw [pow_succ]; ring
  have hfin : c₀ * (c₀^ek * γ^(K₁*E*ek)) ≤ c₀ * xk^ek :=
    mul_le_mul_of_nonneg_left hstep4 hc₀0.le
  calc 2*γ' ≤ γ^K * (2/A) := hstep1
    _ ≤ γ^K * (c₀^(E+1)/2^E) := hstep3
    _ ≤ c₀^(ek+1) * γ^(K₁*E*ek) := hstep5
    _ = c₀ * (c₀^ek * γ^(K₁*E*ek)) := hstep6
    _ ≤ c₀ * xk^ek := hfin

end Work.Peluse.LadderP
