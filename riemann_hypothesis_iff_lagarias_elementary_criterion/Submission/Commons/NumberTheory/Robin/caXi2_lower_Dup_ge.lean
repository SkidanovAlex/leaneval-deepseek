import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Commons.NumberTheory.Robin

/-- Lower bound for the expression `(L+2β)/2 - Σ_{k=1}^6 (β/L)^k/k` on the
rectangle `L ≥ 7.333`, `β ∈ [34657359/10^8, 3465736/10^7]`. -/
theorem caXi2_lower_Dup_ge (L β : ℝ) (hL : 7.333 ≤ L)
    (hβlo : 34657359 / 10 ^ 8 ≤ β) (hβhi : β ≤ 3465736 / 10 ^ 7) :
    19823 / 5000 ≤ (L + 2 * β) / 2
      - (β / L + (β / L) ^ 2 / 2 + (β / L) ^ 3 / 3 + (β / L) ^ 4 / 4
          + (β / L) ^ 5 / 5 + (β / L) ^ 6 / 6) := by
  have hLpos : 0 < L := by linarith
  have hβpos : 0 < β := by
    have : (0:ℝ) < 34657359 / 10 ^ 8 := by norm_num
    linarith
  -- write `t = β/L`, the ratio that appears in the tail
  set t := β / L with htdef
  have ht0 : 0 ≤ t := by rw [htdef]; exact div_nonneg hβpos.le hLpos.le
  have htle : t ≤ 4727 / 100000 := by
    rw [htdef, div_le_iff₀ hLpos]
    nlinarith [hβhi, hL]
  -- each power is bounded by the corresponding power of the rational bound
  have hp2 : t ^ 2 ≤ (4727 / 100000 : ℝ) ^ 2 := pow_le_pow_left₀ ht0 htle 2
  have hp3 : t ^ 3 ≤ (4727 / 100000 : ℝ) ^ 3 := pow_le_pow_left₀ ht0 htle 3
  have hp4 : t ^ 4 ≤ (4727 / 100000 : ℝ) ^ 4 := pow_le_pow_left₀ ht0 htle 4
  have hp5 : t ^ 5 ≤ (4727 / 100000 : ℝ) ^ 5 := pow_le_pow_left₀ ht0 htle 5
  have hp6 : t ^ 6 ≤ (4727 / 100000 : ℝ) ^ 6 := pow_le_pow_left₀ ht0 htle 6
  -- bound the truncated exponential-type tail by an explicit rational
  have hT : t + t ^ 2 / 2 + t ^ 3 / 3 + t ^ 4 / 4 + t ^ 5 / 5 + t ^ 6 / 6
      ≤ 48424 / 1000000 := by
    nlinarith [htle, hp2, hp3, hp4, hp5, hp6]
  have hL2 : (7333 : ℝ) / 2000 ≤ L / 2 := by linarith
  have hEq : (L + 2 * β) / 2 = L / 2 + β := by ring
  linarith [hL2, hβlo, hT, hEq]

end Commons.NumberTheory.Robin