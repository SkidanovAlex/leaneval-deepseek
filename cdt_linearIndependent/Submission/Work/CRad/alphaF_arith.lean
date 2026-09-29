import Mathlib

namespace Work.CRad

/-- Elementary arithmetic core of the "alphaF" gap bound: if `m ≠ n` and the
relative gap `10 ^ 6 * |m - n| ≤ n` holds, then `m` and `n` are within a
factor `1001/1000` of each other in the sense that both
`4000 * n + 999 ≤ 4004 * m` and `4000 * m + 999 ≤ 4004 * n`. -/
theorem alphaF_arith (m n : ℕ) (hmn : m ≠ n)
    (hgap : 10 ^ 6 * (((m : ℤ) - (n : ℤ)).natAbs) ≤ n) :
    (4000 : ℝ) * (n : ℝ) + 999 ≤ 4004 * (m : ℝ) ∧
      (4000 : ℝ) * (m : ℝ) + 999 ≤ 4004 * (n : ℝ) := by
  have hgapZ : (10 ^ 6 : ℤ) * (((m : ℤ) - (n : ℤ)).natAbs : ℤ) ≤ (n : ℤ) := by
    exact_mod_cast hgap
  have hzne : ((m : ℤ) - (n : ℤ)) ≠ 0 := by
    simp only [sub_ne_zero]
    exact_mod_cast hmn
  have hd_pos : 1 ≤ (((m : ℤ) - (n : ℤ)).natAbs) := by
    have := Int.natAbs_pos.mpr hzne
    omega
  have hn : 10 ^ 6 ≤ n := by omega
  have hnR : (10 ^ 6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hA : (10 ^ 6 : ℝ) * ((m : ℝ) - (n : ℝ)) ≤ (n : ℝ) := by
    have h1 : (10 ^ 6 : ℤ) * ((m : ℤ) - (n : ℤ)) ≤
        (10 ^ 6 : ℤ) * (((m : ℤ) - (n : ℤ)).natAbs : ℤ) :=
      mul_le_mul_of_nonneg_left (Int.le_natAbs) (by norm_num)
    have h2 : (10 ^ 6 : ℤ) * ((m : ℤ) - (n : ℤ)) ≤ (n : ℤ) := le_trans h1 hgapZ
    exact_mod_cast h2
  have hB : (10 ^ 6 : ℝ) * ((n : ℝ) - (m : ℝ)) ≤ (n : ℝ) := by
    have hneg : ((n : ℤ) - (m : ℤ)) ≤ (((m : ℤ) - (n : ℤ)).natAbs : ℤ) := by
      have := Int.le_natAbs (a := -((m : ℤ) - (n : ℤ)))
      rw [Int.natAbs_neg] at this
      simpa using this
    have h1 : (10 ^ 6 : ℤ) * ((n : ℤ) - (m : ℤ)) ≤
        (10 ^ 6 : ℤ) * (((m : ℤ) - (n : ℤ)).natAbs : ℤ) :=
      mul_le_mul_of_nonneg_left hneg (by norm_num)
    have h2 : (10 ^ 6 : ℤ) * ((n : ℤ) - (m : ℤ)) ≤ (n : ℤ) := le_trans h1 hgapZ
    exact_mod_cast h2
  constructor <;> linarith

end Work.CRad
