import Mathlib

namespace Work.Horn.FatouQ

/-- For `q ≥ 1`, `a, b > 0` and `s ≥ 0` with `s ^ q = b / a`, the negative power of `s`
rewrites as the corresponding ratio of the powers of `a` and `b`:
`s ^ (-m) = a ^ (m / q) * b ^ (-(m / q))`. -/
theorem rpow_neg_eq_mul_rpow_inv {q m : ℕ} {a b s : ℝ} (hq : 1 ≤ q) (ha : 0 < a) (hb : 0 < b)
    (hs : 0 ≤ s) (hp : s ^ q = b / a) :
    s ^ (-(m : ℝ)) = a ^ ((m : ℝ) / (q : ℝ)) * b ^ (-(m : ℝ) / (q : ℝ)) := by
  have hqne : q ≠ 0 := by omega
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  -- `s` is nonzero, since `s ^ q = b / a > 0` and `q ≥ 1`.
  have hspos : 0 < s := by
    rcases eq_or_lt_of_le hs with h | h
    · exfalso
      rw [← h, zero_pow hqne] at hp
      have hba : (0 : ℝ) < b / a := div_pos hb ha
      linarith
    · exact h
  -- `s ^ (-m) = s ^ (q * (-(m/q))) = (s ^ q) ^ (-(m/q)) = (b/a) ^ (-(m/q))`.
  have hqr : (q : ℝ) * (-(m : ℝ) / (q : ℝ)) = -(m : ℝ) := by
    field_simp
  calc s ^ (-(m : ℝ))
      = s ^ ((q : ℝ) * (-(m : ℝ) / (q : ℝ))) := by rw [hqr]
    _ = (s ^ (q : ℝ)) ^ (-(m : ℝ) / (q : ℝ)) := Real.rpow_mul hspos.le _ _
    _ = (s ^ q) ^ (-(m : ℝ) / (q : ℝ)) := by rw [Real.rpow_natCast]
    _ = (b / a) ^ (-(m : ℝ) / (q : ℝ)) := by rw [hp]
    _ = b ^ (-(m : ℝ) / (q : ℝ)) / a ^ (-(m : ℝ) / (q : ℝ)) := Real.div_rpow hb.le ha.le _
    _ = b ^ (-(m : ℝ) / (q : ℝ)) * a ^ ((m : ℝ) / (q : ℝ)) := by
          have hneg : -(-(m : ℝ) / (q : ℝ)) = (m : ℝ) / (q : ℝ) := by ring
          rw [div_eq_mul_inv, ← Real.rpow_neg ha.le, hneg]
    _ = a ^ ((m : ℝ) / (q : ℝ)) * b ^ (-(m : ℝ) / (q : ℝ)) := by ring

end Work.Horn.FatouQ
