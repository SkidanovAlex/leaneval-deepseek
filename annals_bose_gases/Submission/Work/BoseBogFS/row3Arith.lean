import Mathlib.Analysis.Real.Pi.Bounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

/-- Pure arithmetic row: with `T = 10 ^ 6 * (1 + L) / eps`, `L ≥ 0`, `eps > 0`, the
prefactor `4 * π * (8 * π) ^ 3 / (2 * T) = 1024 * π ^ 4 / T` is at most `eps`.

The numerical content is the crude bound `π < 4`, which gives `1024 * π ^ 4 < 262144 < 10 ^ 6`,
while `eps * T = 10 ^ 6 * (1 + L) ≥ 10 ^ 6`. -/
theorem row3Arith {T L eps : ℝ} (hT0 : 0 < T) (heps0 : 0 < eps) (hL0 : 0 ≤ L) (hTdef : T = 10 ^ 6 * (1 + L) / eps) : 4 * Real.pi * (8 * Real.pi) ^ 3 / (2 * T) ≤ eps := by
  -- `π ^ 4 ≤ 4 ^ 4 = 256`.
  have hpi4 : Real.pi ^ 4 ≤ 256 := by
    have h := pow_le_pow_left₀ Real.pi_nonneg Real.pi_lt_four.le 4
    norm_num at h ⊢
    exact h
  -- `eps * T = 10 ^ 6 * (1 + L)`.
  have hprod : eps / 10 ^ 6 * T = 1 + L := by
    rw [hTdef]
    field_simp
  -- hence `1 / T ≤ eps / 10 ^ 6`.
  have hinvT : 1 / T ≤ eps / 10 ^ 6 := by
    rw [div_le_iff₀ hT0]
    rw [hprod]
    linarith
  -- and the numerical coefficient `1024 * π ^ 4 / 10 ^ 6` is at most `1`.
  have hcoef : 1024 * Real.pi ^ 4 / 10 ^ 6 ≤ 1 := by
    rw [div_le_one (by norm_num : (0:ℝ) < 10 ^ 6)]
    have h2 : (1024:ℝ) * Real.pi ^ 4 ≤ 1024 * 256 :=
      mul_le_mul_of_nonneg_left hpi4 (by norm_num)
    linarith [h2]
  calc 4 * Real.pi * (8 * Real.pi) ^ 3 / (2 * T)
      = 1024 * Real.pi ^ 4 * (1 / T) := by field_simp; ring
    _ ≤ 1024 * Real.pi ^ 4 * (eps / 10 ^ 6) :=
        mul_le_mul_of_nonneg_left hinvT (by positivity)
    _ = (1024 * Real.pi ^ 4 / 10 ^ 6) * eps := by ring
    _ ≤ 1 * eps := mul_le_mul_of_nonneg_right hcoef heps0.le
    _ = eps := one_mul _

end Work.BoseBogFS
