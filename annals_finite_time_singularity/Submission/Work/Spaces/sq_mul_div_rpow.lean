import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces

/-- The key identity `(s^(e/2))^2 = s^e` for `0 < s`. -/
private lemma rpow_half_sq (s e : ℝ) (hs : 0 < s) :
    (s ^ (e / 2)) ^ 2 = s ^ e := by
  rw [sq, ← Real.rpow_add hs]
  congr 1
  ring

theorem sq_mul_div_rpow (A W s e : ℝ) (hs : 0 ≤ s) (he : e ≠ 0) :
    (A * (W / s ^ (e / 2))) ^ 2 = A ^ 2 * W ^ 2 * s ^ (-e) := by
  rcases hs.lt_or_eq with h | h
  · -- `0 < s`: reduce to `(s^(e/2))^2 = s^e` and clear inverses.
    rw [Real.rpow_neg hs e, ← rpow_half_sq s e h, ← inv_pow, div_eq_mul_inv]
    ring
  · -- `s = 0`: both sides vanish, since `e ≠ 0` forces `e/2 ≠ 0` and `-e ≠ 0`.
    subst h
    have he2 : e / 2 ≠ 0 := div_ne_zero he two_ne_zero
    have hne : -e ≠ 0 := neg_ne_zero.mpr he
    rw [Real.zero_rpow he2, div_zero, mul_zero, Real.zero_rpow hne]
    ring

end Work.Spaces
