import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Key calculus inequality: for `x ≥ 0` and `L ≥ 1`,
`log (1 + x) + (1 - L) ≤ x * exp (1 - L)`.
It is the tangent-line bound `log z ≤ z - 1` applied at `z = (1+x)·e^{1-L}`,
combined with `e^{1-L} ≤ 1`. -/
lemma log_one_add_add_sub_le {x L : ℝ} (hx : 0 ≤ x) (hL : 1 ≤ L) :
    Real.log (1 + x) + (1 - L) ≤ x * Real.exp (1 - L) := by
  have hy : (1 : ℝ) - L ≤ 0 := by linarith
  have h1x : 0 < 1 + x := by linarith
  have hpos : 0 < Real.exp (1 - L) := Real.exp_pos _
  have h := Real.log_le_sub_one_of_pos (mul_pos h1x hpos)
  rw [Real.log_mul (ne_of_gt h1x) (ne_of_gt hpos), Real.log_exp] at h
  have hexp : Real.exp (1 - L) ≤ 1 := Real.exp_le_one_iff.mpr hy
  calc Real.log (1 + x) + (1 - L) ≤ (1 + x) * Real.exp (1 - L) - 1 := h
    _ = x * Real.exp (1 - L) + (Real.exp (1 - L) - 1) := by ring
    _ ≤ x * Real.exp (1 - L) := by linarith

/-- `t ↦ t(1 + log(1+G/t)) - tL` is bounded by `G e^{1-L}` for `L ≥ 1`. -/
theorem mul_log_one_add_le {G L t : ℝ} (hG : 0 ≤ G) (hL : 1 ≤ L) (ht : 0 ≤ t) :
    t * (1 + Real.log (1 + G / t)) ≤ t * L + G * Real.exp (1 - L) := by
  rcases eq_or_lt_of_le ht with h | ht'
  · subst h
    simp
    exact mul_nonneg hG (Real.exp_pos _).le
  · have hx : 0 ≤ G / t := div_nonneg hG ht
    have hkey := log_one_add_add_sub_le hx hL
    have htpos : 0 < t := ht'
    have hmul : t * (Real.log (1 + G / t) + (1 - L)) ≤ t * (G / t * Real.exp (1 - L)) :=
      mul_le_mul_of_nonneg_left hkey ht
    have hcancel : t * (G / t) = G := mul_div_cancel₀ G (ne_of_gt htpos)
    have hmul' : t * (Real.log (1 + G / t) + (1 - L)) ≤ G * Real.exp (1 - L) := by
      calc t * (Real.log (1 + G / t) + (1 - L)) ≤ t * (G / t * Real.exp (1 - L)) := hmul
        _ = (t * (G / t)) * Real.exp (1 - L) := by ring
        _ = G * Real.exp (1 - L) := by rw [hcancel]
    nlinarith [hmul']

end Work.BW
