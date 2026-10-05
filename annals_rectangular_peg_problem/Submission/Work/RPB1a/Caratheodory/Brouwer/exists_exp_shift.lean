import Mathlib

namespace Work.RPB1a.Caratheodory.Brouwer

/-- Given two distinct points `a`, `b` on the unit circle, there is a base angle `t0`
parametrising `a` and an increment `t1 ∈ (0, 2π)` so that `t0 + t1` parametrises `b`.
Equivalently: the parametrisation `Circle.exp` of the circle by `ℝ` can be shifted from
any prescribed starting point `a` to any other point `b` by a positive rotation of less
than a full turn. -/
theorem exists_exp_shift (a b : Circle) (hab : a ≠ b) :
    ∃ t0 t1 : ℝ, Circle.exp t0 = a ∧ Circle.exp (t0 + t1) = b ∧ 0 < t1 ∧ t1 < 2 * Real.pi := by
  -- Start at the argument of `a`; the remaining rotation is the argument of `a⁻¹ * b`.
  set t0 : ℝ := Complex.arg (a : ℂ) with ht0
  set c : Circle := a⁻¹ * b with hc
  -- `c ≠ 1` exactly because `a ≠ b`.
  have hc1 : c ≠ 1 := by
    rw [hc]
    intro h
    exact hab (inv_mul_eq_one.mp h)
  set s : ℝ := Complex.arg (c : ℂ) with hs
  have hexps : Circle.exp s = c := by rw [hs]; exact Circle.exp_arg c
  have hspi : s ≤ Real.pi := by rw [hs]; exact Complex.arg_le_pi _
  have hsgt : -Real.pi < s := by rw [hs]; exact Complex.neg_pi_lt_arg _
  -- `s = 0` would force `c = 1`, hence `a = b`.
  have hsne : s ≠ 0 := fun h => hc1 (by rw [← hexps, h, Circle.exp_zero])
  have ht0a : Circle.exp t0 = a := by rw [ht0]; exact Circle.exp_arg a
  -- Once `Circle.exp t1 = c`, the shift lands on `b`.
  have hbase : ∀ t1 : ℝ, Circle.exp t1 = c → Circle.exp (t0 + t1) = b := by
    intro t1 ht1
    rw [Circle.exp_add, ht1, ht0, Circle.exp_arg, hc]
    exact mul_inv_cancel_left a b
  rcases lt_or_ge 0 s with hpos | hnonpos
  · -- `s ∈ (0, π]`, so it is already a valid increment.
    exact ⟨t0, s, ht0a, hbase s hexps, hpos, by linarith [Real.pi_pos]⟩
  · -- `s ∈ (-π, 0)`, so rotate by `s + 2π ∈ (π, 2π)` instead.
    have hneg : s < 0 := lt_of_le_of_ne hnonpos hsne
    have hexp2 : Circle.exp (s + 2 * Real.pi) = c := by
      rw [Circle.exp_add, hexps, Circle.exp_two_pi, mul_one]
    exact ⟨t0, s + 2 * Real.pi, ht0a, hbase _ hexp2, by linarith [Real.pi_pos, hsgt],
      by linarith⟩

end Work.RPB1a.Caratheodory.Brouwer
