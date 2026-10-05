import Mathlib

/-!
# Two arcs of the circle meet only in their endpoints

Let `0 < t1 < 2π`.  The two maps

* `s ↦ Circle.exp (t0 + t1 * (s + 1) / 2)`, `s ∈ [-1, 1]`,  and
* `s' ↦ Circle.exp (t0 + t1 + (2π - t1) * (1 - s') / 2)`, `s' ∈ [-1, 1]`,

parametrise the closed arc from `Circle.exp t0` to `Circle.exp (t0 + t1)` (turning in the
positive direction) and the complementary closed arc from `Circle.exp (t0 + t1)` back to
`Circle.exp t0`.  Together they cover the whole circle, and since both arcs have length
strictly between `0` and `2π` they meet exactly in the two endpoints `Circle.exp t0` and
`Circle.exp (t0 + t1)`.

Consequently, if a point of the first arc equals a point of the second arc, then that common
point is one of the two endpoints.

Formally, writing `u = t1 * (s + 1) / 2 ∈ [0, t1]` and `v = (2π - t1) * (1 - s') / 2 ∈
[0, 2π - t1]`, the hypothesis `Circle.exp (t0 + u) = Circle.exp (t0 + t1 + v)` gives, through
`Circle.exp_eq_exp`, an integer `m` with `u - t1 - v = 2π * m`.  The bounds on `u` and `v` force
`-2π ≤ 2π * m ≤ 0`, hence `m ∈ {-1, 0}`.  If `m = 0` then `u = t1` (so the common point is
`Circle.exp (t0 + t1)`), and if `m = -1` then `u = 0` (so the common point is `Circle.exp t0`).
-/

namespace Work.RPB1a.Caratheodory.Brouwer

theorem exp_arc_inter (t0 t1 s s' : ℝ) (hpos : 0 < t1) (hlt : t1 < 2 * Real.pi)
    (hs : s ∈ Set.Icc (-1 : ℝ) 1) (hs' : s' ∈ Set.Icc (-1 : ℝ) 1)
    (heq : Circle.exp (t0 + t1 * (s + 1) / 2)
      = Circle.exp (t0 + t1 + (2 * Real.pi - t1) * (1 - s') / 2)) :
    Circle.exp (t0 + t1 * (s + 1) / 2) = Circle.exp t0 ∨
      Circle.exp (t0 + t1 * (s + 1) / 2) = Circle.exp (t0 + t1) := by
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp heq
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨hs'1, hs'2⟩ := hs'
  -- The difference of the two parameters is `2π * m`.
  have hd : t1 * (s + 1) / 2 - t1 - (2 * Real.pi - t1) * (1 - s') / 2
      = (m : ℝ) * (2 * Real.pi) := by linarith [hm]
  -- The two arcs are parametrised by `[0, t1]` and `[0, 2π - t1]`.
  have hu0 : 0 ≤ t1 * (s + 1) / 2 := by
    have h1 : 0 ≤ t1 * (s + 1) := mul_nonneg (le_of_lt hpos) (by linarith)
    linarith
  have hu1 : t1 * (s + 1) / 2 ≤ t1 := by
    have h1 : s + 1 ≤ 2 := by linarith
    have h2 : t1 * (s + 1) ≤ t1 * 2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hpos)
    linarith
  have hpi2 : 0 < 2 * Real.pi := by positivity
  have hv0 : 0 ≤ (2 * Real.pi - t1) * (1 - s') / 2 := by
    have h1 : 0 ≤ 2 * Real.pi - t1 := by linarith
    have h2 : 0 ≤ 1 - s' := by linarith
    have h3 : 0 ≤ (2 * Real.pi - t1) * (1 - s') := mul_nonneg h1 h2
    linarith
  have hv1 : (2 * Real.pi - t1) * (1 - s') / 2 ≤ 2 * Real.pi - t1 := by
    have h1 : 1 - s' ≤ 2 := by linarith
    have h2 : 0 ≤ 2 * Real.pi - t1 := by linarith
    have h3 : (2 * Real.pi - t1) * (1 - s') ≤ (2 * Real.pi - t1) * 2 :=
      mul_le_mul_of_nonneg_left h1 h2
    linarith
  -- Squeeze the integer `m`.
  have hle : (m : ℝ) * (2 * Real.pi) ≤ 0 := by linarith [hd, hu1, hv0]
  have hge : -2 * Real.pi ≤ (m : ℝ) * (2 * Real.pi) := by linarith [hd, hu0, hv1]
  have hm_le : (m : ℝ) ≤ 0 := by
    by_contra h
    have h' : 0 < (m : ℝ) := not_le.mp h
    have := mul_pos h' hpi2
    linarith
  have hm_ge : (-1 : ℝ) ≤ (m : ℝ) := by
    by_contra h
    have h' : (m : ℝ) < -1 := not_le.mp h
    have := mul_lt_mul_of_pos_right h' hpi2
    linarith
  have hm_le' : m ≤ 0 := by exact_mod_cast hm_le
  have hm_ge' : (-1 : ℤ) ≤ m := by exact_mod_cast hm_ge
  have hm_cases : m = -1 ∨ m = 0 := by omega
  rcases hm_cases with hm0 | hm0
  · -- `m = -1`: the common point is `Circle.exp t0`.
    left
    rw [hm0] at hd
    push_cast at hd
    have hu_eq : t1 * (s + 1) / 2 = 0 := by linarith [hd, hu0, hv1]
    have htheta : t0 + t1 * (s + 1) / 2 = t0 := by linarith
    rw [htheta]
  · -- `m = 0`: the common point is `Circle.exp (t0 + t1)`.
    right
    rw [hm0] at hd
    push_cast at hd
    have hu_eq : t1 * (s + 1) / 2 = t1 := by linarith [hd, hu1, hv0]
    have htheta : t0 + t1 * (s + 1) / 2 = t0 + t1 := by linarith
    rw [htheta]

end Work.RPB1a.Caratheodory.Brouwer
