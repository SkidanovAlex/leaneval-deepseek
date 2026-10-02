import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-!
# Jordan's inequality on the symmetric fold of `(0, π)`

For `x ∈ (0, π)` one has `sin x = sin (min x (π - x))`, and the argument of the
sine on the right lies in `[0, π/2]`, where Jordan's inequality
`Real.mul_le_sin` gives `(2/π) · min x (π - x) ≤ sin (min x (π - x))`.
-/
set_option linter.unusedVariables false in
theorem jordan_sin_min (lam t : ℝ) (hlam : 0 < lam) (h1 : 0 < lam*t) (h2 : lam*t < Real.pi) :
    (2 / Real.pi) * min (lam * t) (Real.pi - lam * t) ≤ Real.sin (lam * t) := by
  set x := lam * t with hx
  have hx0 : 0 < x := h1
  have hxpi : x < Real.pi := h2
  -- The minimum is nonnegative, ...
  have hmpos : 0 ≤ min x (Real.pi - x) := le_min (le_of_lt hx0) (by linarith)
  -- ... and at most `π/2`.
  have hmle : min x (Real.pi - x) ≤ Real.pi / 2 := by
    rcases le_total x (Real.pi - x) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  -- Reflecting at `π/2` leaves the sine unchanged: `sin x = sin (min x (π - x))`.
  have hsin_eq : Real.sin x = Real.sin (min x (Real.pi - x)) := by
    rcases le_total x (Real.pi - x) with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, Real.sin_pi_sub]
  rw [hsin_eq]
  exact Real.mul_le_sin hmpos hmle

end Work.PARIMPL2.Direct
