import Mathlib
import Submission.Work.Implosion.Basic
import Submission.Work.Implosion.Ecalle

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Ecalle

theorem mobius_injective_of_ne (a x y : ℂ) (ha : a ≠ 0) (hx : x ≠ a) (hy : y ≠ a)
    (h : mobius a x = mobius a y) : x = y := by
  have hx' : x - a ≠ 0 := sub_ne_zero.mpr hx
  have hy' : y - a ≠ 0 := sub_ne_zero.mpr hy
  simp only [mobius_apply] at h
  have hkey : (x + a) * (y - a) = (y + a) * (x - a) := (div_eq_div_iff hx' hy').mp h
  have h2 : 2 * a * (y - x) = 0 := by linear_combination hkey
  have h2a : (2 * a : ℂ) ≠ 0 := mul_ne_zero two_ne_zero ha
  have h3 : y - x = 0 := (mul_eq_zero.mp h2).resolve_left h2a
  exact (sub_eq_zero.mp h3).symm

end Work.Implosion.Ecalle
