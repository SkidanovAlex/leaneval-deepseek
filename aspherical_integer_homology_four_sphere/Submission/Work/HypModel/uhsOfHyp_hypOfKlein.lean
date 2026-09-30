import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The upper half space coordinates of a Klein point

For a point `y` of the open unit ball (the Klein model), the upper half space position of its
Klein lift `hypOfKlein y = (y,1)/√(1−‖y‖²)` is

`(y₀/(1−y₃), y₁/(1−y₃), y₂/(1−y₃), √(1−‖y‖²)/(1−y₃))`.

Indeed `hypOfKlein y` has height coordinate `s = (√(1−‖y‖²))⁻¹` and horizontal coordinates `s • y`,
so `hypOfKlein y 4 - hypOfKlein y 3 = s·(1−y₃)`; dividing the horizontal coordinates by this height
difference cancels the two factors of `s` and gives `y_i/(1−y₃)`, while the height coordinate is
`(s·(1−y₃))⁻¹ = √(1−‖y‖²)/(1−y₃)`.
-/

noncomputable section

namespace Work.HypModel

theorem uhsOfHyp_hypOfKlein {y : E4} (hy : y ∈ ball) :
    uhsOfHyp (hypOfKlein y) =
      !₂[y 0 / (1 - y 3), y 1 / (1 - y 3), y 2 / (1 - y 3),
        Real.sqrt (1 - euclid y y) / (1 - y 3)] := by
  have hnorm_lt : ‖y‖ < 1 := hy
  -- `1 - ‖y‖ ^ 2` is positive, so the Klein lift factor `√(1 - ‖y‖ ^ 2)` is nonzero.
  have hpos : 0 < 1 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y, hnorm_lt]
  have hsqrt_ne : Real.sqrt (1 - ‖y‖ ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  -- All coordinates of `y` are `< 1`, in particular `1 - y 3 ≠ 0`.
  have hy3_lt : y 3 < 1 := by
    have hle : ‖y.ofLp 3‖ ≤ ‖y‖ := PiLp.norm_apply_le y 3
    rw [Real.norm_eq_abs] at hle
    have h : y.ofLp 3 ≤ |y.ofLp 3| := le_abs_self _
    linarith
  have h1y3 : 1 - y 3 ≠ 0 := by linarith
  ext i
  fin_cases i <;> simp <;> field_simp

end Work.HypModel
