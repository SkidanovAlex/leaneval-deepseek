/-
# Continuity of the ceiling function `β`

The ceiling `β x = √(9/4 − ∑ᵢ off(xᵢ)²)` of the cusp chapter `Work.Cusp` is built from the
`1`-periodic triangle wave

`off t = 1/2 − |Int.fract t − 1/2|`

(the distance of `t` to the nearest half-integer), which is the value of the continuous tent
function `s ↦ 1/2 − |s − 1/2|` at the fractional part `Int.fract t`.  Since the tent function has
the same value at `0` and at `1`, Mathlib's `ContinuousOn.comp_fract''` (`Int.fract` is
`1`-periodic and the endpoints match) shows that `off` is continuous: the jumps of `Int.fract`
at the integers are exactly compensated by the vanishing of the tent function at the endpoints.
Finite sums, powers, subtraction and the square root are continuous, so `β` is continuous; this
is the standing regularity assumption for every chart of `ThetaOuter`/`ThetaPolar`/`ThetaCore`
and for the transition maps of the cusp piece.
-/
import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Cusp

/-- The triangle wave `off t = 1/2 − |Int.fract t − 1/2|` is continuous: it is the composition of
`Int.fract` with the tent function `s ↦ 1/2 − |s − 1/2|` on the unit interval, whose values at
`0` and `1` coincide. -/
@[fun_prop]
theorem off_continuous_aux : Continuous off := by
  change Continuous (fun t : ℝ => 1 / 2 - |Int.fract t - 1 / 2|)
  exact ContinuousOn.comp_fract'' (f := fun s : ℝ => 1 / 2 - |s - 1 / 2|)
    (by fun_prop) (by norm_num)

/-- **The ceiling function `β` is continuous.**  It is a finite sum of squares of the continuous
triangle wave `off` (which is continuous in spite of `Int.fract` not being so), inside a square
root. -/
theorem beta_continuous : Continuous beta := by
  unfold beta
  fun_prop

end Work.Cusp
