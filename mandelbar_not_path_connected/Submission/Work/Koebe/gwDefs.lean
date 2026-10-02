import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Vocabulary for the Grönwall area theorem

If `F (z) = 1/z + H z` is injective on the punctured unit disc with `H` holomorphic on the disc,
then `‖deriv H 0‖ ≤ 1` (Grönwall's area theorem, first coefficient).

This module fixes the notation used by the proof:

* `gco H n`      : the `n`-th Taylor coefficient `H⁽ⁿ⁾(0)/n!` of `H`;
* `sArea F r`    : the (signed) area `(2i)⁻¹ ∮_{|z|=r} conj (F z) · F'(z) dz`;
* `winding F r w`: the winding number `(2πi)⁻¹ ∮_{|z|=r} F'(z)/(F z - w) dz`.
-/

namespace Work.Koebe

open Complex Metric Set MeasureTheory

noncomputable section

/-- `n`-th Taylor coefficient of `H` at `0`. -/
def gco (H : ℂ → ℂ) (n : ℕ) : ℂ := ((n.factorial : ℂ))⁻¹ * iteratedDeriv n H 0

/-- The signed area enclosed by the curve `θ ↦ F (r e^{iθ})`. -/
def sArea (F : ℂ → ℂ) (r : ℝ) : ℂ :=
  (2 * Complex.I)⁻¹ * ∮ z in C(0, r), (starRingEnd ℂ (F z)) * deriv F z

/-- The winding number of the curve `θ ↦ F (r e^{iθ})` around `w`. -/
def winding (F : ℂ → ℂ) (r : ℝ) (w : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ * ∮ z in C(0, r), (deriv F z) / (F z - w)

end

end Work.Koebe
