import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Vocabulary for Grönwall's area theorem

For `F z = 1/z + H z` on the punctured unit disc we define

* `wind F r z = (2πi)⁻¹ ∮_{|w|=r} (F w - z)⁻¹ F'(w) dw` — the (negative of the)
  winding number of the curve `F(|w|=r)` around `z`;
* `signedArea F r = (2i)⁻¹ ∮_{|w|=r} conj(F w) F'(w) dw` — the signed area enclosed
  by the curve.

The area theorem is the pair of facts `wind F r z ∈ {-1,0}` (argument principle,
injectivity gives at most one preimage) and `signedArea F r = ∫∫ wind` (Fubini +
`∫∫_{|z|<M} (u-z)⁻¹ dA = π conj u`), together with the explicit value
`signedArea F r = π (∑_n n ‖a_n‖² r^{2n} - r⁻²)`.
-/

namespace Work.Area

open Complex Metric MeasureTheory

/-- Signature-agnostic helper: `(2πi)⁻¹` as a complex number. -/
noncomputable def twoPiIinv : ℂ := (2 * (Real.pi : ℂ) * I)⁻¹

/-- The winding-number integral of the curve `F(|w|=r)` around `z`. -/
noncomputable def wind (F : ℂ → ℂ) (r : ℝ) (z : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ * circleIntegral (fun w => (F w - z)⁻¹ * deriv F w) 0 r

/-- The signed-area integral of the curve `F(|w|=r)`. -/
noncomputable def signedArea (F : ℂ → ℂ) (r : ℝ) : ℂ :=
  (2 * I)⁻¹ * circleIntegral (fun w => (starRingEnd ℂ (F w)) * deriv F w) 0 r

end Work.Area
