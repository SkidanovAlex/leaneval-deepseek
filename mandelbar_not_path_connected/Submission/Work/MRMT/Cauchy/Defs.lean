/-
Work.MRMT — the Cauchy transform and the truncated Beurling singular integral.

These are the two analytic objects used by the Ahlfors–Bers construction: the solution of
`∂̄f = ω` is `f = C ω`, and `∂(C ω) = S ω` is the Beurling transform (the singular integral
with kernel `-1/(π z²)`, identified on `L²` with the Fourier multiplier `beurlingSymbol`).
-/
import Submission.Work.MRMT.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal

namespace Work.MRMT

/-- The Cauchy kernel constant `-(1/π)`. -/
def cauchyConst : ℂ := -((Real.pi : ℂ))⁻¹

/-- The Beurling kernel constant `-(1/π)` (same constant, kept separate for readability). -/
def beurlingConst : ℂ := -((Real.pi : ℂ))⁻¹

theorem cauchyConst_eq_beurlingConst : cauchyConst = beurlingConst := rfl

/-- The **Cauchy transform** `C ω (z) = -(1/π) ∫ ω(ζ)/(ζ - z) dζdη`.  For `ω` with compact
support (or `ω ∈ L^p` with `p < 2`) the integral converges absolutely; the definition is
total, with the junk value `0` when the integral does not converge. -/
def cauchyTransform (ω : ℂ → ℂ) (z : ℂ) : ℂ := cauchyConst * ∫ ζ, ω ζ / (ζ - z)

/-- The **truncated Beurling singular integral**
`S_ε ω (z) = -(1/π) ∫_{|ζ - z| > ε} ω(ζ)/(ζ - z)² dζdη`. -/
def beurlingTrunc (ε : ℝ) (ω : ℂ → ℂ) (z : ℂ) : ℂ :=
  beurlingConst * ∫ ζ in {ζ : ℂ | ε < ‖ζ - z‖}, ω ζ / (ζ - z) ^ 2

end Work.MRMT
