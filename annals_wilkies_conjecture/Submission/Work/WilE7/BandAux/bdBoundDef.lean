/-
  `Work.WilE7.bdBound`: the explicit degree bound for the two-strata band.

  The degree of the semi-Pfaffian presentation `bandS3two Z S₁ S₂` of the band between two
  sheets of two strata is bounded by `bdBound F * (1 + D) ^ 8`, where `F` bounds the formats
  of `Z`, `S₁.X`, `S₂.X` and `D` bounds their degrees.  The chain of bounds is

    deg(bandW1)  ≤ 2 (1+F) (1 + (deg Z + deg S.X))²                      (`fiberProdZ_deg`)
    deg(bandW2)  ≤ 2 (1+2F) (1 + (deg bandW1 + deg bandW1'))²            (`fiberProdZ_deg`)
    deg(padded)  ≤ 2 (1 + deg bandW2)²                                   (`prodDeg`)
    deg(bandS3)  ≤ deg(padded) + max 1 deg(padded) · 4                   (`addConds_deg_le`)

  With `T = 1 + D` and `deg Z, deg S₁.X, deg S₂.X ≤ D`, each step is bounded by a multiple of
  `T²`, `T⁴`, `T⁸`, `T⁸` respectively; keeping the constants explicit gives
  `bdBound F = 10 (1 + 2 (1+2F) (1 + 36 (1+F))²)² + 4`.
-/
import Mathlib

set_option autoImplicit false

namespace Work.WilE7

/-- The explicit polynomial degree bound (coefficient of `(1 + D)^8`) for the two-strata band. -/
def bdBound (F : ℕ) : ℕ :=
  10 * (1 + 2 * (1 + 2 * F) * (1 + 36 * (1 + F)) ^ 2) ^ 2 + 4

end Work.WilE7
