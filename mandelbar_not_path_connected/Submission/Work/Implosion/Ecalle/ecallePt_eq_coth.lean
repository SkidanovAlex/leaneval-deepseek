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

/-- The Écalle point map is the complex hyperbolic cotangent:
`ζ(u) = a·(s+1)/(s−1) = a·coth(a u)` with `s = e^{2au}`.

This is the identity that identifies the algebraic inverse coordinate `ecalPt`
with the closed form `a·coth(a u)` used in Hubbard–Schleicher §4.  The hypothesis
`s ≠ 1` only removes the punctures `u ∈ (πi/a)ℤ`, where both sides have a pole. -/
theorem ecallePt_eq_coth (a u : ℂ) (hs : ecalE a u ≠ 1) :
    ecalPt a u = a * coth (a * u) := by
  -- Rewrite the exponent `2 * a * u` of `ecalE` as `2 * (a * u)`.
  have hE : ecalE a u = Complex.exp (2 * (a * u)) := by
    rw [ecalE]; congr 1; ring
  have hden : Complex.exp (2 * (a * u)) ≠ 1 := by rw [← hE]; exact hs
  set E := Complex.exp (a * u) with hEdef
  have hE0 : E ≠ 0 := Complex.exp_ne_zero _
  have hww : Complex.exp (2 * (a * u)) = E ^ 2 := by
    rw [hEdef, two_mul, Complex.exp_add]; ring
  have hneg : Complex.exp (-(a * u)) = E⁻¹ := by rw [hEdef, Complex.exp_neg]
  rw [ecalPt, hE, coth, Complex.cosh, Complex.sinh, hneg, hww]
  field_simp
  ring

end Work.Implosion.Ecalle
