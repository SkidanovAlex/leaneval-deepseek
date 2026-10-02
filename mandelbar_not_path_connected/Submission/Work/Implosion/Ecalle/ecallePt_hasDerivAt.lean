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

/-- The derivative of the Écalle point map `ζ(u) = a(s+1)/(s-1)`, `s = e^{2au}`:
`dζ/du = a² − ζ(u)²`.  Since `ds/du = 2a·s` and `ζ = a(s+1)/(s−1)`, one has
`dζ/du = −4a²s/(s−1)²`, which equals `a²(1 − (s+1)²/(s−1)²) = a² − ζ²`. -/
theorem ecallePt_hasDerivAt (a u : ℂ) (hs : ecalE a u ≠ 1) :
    HasDerivAt (ecalPt a) (a ^ 2 - ecalPt a u ^ 2) u := by
  have hd : ecalE a u - 1 ≠ 0 := sub_ne_zero.mpr hs
  -- derivative of the multiplier coordinate `u ↦ e^{2au}`
  have hE : HasDerivAt (fun u => ecalE a u) (2 * a * ecalE a u) u := by
    have h1 : HasDerivAt (fun u : ℂ => 2 * a * u) (2 * a) u := by
      simpa using (hasDerivAt_id u).const_mul (2 * a)
    have h2 : HasDerivAt (fun u => Complex.exp (2 * a * u))
        (Complex.exp (2 * a * u) * (2 * a)) u := h1.cexp
    convert h2 using 1
    · funext v; simp only [ecalE]
    · simp only [ecalE]; ring
  have hnum : HasDerivAt (fun u => a * (ecalE a u + 1)) (a * (2 * a * ecalE a u)) u :=
    (hE.add_const 1).const_mul a
  have hden : HasDerivAt (fun u => ecalE a u - 1) (2 * a * ecalE a u) u := hE.sub_const 1
  have hdiv := hnum.div hden hd
  convert hdiv using 1
  · funext v; simp only [Pi.div_apply]; rfl
  · simp only [ecalPt]
    field_simp
    ring

end Work.Implosion.Ecalle
