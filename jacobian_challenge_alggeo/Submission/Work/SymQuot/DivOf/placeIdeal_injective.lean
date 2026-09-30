/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The place ideal determines the place

For a curve `C` over a field `F` and an affine open `V ⊆ C`, the assignment
`z ↦ placeIdeal C V z hz` from places `z` of `C` lying in `V` to ideals of `Γ(C,V)`
is injective.  Indeed `placeIdeal C V z hz` is the prime ideal
`(hV.primeIdealOf ⟨z.point, hz⟩).asIdeal` (`placeIdeal_eq_primeIdealOf`), and the map
`x ↦ hV.primeIdealOf x` is injective because it is the homeomorphism `V ≃ Spec Γ(C,V)`
underlying `hV.isoSpec`, with inverse `hV.fromSpec` (`IsAffineOpen.fromSpec_primeIdealOf`).

This is what makes the extraction of the divisor of a point of `Symⁿ C` from an ideal
well defined: distinct points of `V` give distinct maximal ideals of `Γ(C,V)`.
-/
import Mathlib
import Submission.Work.SymQuot.DivOf.AffineCurve
import Submission.Work.SymQuot.DivOf.placeIdeal_isMaximal

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SymQuot.DivOf

open AlgebraicGeometry

universe u

/-- **The place ideal determines the place**: the map sending a place `z ∈ V` to the ideal
`placeIdeal C V z hz` is injective. -/
theorem placeIdeal_injective {F : Type u} [Field F] {C : Work.CurveBasics.Curve F}
    {V : C.left.Opens} (hV : AlgebraicGeometry.IsAffineOpen V)
    {z w : Work.CurveBasics.Curve.Place C} (hz : z.point ∈ V) (hw : w.point ∈ V)
    (h : Work.SymQuot.DivOf.placeIdeal C V z hz = Work.SymQuot.DivOf.placeIdeal C V w hw) :
    z = w := by
  -- `placeIdeal` is the prime ideal of the point; we give the (harmless) `Nonempty` instance
  -- required by `placeIdeal_eq_primeIdealOf` explicitly, since the point `z` provides it.
  rw [@placeIdeal_eq_primeIdealOf F _ C V ⟨⟨z.point, hz⟩⟩ hV z hz,
      @placeIdeal_eq_primeIdealOf F _ C V ⟨⟨z.point, hz⟩⟩ hV w hw] at h
  -- Equality of ideals is equality of the corresponding points of `Spec Γ(C,V)`,
  have hspec : hV.primeIdealOf ⟨z.point, hz⟩ = hV.primeIdealOf ⟨w.point, hw⟩ :=
    PrimeSpectrum.ext h
  -- and `hV.fromSpec` is a left inverse of `hV.primeIdealOf`, hence both points of `V` agree.
  have hpt : z.point = w.point := by
    have h2 := congrArg (fun p => hV.fromSpec p) hspec
    rwa [IsAffineOpen.fromSpec_primeIdealOf, IsAffineOpen.fromSpec_primeIdealOf] at h2
  exact Subtype.ext hpt

end Work.SymQuot.DivOf
