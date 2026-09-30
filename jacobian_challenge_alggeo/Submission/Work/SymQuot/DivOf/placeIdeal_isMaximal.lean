/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The ideal of a place in an affine open is maximal

For a curve `C` over a field `F` and an affine open `V ⊆ C`, the ring `Γ(C,V)` is a Dedekind
domain whose maximal ideals are the closed points of `V`.  This file proves the pointwise form
of that statement for the ideal `placeIdeal C V z hz = ker (Γ(C,V) → κ(z))` attached to a place
`z ∈ V`:

* `placeIdeal_eq_primeIdealOf` — `placeIdeal C V z hz` is the prime ideal
  `hV.primeIdealOf ⟨z.point, hz⟩` of `Spec Γ(C,V)` corresponding to the point `z`;
* `placeIdeal_isMaximal` — since `z` is a closed point, that prime is maximal.

The proof does not need the Dedekind property of `Γ(C,V)`: `IsAffineOpen.isLocalization_stalk`
identifies `𝒪_{C,z}` with the localization of `Γ(C,V)` at the prime `hV.primeIdealOf ⟨z, hz⟩`,
and `IsLocalization.AtPrime.to_map_mem_maximal_iff` then computes the kernel of
`Γ(C,V) → 𝒪_{C,z} → κ(z)`.
-/
import Mathlib
import Submission.Work.SymQuot.DivOf.AffineCurve

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot.DivOf

/-- **The ideal of a place in an affine open is the prime ideal of the corresponding point of
`Spec Γ(C,V)`**: the kernel of `Γ(C,V) → 𝒪_{C,z} → κ(z)` is `hV.primeIdealOf ⟨z, hz⟩`. -/
theorem placeIdeal_eq_primeIdealOf {F : Type u} [Field F] {C : Work.CurveBasics.Curve F}
    {V : C.left.Opens} [Nonempty V] (hV : AlgebraicGeometry.IsAffineOpen V)
    (z : Work.CurveBasics.Curve.Place C) (hz : z.point ∈ V) :
    Work.SymQuot.DivOf.placeIdeal C V z hz
      = (hV.primeIdealOf ⟨z.point, hz⟩).asIdeal := by
  -- `𝒪_{C,z}` is the localization of `Γ(C,V)` at the prime of `z`, with the `Algebra`
  -- structure given by the germ map.
  letI : Algebra (C.left.presheaf.obj (Opposite.op V)) (C.left.presheaf.stalk z.point) :=
    (C.left.presheaf.germ V z.point hz).hom.toAlgebra
  haveI hLoc : IsLocalization.AtPrime (C.left.presheaf.stalk z.point)
      (hV.primeIdealOf ⟨z.point, hz⟩).asIdeal := hV.isLocalization_stalk ⟨z.point, hz⟩
  ext a
  rw [Work.SymQuot.DivOf.placeIdeal, RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply,
    IsLocalRing.residue_eq_zero_iff]
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff (C.left.presheaf.stalk z.point)
    (hV.primeIdealOf ⟨z.point, hz⟩).asIdeal a

theorem placeIdeal_isMaximal {F : Type u} [Field F] {C : Work.CurveBasics.Curve F}
    {V : C.left.Opens} [Nonempty V] (hV : AlgebraicGeometry.IsAffineOpen V)
    (z : Work.CurveBasics.Curve.Place C) (hz : z.point ∈ V) :
    (Work.SymQuot.DivOf.placeIdeal C V z hz).IsMaximal := by
  rw [placeIdeal_eq_primeIdealOf hV z hz]
  exact hV.primeIdealOf_isMaximal_of_isClosed ⟨z.point, hz⟩ z.isClosed

end Work.SymQuot.DivOf
