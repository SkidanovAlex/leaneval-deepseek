import Mathlib
import Submission.Work.CurveBasics.Place.Coheight

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.style.haveILetI false

namespace Work.SpecLin.Alt

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

/-- The ring of sections of a smooth proper curve over a field, on a nonempty affine open
subscheme, is never a field.

Indeed, a nonempty affine open `U` of a curve contains a closed point `z` (closed points are
dense since `C` is of finite type over a field).  If `Γ(C, U)` were a field, then the stalk
`𝒪_{C,z}`, being a localization of `Γ(C, U)`, would be a field as well.  But the local ring at a
closed point of a curve has Krull dimension one. -/
theorem not_isField_chartSections {k : Type _} [Field k] (C : Work.CurveBasics.Curve k)
    (U : C.left.Opens) (hU : AlgebraicGeometry.IsAffineOpen U) [Nonempty U] :
    ¬ IsField (C.left.presheaf.obj (Opposite.op U)) := by
  intro hfield
  -- `U` is nonempty as a subset
  have hUne : (U : Set C.left).Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty U›
    exact ⟨x.1, x.2⟩
  -- a closed point of `C` lying in `U`
  obtain ⟨z, hzU, hzcl⟩ := nonempty_inter_closedPoints hUne U.isOpen.isLocallyClosed
  have hzclosed : IsClosed ({z} : Set C.left) := hzcl
  let x : U := ⟨z, hzU⟩
  -- the `Γ(C,U)`-algebra structure on the stalk coming from the germ
  letI : Algebra Γ(C.left, U) (C.left.presheaf.stalk x) :=
    C.left.presheaf.algebra_section_stalk x
  -- the stalk at `x` is the localization of `Γ(C,U)` at `primeIdealOf x`
  have hloc := hU.isLocalization_stalk x
  -- if `Γ(C,U)` is a field, the localization map is bijective, so the stalk is a field
  have hzero : (0 : Γ(C.left, U)) ∉ (hU.primeIdealOf x).asIdeal.primeCompl := by
    intro h; exact h (Ideal.zero_mem _)
  have hbij : Function.Bijective (algebraMap Γ(C.left, U) (C.left.presheaf.stalk x)) :=
    IsField.localization_map_bijective hzero hfield
  have hfieldStalk : IsField (C.left.presheaf.stalk x) :=
    (RingEquiv.ofBijective (algebraMap Γ(C.left, U) (C.left.presheaf.stalk x)) hbij).symm.toMulEquiv.isField
      hfield
  -- but the local ring at a closed point of a curve has Krull dimension one
  have h1 : ringKrullDim (C.left.presheaf.stalk x) = 0 :=
    ringKrullDim_eq_zero_of_isField hfieldStalk
  have h2 : ringKrullDim (C.left.presheaf.stalk x) = 1 :=
    Work.CurveBasics.Curve.Place.ringKrullDim_localRing (C := C) ⟨z, hzclosed⟩
  exact zero_ne_one (h1 ▸ h2)

end Work.SpecLin.Alt
