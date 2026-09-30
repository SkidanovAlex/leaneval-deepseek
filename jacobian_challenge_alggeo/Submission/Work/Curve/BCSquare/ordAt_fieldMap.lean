import Mathlib
import Submission.Work.CurveBasics.BCSquare
import Submission.Work.CurveBasics.BaseChange.ordAt_fieldMap

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.Curve.BCSquare

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry in
universe u in
/-- **The field map of a base-change square intertwines the structural maps of the local
rings.**  For a place-like point `y` of `C'`, the map `S.fieldMap : K(C) ⟶ K(C')` sends the
image of an element of the local ring `𝒪_{C, S.π y}` (inside `K(C)`) to the image of its
push-forward under `S.π.stalkMap y` (inside `K(C')`). -/
theorem fieldMap_stalkMap {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    {C : Curve k} {C' : Curve F} (S : Curve.BCSquare C C') (y : C'.left)
    (a : C.left.presheaf.stalk (S.π y)) :
    S.fieldMap.hom (algebraMap (C.left.presheaf.stalk (S.π y)) (↑C.functionField) a) =
      algebraMap (C'.left.presheaf.stalk y) (↑C'.functionField) ((S.π.stalkMap y).hom a) := by
  let Φ : (↑C.functionField) →+* (↑C'.functionField) := S.fieldMap.hom
  change Φ (algebraMap (C.left.presheaf.stalk (S.π y)) (↑C.functionField) a) =
      algebraMap (C'.left.presheaf.stalk y) (↑C'.functionField) ((S.π.stalkMap y).hom a)
  -- every element of a stalk is the germ of a section on an affine open neighbourhood
  obtain ⟨U, hxU, hUaff, r, hr⟩ :=
    TopCat.Presheaf.exists_mem_germ_eq_of_isBasis C.left.isBasis_affineOpens C.left.presheaf _ a
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  haveI hbc : Nonempty (S.preimage U) := S.instNonemptyPreimage U
  -- the two sides, evaluated on the germ of `r`
  have hA : algebraMap (C.left.presheaf.stalk (S.π y)) (↑C.functionField)
      (C.left.presheaf.germ U (S.π y) hxU r) = C.germToFunctionField U r :=
    Scheme.algebraMap_germ_eq_germToFunctionField (X := C.left) hxU r
  have hΦ : Φ (C.germToFunctionField U r) =
      Scheme.germToFunctionField (X := C'.left) (U := S.preimage U) (h := hbc)
        (S.π.app U r) := by
    rw [show Φ = S.fieldMap.hom from rfl, Work.CurveBasics.Curve.BCSquare.fieldMap]
    erw [ConcreteCategory.comp_apply, TopCat.Presheaf.germ_stalkSpecializes_apply,
      Scheme.Hom.germ_stalkMap_apply]
  have hψ : ((S.π.stalkMap y).hom)
      (C.left.presheaf.germ U (S.π y) hxU r) =
      C'.left.presheaf.germ (S.preimage U) y hxU (S.π.app U r) :=
    Scheme.Hom.germ_stalkMap_apply S.π U y hxU r
  have hβ : algebraMap (C'.left.presheaf.stalk y) (↑C'.functionField)
      (C'.left.presheaf.germ (S.preimage U) y hxU (S.π.app U r)) =
      Scheme.germToFunctionField (X := C'.left) (U := S.preimage U) (h := hbc)
        (S.π.app U r) :=
    @Scheme.algebraMap_germ_eq_germToFunctionField C'.left _ (S.preimage U) hbc y hxU
      (S.π.app U r)
  rw [← hr, hA, hψ]
  exact hΦ.trans hβ.symm

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry in
universe u in
theorem ordAt_fieldMap {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    {C : Curve k} {C' : Curve F} (S : Curve.BCSquare C C') (Q' : Curve.Place C')
    (h : IsClosed ({S.π Q'.point} : Set C.left)) {f : C.functionField} (hf : f ≠ 0) :
    C'.ordAt (S.fieldMap.hom f) Q' = S.ramIdx Q' * C.ordAt f (S.under Q' h) := by
  classical
  -- the local rings of `C` at `Q` and of `C'` at `Q'` are discrete valuation rings
  haveI hDVR : IsDiscreteValuationRing (C.left.presheaf.stalk (S.π Q'.point)) :=
    (S.under Q' h).instIsDiscreteValuationRing
  haveI hDVR' : IsDiscreteValuationRing (C'.left.presheaf.stalk Q'.point) :=
    Q'.instIsDiscreteValuationRing
  -- a uniformizer vanishes to order one
  have hu' : Ring.ordFrac (C.left.presheaf.stalk (S.under Q' h).point) (K := ↑C.functionField)
      (S.under Q' h).uniformizer = WithZero.exp 1 := by
    have h1 : Scheme.ord (S.under Q' h).uniformizer (S.under Q' h).point = 1 :=
      Work.CurveBasics.Place.ord_uniformizer (S.under Q' h)
    have hne : (S.under Q' h).uniformizer ≠ 0 := by
      intro h0; rw [h0] at h1; simp at h1
    have h2 := (Scheme.ord_eq_iff (S.under Q' h).eq_coheight_one hne).mp h1
    simpa [Scheme.ordHom, WithZero.exp] using h2
  have hu : Ring.ordFrac (C.left.presheaf.stalk (S.π Q'.point))
      (K := ↑C.functionField) (S.under Q' h).uniformizer = WithZero.exp 1 := hu'
  -- the map on function fields comes from the map of local rings
  have hcomm : ∀ a : C.left.presheaf.stalk (S.π Q'.point),
      S.fieldMap.hom
          (algebraMap (C.left.presheaf.stalk (S.π Q'.point)) (↑C.functionField) a) =
        algebraMap (C'.left.presheaf.stalk Q'.point) (↑C'.functionField)
          ((S.π.stalkMap Q'.point).hom a) :=
    fun a => fieldMap_stalkMap S Q'.point a
  haveI : Nontrivial (↑C'.functionField) := inferInstance
  have hcore := ordFrac_log_comp
    (A := C.left.presheaf.stalk (S.π Q'.point)) (K := ↑C.functionField)
    (B := C'.left.presheaf.stalk Q'.point) (L := ↑C'.functionField)
    (S.fieldMap.hom) S.fieldMap.hom.injective
    ((S.π.stalkMap Q'.point).hom) hcomm (u := (S.under Q' h).uniformizer) hu f
  have hram : S.ramIdx Q' = (Ring.ordFrac (C'.left.presheaf.stalk Q'.point)
      (K := ↑C'.functionField) (S.fieldMap.hom (S.under Q' h).uniformizer)).log := by
    rw [Work.CurveBasics.Curve.BCSquare.ramIdx, dite_eq_left h,
      Curve.ordAt_eq_log_ordFrac (C := C') Q']
  rw [Curve.ordAt_eq_log_ordFrac (C := C') Q' (S.fieldMap.hom f), hram,
    Curve.ordAt_eq_log_ordFrac (C := C) (S.under Q' h) f]
  exact hcore

end Work.Curve.BCSquare
