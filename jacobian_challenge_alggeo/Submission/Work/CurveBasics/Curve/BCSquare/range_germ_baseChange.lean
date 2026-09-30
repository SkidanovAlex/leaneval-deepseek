import Mathlib
import Submission.Work.CurveBasics.BCSquare
import Submission.Work.CurveBasics.BaseChange.range_germ_baseChange
import Submission.Work.CurveBasics.Curve.BCSquare.GermNaturality
import Submission.Work.CurveBasics.Curve.BCSquare.algebraMap_functionFieldMapIso
import Submission.Work.CurveBasics.Curve.BCSquare.fieldMap_eq_functionFieldMapIso_apply

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveBasics.Curve.BCSquare

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry in
universe u in
theorem range_germ_baseChange {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    {C : Curve k} {C' : Curve F} (S : Curve.BCSquare C C') (W : C.left.Opens)
    (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W] :
    ((C'.germToFunctionField (S.preimage W)).hom.range : Set C'.functionField) =
      Submodule.span F (S.fieldMap.hom '' ((C.germToFunctionField W).hom.range : Set C.functionField)) := by
  haveI hneW : Nonempty (S.preimage W) := inferInstance
  -- the tautological statement for `C.baseChange F`
  have hT := BaseChange.range_germ_baseChange F W hW
  -- the isomorphism between `S` and the tautological base change square
  have hπ : (isoBaseChange S).hom ≫ Curve.baseChangeFst C F = S.π := isoBaseChange_hom_fst S
  have hgen : (isoBaseChange S).hom (genericPoint C'.left) =
      genericPoint (C.baseChange F).left := iso_genericPoint (isoBaseChange S)
  haveI hneV : Nonempty (Curve.bcOpens C F W) := inferInstance
  haveI hneV' : Nonempty ((isoBaseChange S).hom ⁻¹ᵁ Curve.bcOpens C F W) :=
    nonempty_preimage_of_genericPoint (isoBaseChange S).hom hgen (Curve.bcOpens C F W)
  -- the two properties of the induced map on function fields
  have hfieldMap : ∀ x : C.functionField,
      (functionFieldMapIso (isoBaseChange S)).hom ((C.functionFieldMap F).hom x) =
        S.fieldMap.hom x :=
    fun x => fieldMap_eq_functionFieldMapIso_apply S x
  have halg : ∀ c : F,
      (functionFieldMapIso (isoBaseChange S)).hom
          (algebraMap F (C.baseChange F).functionField c) =
        algebraMap F C'.functionField c :=
    fun c => algebraMap_functionFieldMapIso S c
  -- `Φ` is `F`-linear
  let Φlin : (C.baseChange F).functionField →ₗ[F] C'.functionField :=
    { toFun := (functionFieldMapIso (isoBaseChange S)).hom
      map_add' := fun x y => map_add _ x y
      map_smul' := fun c x => by
        show (functionFieldMapIso (isoBaseChange S)).hom (c • x) =
          c • (functionFieldMapIso (isoBaseChange S)).hom x
        rw [Algebra.smul_def, map_mul, halg c, ← Algebra.smul_def] }
  -- the preimage open of the tautological square is the preimage open of `S`
  have hV : (isoBaseChange S).hom ⁻¹ᵁ (Curve.bcOpens C F W) = S.preimage W := by
    rw [Curve.bcOpens, Curve.BCSquare.preimage, ← hπ]
    rfl
  -- the isomorphism identifies the two ranges
  have hH4 := functionFieldMapIso_image_range (isoBaseChange S) (Curve.bcOpens C F W)
  -- the image of the image of the tautological range is the range of `S.fieldMap`
  have himg : Φlin '' ((C.functionFieldMap F).hom ''
        ((C.germToFunctionField W).hom.range : Set C.functionField)) =
      S.fieldMap.hom '' ((C.germToFunctionField W).hom.range : Set C.functionField) := by
    ext x
    constructor
    · rintro ⟨y, ⟨f, ⟨a, rfl⟩, rfl⟩, rfl⟩
      exact ⟨(C.germToFunctionField W).hom a, ⟨a, rfl⟩, (hfieldMap _).symm⟩
    · rintro ⟨f, ⟨a, rfl⟩, rfl⟩
      exact ⟨(C.functionFieldMap F).hom ((C.germToFunctionField W).hom a),
        ⟨_, ⟨a, rfl⟩, rfl⟩, hfieldMap _⟩
  have hrange := range_germToFunctionField_congr (X := C'.left) hV
  rw [← hrange, ← hH4, hT]
  change (⇑Φlin '' ↑(Submodule.span F ((C.functionFieldMap F).hom ''
      ((C.germToFunctionField W).hom.range : Set C.functionField))) : Set C'.functionField) =
    ↑(Submodule.span F (S.fieldMap.hom ''
      ((C.germToFunctionField W).hom.range : Set C.functionField)))
  rw [← Submodule.map_coe (f := Φlin), ← Submodule.span_image (f := Φlin), himg]

end Work.CurveBasics.Curve.BCSquare
