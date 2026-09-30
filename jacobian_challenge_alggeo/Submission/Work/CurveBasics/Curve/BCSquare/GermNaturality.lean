import Mathlib
import Submission.Work.CurveBasics.BCSquare

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveBasics.Curve.BCSquare

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

noncomputable section

/-- In an irreducible space every non-empty open contains the generic point. -/
theorem genericPoint_mem_of_nonempty {X : Scheme.{u}} [IrreducibleSpace X] (U : X.Opens)
    [Nonempty U] : genericPoint X ∈ U := by
  by_contra hU
  have hclosed : IsClosed (U : Set X)ᶜ := U.isOpen.isClosed_compl
  have h1 : closure ({genericPoint X} : Set X) ⊆ (U : Set X)ᶜ :=
    closure_minimal (Set.singleton_subset_iff.mpr hU) hclosed
  have h2 : closure ({genericPoint X} : Set X) = Set.univ := (genericPoint_spec X).def
  rw [h2] at h1
  obtain ⟨y, hy⟩ := ‹Nonempty U›
  exact (h1 (Set.mem_univ y)) hy

/-- The preimage of a non-empty open under a morphism mapping the generic point to the generic
point is non-empty. -/
theorem nonempty_preimage_of_genericPoint {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (f : X ⟶ Y) (h : f (genericPoint X) = genericPoint Y) (V : Y.Opens)
    [Nonempty V] : Nonempty (f ⁻¹ᵁ V) :=
  ⟨⟨genericPoint X, by
    show f (genericPoint X) ∈ V
    rw [h]
    exact genericPoint_mem_of_nonempty V⟩⟩

/-- **Naturality of `germToFunctionField`.**  For a morphism of schemes `f : X ⟶ Y` carrying the
generic point of `X` to the generic point of `Y`, the map induced by `f` on function fields
intertwines the canonical maps from the sections over an open set and over its preimage. -/
theorem germ_stalkMap_germToFunctionField {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (f : X ⟶ Y) (h : f (genericPoint X) = genericPoint Y) (V : Y.Opens)
    [Nonempty V] [Nonempty (f ⁻¹ᵁ V)] :
    Y.germToFunctionField V ≫ Y.presheaf.stalkSpecializes
        ((Inseparable.of_eq h.symm).specializes') ≫ f.stalkMap (genericPoint X) =
      f.app V ≫ X.germToFunctionField (f ⁻¹ᵁ V) := by
  rw [← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes, Scheme.Hom.germ_stalkMap]

/-- The generic point of an isomorphic scheme. -/
theorem iso_genericPoint {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (e : X ≅ Y) : e.hom (genericPoint X) = genericPoint Y :=
  genericPoint_eq_of_isOpenImmersion e.hom

/-- The canonical isomorphism between an arbitrary base-change square of curves and the
tautological base-change square `bcSquare C F`. -/
noncomputable def isoBaseChange {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    {C : Curve k} {C' : Curve F} (S : Curve.BCSquare C C') : C'.left ≅ (C.baseChange F).left :=
  S.isPullback.isoIsPullback _ _ (Curve.bcSquare C F).isPullback

theorem isoBaseChange_hom_fst {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    {C : Curve k} {C' : Curve F} (S : Curve.BCSquare C C') :
    (isoBaseChange S).hom ≫ Curve.baseChangeFst C F = S.π :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

theorem isoBaseChange_hom_snd {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    {C : Curve k} {C' : Curve F} (S : Curve.BCSquare C C') :
    (isoBaseChange S).hom ≫ Curve.baseChangeHom C F = C'.hom :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- The map on function fields induced by an isomorphism of schemes. -/
noncomputable def functionFieldMapIso {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (e : X ≅ Y) : Y.functionField ⟶ X.functionField :=
  Y.presheaf.stalkSpecializes ((Inseparable.of_eq (iso_genericPoint e).symm).specializes') ≫
    e.hom.stalkMap (genericPoint X)

/-- The compatibility of `functionFieldMapIso` with the canonical maps from the sections. -/
theorem functionFieldMapIso_germToFunctionField {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (e : X ≅ Y) (V : Y.Opens) [Nonempty V] [Nonempty (e.hom ⁻¹ᵁ V)]
    (b : Γ(Y, V)) :
    (functionFieldMapIso e).hom ((Y.germToFunctionField V).hom b) =
      (X.germToFunctionField (e.hom ⁻¹ᵁ V)).hom ((e.hom.app V).hom b) := by
  have h := germ_stalkMap_germToFunctionField e.hom (iso_genericPoint e) V
  have h2 := congrArg (fun (φ : Γ(Y, V) ⟶ X.functionField) => φ.hom b) h
  simpa only [functionFieldMapIso, ConcreteCategory.comp_apply] using h2

/-- An isomorphism of schemes identifies the ranges of the canonical maps to the function field
over corresponding open subsets. -/
theorem functionFieldMapIso_image_range {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (e : X ≅ Y) (V : Y.Opens) [Nonempty V] [Nonempty (e.hom ⁻¹ᵁ V)] :
    (functionFieldMapIso e).hom '' (((Y.germToFunctionField V).hom.range : Set Y.functionField)) =
      ((X.germToFunctionField (e.hom ⁻¹ᵁ V)).hom.range : Set X.functionField) := by
  ext x
  constructor
  · rintro ⟨y, ⟨b, rfl⟩, rfl⟩
    exact ⟨(e.hom.app V).hom b, (functionFieldMapIso_germToFunctionField e V b).symm⟩
  · rintro ⟨a, rfl⟩
    refine ⟨(Y.germToFunctionField V).hom ((inv (e.hom.app V)).hom a), ⟨_, rfl⟩, ?_⟩
    rw [functionFieldMapIso_germToFunctionField e V, IsIso.inv_hom_id_apply]

/-- The range of the canonical map to the function field only depends on the open subset up to
equality of the open subsets. -/
theorem range_germToFunctionField_congr {X : Scheme.{u}} [IrreducibleSpace X] {U U' : X.Opens}
    (h : U = U') [Nonempty U] [Nonempty U'] :
    ((X.germToFunctionField U).hom.range : Set X.functionField) =
      ((X.germToFunctionField U').hom.range : Set X.functionField) := by
  subst h
  congr 1

end

end Work.CurveBasics.Curve.BCSquare
