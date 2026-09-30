import Mathlib
import Submission.Work.CurveBasics.BCSquare
import Submission.Work.CurveBasics.BaseChange.divMap_div

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveBasics.Curve.BCSquare

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry
open scoped Classical

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

universe v

variable {k : Type v} [Field k] {F : Type v} [Field F] [Algebra k F]
variable {C : Curve k} {C' : Curve F}

/-! ### The field map of a base-change square on germs and on local rings

For an arbitrary cartesian square `S : BCSquare C C'` the induced map of function fields
`S.fieldMap : K(C) ⟶ K(C')` is, by definition, the composite of the specialisation of the
stalk at the generic point of `C` and the stalk map of `S.π`.  Exactly as in the tautological
case (`Work.CurveBasics.BaseChange.functionFieldMap`) this makes it compatible with the
structure sheaves: it carries the germ of a section on `U ⊆ C` to the germ of its image on
`S.π ⁻¹ᵁ U`, and it intertwines the canonical maps `𝒪_{C,y} ⟶ K(C)` and
`𝒪_{C',z} ⟶ K(C')` along the stalk map of `S.π`. -/

/-- **The field map on germs.**  For an open `U ⊆ C` and a section `s ∈ Γ(C, U)`, the image of
the germ of `s` at the generic point of `C` under the field map is the germ of `S.π.app U s` at
the generic point of `C'`. -/
theorem fieldMap_germToFunctionField_apply (S : BCSquare C C') (U : C.left.Opens) [Nonempty U]
    (s : Γ(C.left, U)) :
    S.fieldMap.hom (C.left.germToFunctionField U s) =
      C'.left.germToFunctionField (S.π ⁻¹ᵁ U) (S.π.app U s) := by
  rw [fieldMap]
  erw [ConcreteCategory.comp_apply]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  erw [Scheme.Hom.germ_stalkMap_apply]

/-- **The field map is compatible with the local rings.**  If `z` is a point of `C'`, then the
composite `𝒪_{C,S.π z} ⟶ 𝒪_{C',z} ⟶ K(C')` of the stalk map of the projection with the
inclusion of the local ring of `C'` at `z` into its function field is the composite
`𝒪_{C,S.π z} ⟶ K(C) ⟶ K(C')` of the inclusion of the local ring of `C` at `S.π z` into `K(C)`
with the field map. -/
theorem fieldMap_algebraMap_stalk (S : BCSquare C C') (z : C'.left)
    (a : C.left.presheaf.stalk (S.π z)) :
    S.fieldMap.hom (algebraMap (C.left.presheaf.stalk (S.π z)) C.functionField a) =
      algebraMap (C'.left.presheaf.stalk z) C'.functionField (S.π.stalkMap z a) := by
  obtain ⟨U, hU, s, hs⟩ := C.left.presheaf.exists_germ_eq a
  rw [← hs]
  haveI : Nonempty U := ⟨⟨_, hU⟩⟩
  have hU' : z ∈ S.π ⁻¹ᵁ U := hU
  haveI : Nonempty (S.π ⁻¹ᵁ U) := ⟨⟨z, hU'⟩⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField C.left hU s]
  erw [Scheme.Hom.germ_stalkMap_apply]
  erw [Scheme.algebraMap_germ_eq_germToFunctionField C'.left
        (U := S.π ⁻¹ᵁ U) hU' (S.π.app U s)]
  exact fieldMap_germToFunctionField_apply S U s

/-- **Regularity transfer.**  If a rational function `g` on `C` is regular at the image in `C`
of a place `Q'` of `C'` (i.e. lies in the image of the local ring `𝒪_{C,S.π Q'.point}`), then
its image in `K(C')` is regular at `Q'`. -/
theorem ordAt_fieldMap_nonneg_of_mem_range (S : BCSquare C C') (Q' : C'.Place)
    {g : C.functionField}
    (hg : g ∈ (algebraMap (C.left.presheaf.stalk (S.π Q'.point)) C.functionField).range) :
    0 ≤ C'.ordAt (S.fieldMap.hom g) Q' := by
  obtain ⟨a, rfl⟩ := hg
  rw [fieldMap_algebraMap_stalk S Q'.point a]
  exact (BaseChange.mem_range_algebraMap_stalk_iff C' Q' _).mp
    ⟨S.π.stalkMap Q'.point a, rfl⟩

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry in
universe u in
theorem ordAt_fieldMap_of_not_isClosed {k : Type u} [Field k] {F : Type u} [Field F]
    [Algebra k F] {C : Curve k} {C' : Curve F} (S : Curve.BCSquare C C')
    (Q' : Curve.Place C') (h : ¬ IsClosed ({S.π Q'.point} : Set C.left))
    {f : C.functionField} (hf : f ≠ 0) : C'.ordAt (S.fieldMap.hom f) Q' = 0 := by
  -- the image of `Q'` in `C` is the generic point
  have hgen : S.π Q'.point = genericPoint C.left := by
    rcases C.eq_genericPoint_or_isClosed (S.π Q'.point) with hgen | hcl
    · exact hgen
    · exact absurd hcl h
  -- a rational function is regular at the generic point, and so is its inverse
  have hmem : f ∈ (algebraMap (C.left.presheaf.stalk (S.π Q'.point)) C.functionField).range :=
    BaseChange.mem_range_algebraMap_genericPoint hgen f
  have hmem' : f⁻¹ ∈
      (algebraMap (C.left.presheaf.stalk (S.π Q'.point)) C.functionField).range :=
    BaseChange.mem_range_algebraMap_genericPoint hgen f⁻¹
  have h1 : 0 ≤ C'.ordAt (S.fieldMap.hom f) Q' :=
    ordAt_fieldMap_nonneg_of_mem_range S Q' hmem
  have h2 : 0 ≤ C'.ordAt (S.fieldMap.hom f⁻¹) Q' :=
    ordAt_fieldMap_nonneg_of_mem_range S Q' hmem'
  -- `S.fieldMap` is nontrivial, so it carries inverses to inverses for the order
  have hne : S.fieldMap.hom f ≠ 0 := by
    intro h0
    have hone : S.fieldMap.hom f⁻¹ * S.fieldMap.hom f = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hf, map_one]
    rw [h0, mul_zero] at hone
    exact one_ne_zero hone.symm
  have h3 : C'.ordAt (S.fieldMap.hom f⁻¹) Q' = -C'.ordAt (S.fieldMap.hom f) Q' := by
    rw [map_inv₀]
    exact Curve.ordAt_inv C' hne Q'
  linarith

end Work.CurveBasics.Curve.BCSquare
