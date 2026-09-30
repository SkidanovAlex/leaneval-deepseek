import Mathlib
import Submission.Work.CurveBasics.BaseChangeDivisor
import Submission.Work.CurveBasics.BaseChange.mem_range_germ_iff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.CurveBasics.BaseChange

universe v

variable {k : Type v} [Field k]

/-- **The field map on germs.**  For an open `U ⊆ C` and a section `s ∈ Γ(C, U)`, the image of
the germ of `s` at the generic point of `C` under the field map `K(C) ⟶ K(C_F)` is the germ of
`baseChangeFst.app U s` at the generic point of `C_F`. -/
theorem functionFieldMap_germToFunctionField (C : Curve k) (F : Type v) [Field F] [Algebra k F]
    (U : C.left.Opens) [Nonempty U] (s : Γ(C.left, U)) :
    (C.functionFieldMap F).hom (C.left.germToFunctionField U s) =
      (C.baseChange F).left.germToFunctionField ((C.baseChangeFst F) ⁻¹ᵁ U)
        ((C.baseChangeFst F).app U s) := by
  rw [Curve.functionFieldMap]
  erw [ConcreteCategory.comp_apply]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  erw [Scheme.Hom.germ_stalkMap_apply]
  rfl

/-- **The field map is compatible with the local rings.**  If `z` is a point of `C_F` and
`y = baseChangeFst z`, then the composite `O_{C,y} ⟶ O_{C_F,z} ⟶ K(C_F)` of the stalk map of
the projection with the inclusion of the local ring of `C_F` at `z` into its function field is
the composite `O_{C,y} ⟶ K(C) ⟶ K(C_F)` of the inclusion of the local ring of `C` at `y` into
`K(C)` with the field map. -/
theorem functionFieldMap_algebraMap_stalk (C : Curve k) (F : Type v) [Field F] [Algebra k F]
    (z : (C.baseChange F).left) (a : C.left.presheaf.stalk ((C.baseChangeFst F) z)) :
    (C.functionFieldMap F).hom
        (algebraMap (C.left.presheaf.stalk ((C.baseChangeFst F) z)) C.functionField a) =
      algebraMap ((C.baseChange F).left.presheaf.stalk z) (C.baseChange F).functionField
        ((C.baseChangeFst F).stalkMap z a) := by
  obtain ⟨U, hU, s, hs⟩ := C.left.presheaf.exists_germ_eq a
  rw [← hs]
  haveI : Nonempty U := ⟨⟨_, hU⟩⟩
  have hU' : z ∈ (C.baseChangeFst F) ⁻¹ᵁ U := hU
  haveI : Nonempty ((C.baseChangeFst F) ⁻¹ᵁ U) := ⟨⟨z, hU'⟩⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField C.left hU s]
  erw [Scheme.Hom.germ_stalkMap_apply]
  erw [Scheme.algebraMap_germ_eq_germToFunctionField (C.baseChange F).left
        (U := (C.baseChangeFst F) ⁻¹ᵁ U) hU' ((C.baseChangeFst F).app U s)]
  exact functionFieldMap_germToFunctionField C F U s

theorem functionFieldMap_algebraMap_stalk_under (C : Curve k) (F : Type v) [Field F]
    [Algebra k F] (Q' : (C.baseChange F).Place)
    (h : IsClosed ({(Curve.baseChangeFst C F) Q'.point} : Set C.left))
    (a : C.left.presheaf.stalk ((Curve.baseChangeFst C F) Q'.point)) :
    (C.functionFieldMap F).hom
        (algebraMap (C.left.presheaf.stalk (C.under F Q' h).point) C.functionField a) =
      algebraMap ((C.baseChange F).left.presheaf.stalk Q'.point) (C.baseChange F).functionField
        ((C.baseChangeFst F).stalkMap Q'.point a) :=
  functionFieldMap_algebraMap_stalk C F Q'.point a

/-- The uniformizer of `C.under F Q' h`, viewed in `K(C)`, lies in the local ring of `C_F` at
`Q'`; equivalently its order of vanishing at `Q'` is nonnegative. -/
theorem ordAt_functionFieldMap_uniformizer (C : Curve k) (F : Type v) [Field F] [Algebra k F]
    (Q' : (C.baseChange F).Place)
    (h : IsClosed ({(Curve.baseChangeFst C F) Q'.point} : Set C.left)) :
    0 ≤ (C.baseChange F).ordAt
      ((C.functionFieldMap F).hom (C.under F Q' h).uniformizer) Q' := by
  refine (mem_range_algebraMap_stalk_iff (C.baseChange F) Q' _).mp ?_
  rw [Curve.Place.uniformizer]
  exact ⟨_, (functionFieldMap_algebraMap_stalk_under C F Q' h _).symm⟩

universe u in
open Work.CurveBasics in
theorem divMap_isEffective {k : Type u} [Field k] {C : Curve k} (F : Type u) [Field F]
    [Algebra k F] {D : C.Div} (hD : D.IsEffective) : (C.divMap F D).IsEffective := by
  intro Q'
  rw [Curve.divMap_apply]
  simp only [Curve.divMapCoeff]
  split
  · rename_i h
    refine mul_nonneg (hD _) ?_
    rw [Curve.ramIdx, dite_eq_left h]
    exact ordAt_functionFieldMap_uniformizer C F Q' h
  · exact le_refl 0

end Work.CurveBasics.BaseChange
