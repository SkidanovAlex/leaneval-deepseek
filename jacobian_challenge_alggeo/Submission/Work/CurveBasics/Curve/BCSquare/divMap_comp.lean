import Mathlib
import Submission.Work.CurveBasics.BCSquare
import Submission.Work.CurveBasics.Curve.BCSquare.ordAt_fieldMap
import Submission.Work.CurveBasics.Curve.BCSquare.ordAt_fieldMap_of_not_isClosed
import Submission.Work.CurveBasics.Curve.BCSquare.fieldMap_injective

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.CurveBasics.Curve.BCSquare

universe v

variable {k : Type v} [Field k] {F : Type v} [Field F] [Algebra k F]
variable {F' : Type v} [Field F'] [Algebra F F'] [Algebra k F'] [IsScalarTower k F F']
variable {C : Curve k} {C' : Curve F} {C'' : Curve F'}

theorem germ_genericPoint_eq_germToFunctionField' {X : Scheme.{v}} [IrreducibleSpace X]
    (U : X.Opens) [Nonempty U] (hU : genericPoint X ∈ U) (s : Γ(X, U)) :
    X.presheaf.germ U (genericPoint X) hU s = X.germToFunctionField U s := by
  simp only [Scheme.germToFunctionField]

theorem germToFunctionField_congr_hom' {X Y : Scheme.{v}} [IrreducibleSpace X] {k l : X ⟶ Y}
    (hk : k = l) (U : Y.Opens) [Nonempty (k ⁻¹ᵁ U)] [Nonempty (l ⁻¹ᵁ U)] (s : Γ(Y, U)) :
    X.germToFunctionField (k ⁻¹ᵁ U) (k.app U s) = X.germToFunctionField (l ⁻¹ᵁ U) (l.app U s) := by
  cases hk
  congr 1

theorem fieldMap_comp_aux (S : Curve.BCSquare C C') (T : Curve.BCSquare C' C'') :
    (S.comp T).fieldMap = S.fieldMap ≫ T.fieldMap := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  obtain ⟨U, hU, s, hs⟩ := C.left.presheaf.exists_germ_eq x
  haveI hUne : Nonempty U := ⟨⟨genericPoint C.left, hU⟩⟩
  have hgerm : C.left.presheaf.germ U (genericPoint C.left) hU s = C.germToFunctionField U s :=
    germ_genericPoint_eq_germToFunctionField' U hU s
  rw [← hs, hgerm, CommRingCat.hom_comp]
  rw [fieldMap_germToFunctionField_apply (S.comp T) U s]
  rw [RingHom.comp_apply, fieldMap_germToFunctionField_apply S U s,
      fieldMap_germToFunctionField_apply T (S.π ⁻¹ᵁ U) (S.π.app U s)]
  exact germToFunctionField_congr_hom' rfl U s

theorem fieldMap_comp_apply (S : Curve.BCSquare C C') (T : Curve.BCSquare C' C'')
    (x : C.functionField) :
    (S.comp T).fieldMap.hom x = T.fieldMap.hom (S.fieldMap.hom x) := by
  rw [fieldMap_comp_aux S T, CommRingCat.hom_comp]
  rfl

theorem not_isClosed_genericPoint (C : Curve k) :
    ¬ IsClosed ({genericPoint C.left} : Set C.left) := by
  intro h
  obtain ⟨a, b, hab⟩ := exists_pair_ne C.left
  have hsub : ({genericPoint C.left} : Set C.left) = Set.univ := by
    rw [← h.closure_eq, genericPoint_spec]
  have ha : a = genericPoint C.left := by
    have : a ∈ ({genericPoint C.left} : Set C.left) := by rw [hsub]; trivial
    simpa using this
  have hb : b = genericPoint C.left := by
    have : b ∈ ({genericPoint C.left} : Set C.left) := by rw [hsub]; trivial
    simpa using this
  exact hab (ha.trans hb.symm)

theorem ramIdx_comp (S : Curve.BCSquare C C') (T : Curve.BCSquare C' C'')
    (Q'' : Curve.Place C'') (hT : IsClosed ({T.π Q''.point} : Set C'.left)) :
    (S.comp T).ramIdx Q'' = T.ramIdx Q'' * S.ramIdx (T.under Q'' hT) := by
  classical
  by_cases hS : IsClosed ({S.π (T.under Q'' hT).point} : Set C.left)
  · have h : IsClosed ({(S.comp T).π Q''.point} : Set C.left) := by
      show IsClosed ({S.π (T.π Q''.point)} : Set C.left)
      rwa [show T.π Q''.point = (T.under Q'' hT).point from rfl]
    have hcomp : (S.comp T).ramIdx Q'' =
        C''.ordAt ((S.comp T).fieldMap.hom ((S.comp T).under Q'' h).uniformizer) Q'' := by
      rw [Curve.BCSquare.ramIdx, dif_pos h]
    have hSram : S.ramIdx (T.under Q'' hT) =
        C'.ordAt (S.fieldMap.hom (S.under (T.under Q'' hT) hS).uniformizer)
          (T.under Q'' hT) := by
      rw [Curve.BCSquare.ramIdx, dif_pos hS]
    have hD : (S.comp T).under Q'' h = S.under (T.under Q'' hT) hS := Subtype.ext rfl
    have hu : (S.under (T.under Q'' hT) hS).uniformizer ≠ 0 := by
      intro h1
      have h2 := Work.CurveBasics.Place.ord_uniformizer (S.under (T.under Q'' hT) hS)
      rw [h1] at h2
      simp at h2
    have hf : S.fieldMap.hom (S.under (T.under Q'' hT) hS).uniformizer ≠ 0 := by
      intro h0
      exact hu (fieldMap_injective S (by rw [h0, map_zero]))
    rw [hcomp, hSram, hD, fieldMap_comp_apply S T]
    exact ordAt_fieldMap T Q'' hT hf
  · have h : ¬ IsClosed ({(S.comp T).π Q''.point} : Set C.left) := by
      show ¬ IsClosed ({S.π (T.π Q''.point)} : Set C.left)
      rwa [show T.π Q''.point = (T.under Q'' hT).point from rfl]
    have hcomp : (S.comp T).ramIdx Q'' = 0 := by
      rw [Curve.BCSquare.ramIdx, dif_neg h]
    have hSram : S.ramIdx (T.under Q'' hT) = 0 := by
      rw [Curve.BCSquare.ramIdx, dif_neg hS]
    rw [hcomp, hSram, mul_zero]

theorem divMapCoeff_comp (S : Curve.BCSquare C C') (T : Curve.BCSquare C' C'')
    (D : C.Div) (Q'' : Curve.Place C'') :
    (S.comp T).divMapCoeff D Q'' = T.divMapCoeff (S.divMap D) Q'' := by
  classical
  by_cases hT : IsClosed ({T.π Q''.point} : Set C'.left)
  · by_cases hS : IsClosed ({S.π (T.under Q'' hT).point} : Set C.left)
    · have h : IsClosed ({(S.comp T).π Q''.point} : Set C.left) := by
        show IsClosed ({S.π (T.π Q''.point)} : Set C.left)
        rwa [show T.π Q''.point = (T.under Q'' hT).point from rfl]
      have hD : (S.comp T).under Q'' h = S.under (T.under Q'' hT) hS := Subtype.ext rfl
      rw [Curve.BCSquare.divMapCoeff, dif_pos h, Curve.BCSquare.divMapCoeff, dif_pos hT]
      rw [divMap_apply, Curve.BCSquare.divMapCoeff, dif_pos hS]
      rw [hD, ramIdx_comp S T Q'' hT]
      ring
    · have h : ¬ IsClosed ({(S.comp T).π Q''.point} : Set C.left) := by
        show ¬ IsClosed ({S.π (T.π Q''.point)} : Set C.left)
        rwa [show T.π Q''.point = (T.under Q'' hT).point from rfl]
      rw [Curve.BCSquare.divMapCoeff, dif_neg h, Curve.BCSquare.divMapCoeff, dif_pos hT]
      rw [divMap_apply, Curve.BCSquare.divMapCoeff, dif_neg hS]
      ring
  · have hgen : T.π Q''.point = genericPoint C'.left := by
      rcases Curve.eq_genericPoint_or_isClosed C' (T.π Q''.point) with hh | hh
      · exact hh
      · exact absurd hh hT
    have h : ¬ IsClosed ({(S.comp T).π Q''.point} : Set C.left) := by
      rw [show (S.comp T).π Q''.point = S.π (T.π Q''.point) from rfl, hgen,
          Curve.BCSquare.π_genericPoint S]
      exact not_isClosed_genericPoint C
    rw [Curve.BCSquare.divMapCoeff, dif_neg h, Curve.BCSquare.divMapCoeff, dif_neg hT]

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry in
universe u in
theorem divMap_comp {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    {F' : Type u} [Field F'] [Algebra F F'] [Algebra k F'] [IsScalarTower k F F']
    {C : Curve k} {C' : Curve F} {C'' : Curve F'} (S : Curve.BCSquare C C')
    (T : Curve.BCSquare C' C'') :
    (S.comp T).divMap = T.divMap.comp S.divMap := by
  apply AddMonoidHom.ext
  intro D
  ext Q''
  rw [AddMonoidHom.comp_apply, Curve.BCSquare.divMap_apply, Curve.BCSquare.divMap_apply]
  exact divMapCoeff_comp S T D Q''

end Work.CurveBasics.Curve.BCSquare
