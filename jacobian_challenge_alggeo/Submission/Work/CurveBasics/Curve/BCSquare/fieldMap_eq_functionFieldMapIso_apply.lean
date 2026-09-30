/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The projection of a base-change square induces the field map

For a curve `C` over `k`, a field extension `F/k` and a base-change square

```
C'  ⟶  C
↓      ↓
Spec F ⟶ Spec k
```

the canonical isomorphism `isoBaseChange S : C' ⟶ C_F` of the square with the tautological
square `bcSquare C F` identifies the function fields `K(C')` and `K(C_F)`.  This file shows
that under this identification the map `K(C) ⟶ K(C')` induced by the projection `S.π` (the
`fieldMap` of the square) is exactly the base-change map `functionFieldMap C F : K(C) ⟶ K(C_F)`
followed by the isomorphism on function fields:

`(functionFieldMapIso (isoBaseChange S)).hom ((C.functionFieldMap F).hom x) = S.fieldMap.hom x`.

The proof is by reduction to the germs of sections (via `exists_germ_eq`): on a germ the three
maps are described by `germToFunctionField_baseChangeFst_app`,
`functionFieldMapIso_germToFunctionField` and `fieldMap_germToFunctionField`, and the two
resulting germs agree because the projections of the two cartesian squares agree
(`isoBaseChange_hom_fst`).
-/
import Mathlib
import Submission.Work.CurveBasics.Curve.BCSquare.GermNaturality
import Submission.Work.CurveBasics.BaseChangeFunctionField
import Submission.Work.CurveBasics.BaseChange.range_germ_baseChange
import Submission.Work.CurveBasics.Curve.BCSquare.ordAt_fieldMap_of_not_isClosed

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.CurveBasics.Curve.BCSquare

universe u

/-- The germ of a section at the generic point is unchanged if the proof that the generic point
lies in the open set is replaced by another one. -/
theorem germ_genericPoint_eq_germToFunctionField {X : Scheme.{u}} [IrreducibleSpace X]
    (U : X.Opens) [Nonempty U] (hU : genericPoint X ∈ U) (s : Γ(X, U)) :
    X.presheaf.germ U (genericPoint X) hU s = X.germToFunctionField U s := by
  simp only [Scheme.germToFunctionField]

/-- Two morphisms `k l : X ⟶ Y` with `k = l` induce the same map on the germ of a section at
the generic point of the (irreducible) scheme `X`. -/
theorem germToFunctionField_congr_hom {X Y : Scheme.{u}} [IrreducibleSpace X] {k l : X ⟶ Y}
    (hk : k = l) (U : Y.Opens) [Nonempty (k ⁻¹ᵁ U)] [Nonempty (l ⁻¹ᵁ U)] (s : Γ(Y, U)) :
    X.germToFunctionField (k ⁻¹ᵁ U) (k.app U s) = X.germToFunctionField (l ⁻¹ᵁ U) (l.app U s) := by
  cases hk
  congr 1

/-- The map on function fields induced by the projection of a base-change square is the
base-change map followed by the identification of the square with the tautological
base change. -/
theorem fieldMap_eq_functionFieldMapIso_apply {k : Type u} [Field k] {F : Type u} [Field F]
    [Algebra k F] {C : Curve k} {C' : Curve F} (S : Curve.BCSquare C C')
    (x : C.functionField) :
    (functionFieldMapIso (isoBaseChange S)).hom ((C.functionFieldMap F).hom x) = S.fieldMap.hom x := by
  -- write `x` as the germ of a section over an open set containing the generic point of `C`
  obtain ⟨U, hU, s, hs⟩ := C.left.presheaf.exists_germ_eq x
  haveI hUne : Nonempty U := ⟨⟨genericPoint C.left, hU⟩⟩
  have hgerm : C.left.presheaf.germ U (genericPoint C.left) hU s = C.germToFunctionField U s :=
    germ_genericPoint_eq_germToFunctionField U hU s
  -- non-emptiness of the open sets at which the germs below are taken
  haveI hbc : Nonempty (C.bcOpens F U) := inferInstance
  haveI hpre : Nonempty ((isoBaseChange S).hom ⁻¹ᵁ (C.bcOpens F U)) :=
    nonempty_preimage_of_genericPoint (isoBaseChange S).hom (iso_genericPoint (isoBaseChange S))
      (C.bcOpens F U)
  haveI hSπ : Nonempty (S.π ⁻¹ᵁ U) := inferInstance
  haveI hcomp : Nonempty (((isoBaseChange S).hom ≫ Curve.baseChangeFst C F) ⁻¹ᵁ U) := hpre
  -- on this germ all three maps are described by their compatibility with germs
  rw [← hs, hgerm, ← BaseChange.germToFunctionField_baseChangeFst_app C F U s,
    functionFieldMapIso_germToFunctionField (isoBaseChange S) (C.bcOpens F U)
      ((C.baseChangeFst F).app U s),
    fieldMap_germToFunctionField_apply S U s]
  -- the two squares have the same projection
  exact germToFunctionField_congr_hom (isoBaseChange_hom_fst S) U s

end Work.CurveBasics.Curve.BCSquare
