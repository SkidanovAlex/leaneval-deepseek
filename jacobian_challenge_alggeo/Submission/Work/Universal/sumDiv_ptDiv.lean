/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The sum of `f` over the point divisor `[x]` is `f x`

For a curve `C` over a field `K`, a chart datum `D : GroupChunk.Input C P0`, a group object `A`
over `K` and a morphism `f : C ⟶ A`, the sum `Σ f([x])` of `f` over the divisor of a single
point `x : C(F)` is `f(x)`.

`sumDiv D f E hE n hn` is, by definition, the value of the sum morphism
`sumMap D f n : Symⁿ C ⟶ A` at the point of `Symⁿ C` classified by `E`.  For `E = [x]` and
`n = 1` this point is `x ≫ curveIso` (the interface field `GroupChunk.Input.curveIso_divOf`), and
the composite

  `C --curveIso--> Sym¹ C --sumMap f 1--> A`

is `f`: this is the `n = 1` case of "`Σᵐ f` is the sum of `f` over the points".  The proof goes
through the other description of `curveIso`, namely the quotient map `quotMap D 1 : C¹ ⟶ Sym¹ C`
precomposed with the canonical identification `C ≅ C¹` (`Pi.lift (fun _ => 𝟙)`); the two
morphisms `C ⟶ Sym¹ C` agree on points because both have divisor `[x]` (`divOf_injective`), and
the quotient map is the `1`-fold sum of the universal family by definition of `sumMap`
(`sumMap_spec`).

This file needs only the interface `Work.Universal.Basic`; it deliberately does not use the
companion lemma `Work.Universal.curveIso_sumMap` (the statement for all `f`, which needs an
equality of *morphisms* `curveIso ≫ sumMap f 1 = f`), because for a single point the pointwise
form of the same identity suffices.
-/
import Mathlib
import Submission.Work.Universal.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.



open CategoryTheory Limits
open scoped Classical MonObj

namespace Work.Universal

theorem sumDiv_ptDiv {K : Type _} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : Work.AbVar.Point C.toOver} [Work.SpecLin.DivBase C]
    (D : Work.GroupChunk.Input C P0) [Work.Universal.SymQuotData C P0 D]
    {A : Work.GCBasics.Sch K} [CategoryTheory.GrpObj A] [CategoryTheory.IsCommMonObj A]
    (f : C.toOver ⟶ A) {F : Type _} [Field F] [Algebra K F]
    (x : Work.GCBasics.FPt C.toOver F) :
    Work.Universal.sumDiv D f (Work.SpecLin.ptDiv x) (Work.SpecLin.ptDiv_isEffective x) 1
      (Work.SpecLin.Points.ptDiv_deg x) = CategoryTheory.CategoryStruct.comp x f := by
  classical
  -- `sumDiv` is `sumMap` at the point of `Sym¹ C` whose divisor is `[x]`.
  rw [sumDiv_eq_of_divOf D f (Work.SpecLin.ptDiv_isEffective x)
    (Work.SpecLin.Points.ptDiv_deg x) (D.curveIso_divOf x)]
  -- That point is also `x ≫ powMap 𝟙`, where `powMap 𝟙 : C ⟶ Sym¹ C` is the point divisor map:
  -- both morphisms have divisor `[x]`, and a point of `Sym¹ C` is determined by its divisor.
  have hx : x ≫ (D.symGeom 1).powMap (fun _ : Fin 1 => 𝟙 C.toOver) = x ≫ D.curveIso := by
    refine (D.symGeom 1).divOf_injective _ _ ?_
    have hcomp : x ≫ (D.symGeom 1).powMap (fun _ : Fin 1 => 𝟙 C.toOver)
        = (D.symGeom 1).powMap (fun _ : Fin 1 => x) := by
      simpa only [Category.comp_id] using
        ((D.symGeom 1).powMap_comp x (fun _ : Fin 1 => 𝟙 C.toOver)).symm
    rw [hcomp, (D.symGeom 1).divOf_powMap (fun _ : Fin 1 => x), D.curveIso_divOf x]
    exact Fin.sum_univ_one (fun _ : Fin 1 => Work.SpecLin.ptDiv x)
  -- `powMap 𝟙` is the quotient map `quotMap D 1` precomposed with the canonical iso `C ≅ C¹`,
  -- so composing it with `sumMap D f 1` computes the `1`-fold sum of `f`, which is `f`.
  have hpow : (D.symGeom 1).powMap (fun _ : Fin 1 => 𝟙 C.toOver) ≫ sumMap D f 1 = f := by
    have hlift : Limits.Pi.lift (fun _ : Fin 1 => 𝟙 C.toOver) ≫ quotMap D 1
        = (D.symGeom 1).powMap (fun _ : Fin 1 => 𝟙 C.toOver) := by
      show Limits.Pi.lift (fun _ : Fin 1 => 𝟙 C.toOver)
          ≫ (D.symGeom 1).powMap (fun m => proj C 1 m) = _
      simpa only [Pi.lift_comp_π] using
        ((D.symGeom 1).powMap_comp (Limits.Pi.lift (fun _ : Fin 1 => 𝟙 C.toOver))
          (fun m => proj C 1 m)).symm
    calc (D.symGeom 1).powMap (fun _ : Fin 1 => 𝟙 C.toOver) ≫ sumMap D f 1
        = Limits.Pi.lift (fun _ : Fin 1 => 𝟙 C.toOver) ≫ (quotMap D 1 ≫ sumMap D f 1) := by
          rw [← hlift, Category.assoc]
      _ = Limits.Pi.lift (fun _ : Fin 1 => 𝟙 C.toOver) ≫ sumTerm C f 1 := by rw [sumMap_spec]
      _ = f := by
          rw [sumTerm, comp_prod, Fin.prod_univ_one]
          simp only [← Category.assoc, Pi.lift_comp_π, Category.id_comp]
  rw [← hx, Category.assoc, hpow]

end Work.Universal
