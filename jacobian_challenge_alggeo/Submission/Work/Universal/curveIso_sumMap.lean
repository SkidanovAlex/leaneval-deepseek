import Mathlib
import Submission.Work.Universal.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# `curveIso ≫ Σ¹ f = f`

The identification `Sym¹ C = C` (`GroupChunk.Input.curveIso`) is characterised by its values at
field points (`GroupChunk.Input.curveIso_divOf`).  Since `C` is reduced and `Sym¹ C` is separated
over `K`, a morphism out of `C` is determined by its values at the residue-field points
(`GCBasics.hom_ext_of_resPt`), so `curveIso` is the canonical composite
`C ≅ C¹ ⟶ Sym¹ C` given by `powMap` (`curveIso_eq_powMap`).

Composing with the sum morphism `Σ¹ f = sumMap D f 1` then gives `f`: this is the case `n = 1`
of the general computation `powMap x ≫ sumMap D f n = ∏ m, (x m ≫ f)`
(`sumMap_powMap_gen`), which follows from `SymGeom.powMap_comp` (naturality of `powMap`) and the
defining property of `sumMap` (`sumMap_spec`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical MonObj
open scoped Work.GCBasics
open Work.GCBasics Work.GroupChunk

universe u

namespace Work.Universal

noncomputable section

variable {K : Type u} [Field K]
variable {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver} [SpecLin.DivBase C]

/-- The canonical identification `C ⟶ Sym¹ C`: the `1`-fold sum of the identity, i.e. the
composite `C ≅ C¹ ⟶ Sym¹ C` of the inverse of the projection `C¹ ⟶ C` with the quotient map. -/
def curveIsoPow (D : GroupChunk.Input C P0) : C.toOver ⟶ D.Sym 1 :=
  (D.symGeom 1).powMap (fun _ : Fin 1 => 𝟙 C.toOver)

/-- **`curveIso` is the canonical identification `C ⟶ Sym¹ C`.**  Both morphisms have the same
divisor at every field point (`GroupChunk.Input.curveIso_divOf` and `SymGeom.divOf_powMap`), and
they are morphisms out of the reduced scheme `C` into the separated scheme `Sym¹ C`, hence are
detected by their values at residue-field points (`GCBasics.hom_ext_of_resPt`). -/
theorem curveIso_eq_powMap (D : GroupChunk.Input C P0) :
    D.curveIso = curveIsoPow D := by
  haveI : IsProper ((D.symGeom 1).S).hom := (D.symGeom 1).isProper
  apply GCBasics.hom_ext_of_resPt (K := K) (X := C.toOver) (Y := D.Sym 1)
  intro x
  letI : Algebra K (GCBasics.resField C.toOver x) := GCBasics.resFieldAlgebra C.toOver x
  refine (D.symGeom 1).divOf_injective _ _ ?_
  have h1 : (D.symGeom 1).divOf (GCBasics.resPt C.toOver x ≫ D.curveIso)
      = SpecLin.ptDiv (GCBasics.resPt C.toOver x) := D.curveIso_divOf _
  have h2 : (D.symGeom 1).divOf (GCBasics.resPt C.toOver x ≫ curveIsoPow D)
      = SpecLin.ptDiv (GCBasics.resPt C.toOver x) := by
    have hcomp : GCBasics.resPt C.toOver x ≫ curveIsoPow D
        = (D.symGeom 1).powMap (fun _ : Fin 1 => GCBasics.resPt C.toOver x) := by
      unfold curveIsoPow
      rw [← (D.symGeom 1).powMap_comp (GCBasics.resPt C.toOver x)
        (fun _ : Fin 1 => 𝟙 C.toOver)]
      simp only [Category.comp_id]
    rw [hcomp, (D.symGeom 1).divOf_powMap]
    rw [Fin.sum_univ_one]
  exact h1.trans h2.symm

/-- **The sum morphism tested at `n` points.**  For any family `x : Fin n → (T ⟶ C)` of points
of `C` parametrised by a `K`-scheme `T`, the composite of `Σᵐ f : Symⁿ C ⟶ A` with the `n`-fold
sum `powMap x` is the sum `∏ m, (x m ≫ f)` of the images of the `x m` in the commutative group
object `A`.

This is the computation `Pi.lift x ≫ quotMap ≫ Σᵐ f = Pi.lift x ≫ Σ_m (pr_m ≫ f)`, using the
naturality of `powMap` in the parameter scheme. -/
theorem sumMap_powMap_gen (D : GroupChunk.Input C P0) [SymQuotData C P0 D]
    {A : Sch K} [GrpObj A] [IsCommMonObj A] (f : C.toOver ⟶ A) (n : ℕ) {T : Sch K}
    (x : Fin n → (T ⟶ C.toOver)) :
    (D.symGeom n).powMap x ≫ sumMap D f n = prodHom (A := A) (X := T) (fun m => x m ≫ f) := by
  have hlift : ∀ {T' : Sch K} (y : Fin n → (T' ⟶ C.toOver)),
      (D.symGeom n).powMap y = Limits.Pi.lift y ≫ quotMap D n := by
    intro T' y
    have h1 : y = (fun m => Limits.Pi.lift y ≫ SymQuot.proj C.toOver n m) :=
      funext (fun m => (Limits.Pi.lift_comp_π (f := fun _ : Fin n => C.toOver) y m).symm)
    calc (D.symGeom n).powMap y
        = (D.symGeom n).powMap (fun m => Limits.Pi.lift y ≫ SymQuot.proj C.toOver n m) :=
          congrArg (fun z : Fin n → (T' ⟶ C.toOver) => (D.symGeom n).powMap z) h1
      _ = Limits.Pi.lift y ≫ (D.symGeom n).powMap (fun m => SymQuot.proj C.toOver n m) :=
          (D.symGeom n).powMap_comp (Limits.Pi.lift y) (fun m => SymQuot.proj C.toOver n m)
      _ = Limits.Pi.lift y ≫ quotMap D n := rfl
  rw [hlift x, Category.assoc, sumMap_spec]
  simp only [sumTerm, prodHom]
  rw [comp_prod]
  refine Finset.prod_congr rfl (fun m _ => ?_)
  rw [← Category.assoc, Limits.Pi.lift_comp_π]

/-- **The case `n = 1`**: `Σ¹ f` composed with the canonical identification `C ⟶ Sym¹ C` is
`f`. -/
theorem curveIsoPow_sumMap (D : GroupChunk.Input C P0) [SymQuotData C P0 D]
    {A : Sch K} [GrpObj A] [IsCommMonObj A] (f : C.toOver ⟶ A) :
    curveIsoPow D ≫ sumMap D f 1 = f := by
  unfold curveIsoPow
  rw [sumMap_powMap_gen D f 1 (fun _ : Fin 1 => 𝟙 C.toOver)]
  simp only [prodHom]
  rw [show (fun m : Fin 1 => 𝟙 C.toOver ≫ f) = (fun _ : Fin 1 => f) from
    funext (fun m => by rw [Category.id_comp])]
  rw [Fin.prod_univ_one]

theorem curveIso_sumMap {K : Type _} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : Work.AbVar.Point C.toOver} [Work.SpecLin.DivBase C]
    (D : Work.GroupChunk.Input C P0) [Work.Universal.SymQuotData C P0 D]
    {A : Work.GCBasics.Sch K} [CategoryTheory.GrpObj A] [CategoryTheory.IsCommMonObj A]
    (f : C.toOver ⟶ A) :
    CategoryTheory.CategoryStruct.comp D.curveIso (Work.Universal.sumMap D f 1) = f := by
  rw [curveIso_eq_powMap D]
  exact curveIsoPow_sumMap D f

end

end Work.Universal
