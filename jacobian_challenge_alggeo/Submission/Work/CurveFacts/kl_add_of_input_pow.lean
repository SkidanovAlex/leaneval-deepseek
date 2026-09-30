import Mathlib
import Submission.Work.CurveFacts.AddCompat
import Submission.Work.CurveFacts.kl_add_of_input
import Submission.Work.GroupChunk.landsIn_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.CurveFacts

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical MonObj
open scoped Work.GCBasics

noncomputable section

/-- **The `powMap`-level compatibility implies the field-point compatibility** (local version).

This is the local form of the upgrade `Work.CurveFacts.isAddSumMap_of_isAddSumMapPow` needed by
`Work.CurveFacts.kl_add_of_input_pow`.  The proof is a base-change-to-the-algebraic-closure
argument.

Let `p : FPt (Sym^m C) F` and `q : FPt (Sym^n C) F` be field points, and put `L := F̄` and
`e := (F →ₐ[K] F̄)`.  Since `Spec F̄ ⟶ Spec F` is an epimorphism, the base-changed points
`RPt.map e ·` separate points (`Work.GroupChunk.smap_injective`), so it suffices to check the
identity after base change to `L`.  There, the divisors `divOf (RPt.map e p)` and
`divOf (RPt.map e q)`, being effective of degrees `m` and `n` over the algebraically closed field
`L`, split into points `x : Fin m → CurveFPt C L` and `y : Fin n → CurveFPt C L`
(`Work.SpecLin.SymGeom.split`, using `SymGeom.divOf_map`); consequently
`RPt.map e p = powMap x` and `RPt.map e q = powMap y` by `SymGeom.divOf_powMap` and
`SymGeom.divOf_injective`.  The base-changed identity is then exactly the hypothesis
`IsAddSumMapPow` evaluated at `T := Spec L`, `x`, `y`. -/
theorem isAddSumMap_of_isAddSumMapPow' {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : 𝟙_ (Work.GCBasics.Sch K) ⟶ C.toOver} [Work.SpecLin.DivBase C]
    (D : Work.GroupChunk.Input C P0) [Work.Universal.SymQuotData C P0 D]
    {A : Work.GCBasics.Sch K} [GrpObj A] [IsCommMonObj A] (f : C.toOver ⟶ A)
    (h : Work.CurveFacts.IsAddSumMapPow D f) (m n : ℕ) :
    Work.CurveFacts.IsAddSumMap D f m n := by
  intro F _ _ p q
  let L := AlgebraicClosure F
  let e : F →ₐ[K] L := IsScalarTower.toAlgHom K F L
  refine Work.GroupChunk.smap_injective (X := A) e _ _ ?_
  have hL : Work.GCBasics.RPt.map e
        ((CartesianMonoidalCategory.lift p q ≫ D.addMap m n) ≫ Work.Universal.sumMap D f (m + n))
      = (CartesianMonoidalCategory.lift (Work.GCBasics.RPt.map e p) (Work.GCBasics.RPt.map e q)
            ≫ D.addMap m n) ≫ Work.Universal.sumMap D f (m + n) := by
    simp only [Work.GCBasics.RPt.map]
    rw [← Category.assoc, ← Category.assoc, CartesianMonoidalCategory.comp_lift]
  have hR : Work.GCBasics.RPt.map e
        ((p ≫ Work.Universal.sumMap D f m) * (q ≫ Work.Universal.sumMap D f n))
      = (Work.GCBasics.RPt.map e p ≫ Work.Universal.sumMap D f m)
          * (Work.GCBasics.RPt.map e q ≫ Work.Universal.sumMap D f n) := by
    simp only [Work.GCBasics.RPt.map]
    rw [MonObj.comp_mul]
    simp only [Category.assoc]
  rw [hL, hR]
  obtain ⟨x, hx⟩ := (D.symGeom m).split (F := F) (F' := L)
      ((D.symGeom m).divOf p) ((D.symGeom m).divOf_isEffective p) ((D.symGeom m).divOf_deg p)
  obtain ⟨y, hy⟩ := (D.symGeom n).split (F := F) (F' := L)
      ((D.symGeom n).divOf q) ((D.symGeom n).divOf_isEffective q) ((D.symGeom n).divOf_deg q)
  have hp' : Work.GCBasics.RPt.map e p = (D.symGeom m).powMap x := by
    apply (D.symGeom m).divOf_injective
    rw [show (D.symGeom m).divOf (Work.GCBasics.RPt.map e p)
          = Work.SpecLin.DivBase.bc e ((D.symGeom m).divOf p) from (D.symGeom m).divOf_map e p,
      hx, (D.symGeom m).divOf_powMap x]
  have hq' : Work.GCBasics.RPt.map e q = (D.symGeom n).powMap y := by
    apply (D.symGeom n).divOf_injective
    rw [show (D.symGeom n).divOf (Work.GCBasics.RPt.map e q)
          = Work.SpecLin.DivBase.bc e ((D.symGeom n).divOf q) from (D.symGeom n).divOf_map e q,
      hy, (D.symGeom n).divOf_powMap y]
  rw [hp', hq']
  exact h m n x y

end

/-- **Item A6, additivity with the minimal hypothesis.**  Same conclusion as
`Work.CurveFacts.kl_add_of_input` (namely the type of the field `kl_add` of
`Work.Universal.Input`), but with the hypothesis weakened from the field-point compatibility
`Work.CurveFacts.IsAddSumMap` to the `powMap`-level compatibility
`Work.CurveFacts.IsAddSumMapPow` -- which is the datum area `SY` actually provides, as
`Work.SymQuot.addMap_spec` (a fully proved instance of it is
`Work.CurveFacts.symSumMap_addMap` for the concrete symmetric powers).

Proof: `Work.CurveFacts.isAddSumMap_of_isAddSumMapPow` turns `hadd` into
`Work.CurveFacts.IsAddSumMap D f m n`, and `Work.CurveFacts.kl_add_of_input` then applies to it.
Explicitly:
`exact Work.CurveFacts.kl_add_of_input D (fun {A} _ _ f m n => isAddSumMap_of_isAddSumMapPow D f (hadd f) m n)`. -/
theorem kl_add_of_input_pow {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : 𝟙_ (Work.GCBasics.Sch K) ⟶ C.toOver} [Work.SpecLin.DivBase C]
    (D : Work.GroupChunk.Input C P0) [Work.Universal.SymQuotData C P0 D]
    (hadd : ∀ {A : Work.GCBasics.Sch K} [GrpObj A] [IsCommMonObj A] (f : C.toOver ⟶ A),
      Work.CurveFacts.IsAddSumMapPow D f) :
    ∀ {A : Work.GCBasics.Sch K} [GrpObj A] [IsCommMonObj A] (f : C.toOver ⟶ A) {F : Type u}
      [Field F] [Algebra K F] (E E' : Work.GCBasics.Dv C F) (hE : E.IsEffective)
      (hE' : E'.IsEffective) (n m : ℕ) (hn : Work.GCBasics.Ddeg C F E = (n : ℤ))
      (hm : Work.GCBasics.Ddeg C F E' = (m : ℤ)) (hEE' : (E + E').IsEffective),
      Work.Universal.sumDiv D f (E + E') hEE' (n + m) (Work.Universal.ddeg_add hn hm) =
        Work.Universal.sumDiv D f E hE n hn * Work.Universal.sumDiv D f E' hE' m hm := by
  exact Work.CurveFacts.kl_add_of_input D
    (fun {A} _ _ f m n => isAddSumMap_of_isAddSumMapPow' D f (hadd f) m n)

end Work.CurveFacts
