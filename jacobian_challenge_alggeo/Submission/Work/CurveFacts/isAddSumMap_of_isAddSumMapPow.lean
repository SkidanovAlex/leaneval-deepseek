import Mathlib
import Submission.Work.CurveFacts.AddCompat
import Submission.Work.Universal.Basic
import Submission.Work.SymQuot.SymGeomInst
import Submission.Work.SymQuot.DivBaseInst
import Submission.Work.GroupChunk.landsIn_aux
import Submission.Work.SymQuot.CurveInstance

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

open Work.GCBasics

/-! ## Point-level plumbing for `RPt.map`

The three lemmas below are the only facts about `Work.GCBasics.RPt.map` used in the proof: it is
natural in the point (`rPt_map_comp'`), it commutes with the product pairing (`rPt_map_lift`), and
hence with the group law of points of a group object (`rPt_map_mul`). -/

/-- `RPt.map e` is natural with respect to composition of the point with a morphism. -/
theorem rPt_map_comp' {K : Type u} [Field K] {X Y : Sch K} {F F' : Type u}
    [Field F] [Field F'] [Algebra K F] [Algebra K F'] (e : F →ₐ[K] F') (p : FPt X F)
    (u : X ⟶ Y) : RPt.map e (p ≫ u) = RPt.map e p ≫ u := by
  simp only [RPt.map, Category.assoc]

/-- `RPt.map e` commutes with the cartesian pairing of points. -/
theorem rPt_map_lift {K : Type u} [Field K] {X Y : Sch K} {F F' : Type u}
    [Field F] [Field F'] [Algebra K F] [Algebra K F'] (e : F →ₐ[K] F')
    (p : FPt X F) (q : FPt Y F) :
    RPt.map e (CartesianMonoidalCategory.lift p q) =
      CartesianMonoidalCategory.lift (RPt.map e p) (RPt.map e q) := by
  simp only [RPt.map]
  rw [CartesianMonoidalCategory.comp_lift]

/-- `RPt.map e` preserves the group law on points of a commutative group object. -/
theorem rPt_map_mul {K : Type u} [Field K] {A : Sch K} [CategoryTheory.GrpObj A]
    [CategoryTheory.IsCommMonObj A] {F F' : Type u} [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] (e : F →ₐ[K] F') (X Y : FPt A F) :
    RPt.map e (X * Y) = RPt.map e X * RPt.map e Y := by
  simp only [RPt.map]
  rw [MonObj.comp_mul]


/-- **The `powMap`-level compatibility implies the field-point compatibility.**  If the addition of
symmetric powers is compatible with the sum morphism on points of the form `powMap x`
(`Work.CurveFacts.IsAddSumMapPow`, `Submission/Work/CurveFacts/AddCompat.lean`), then it is
compatible with it on all field points (`Work.CurveFacts.IsAddSumMap`).  This upgrade is what makes
the `powMap`-level datum -- which is what area `SY` actually provides, as
`Work.SymQuot.addMap_spec` -- sufficient for the additivity `Work.CurveFacts.kl_add_of_input`.

Route.  Let `p : FPt (D.Sym m) F` and `q : FPt (D.Sym n) F`.  Pass to `L := AlgebraicClosure F`
(an algebraically closed `F`-algebra, hence a `K`-algebra with `IsScalarTower K F L`), and set
`p' := RPt.map (IsScalarTower.toAlgHom K F L) p`, `q' := ... q`.  By `SymGeom.split` the divisors
`DivBase.bc e (divOf p)` and `DivBase.bc e (divOf q)` split into points `x : Fin m → CurveFPt C L`
and `y : Fin n → CurveFPt C L`; then `divOf p' = ∑ i, ptDiv (x i)` by `SymGeom.divOf_map`, so
`p' = (D.symGeom m).powMap x` by `SymGeom.divOf_injective` and `SymGeom.divOf_powMap`, and
similarly `q' = (D.symGeom n).powMap y`.  Now `IsAddSumMapPow D f m n` at `T := specOf K L` with
`x`, `y` gives the identity after base change, i.e.
`RPt.map e ((lift p q) ≫ Φ) = RPt.map e ((lift p q) ≫ Ψ)` where `Φ := D.addMap m n ≫ sumMap D f (m+n)`
and `Ψ := (sumMap D f m ⊗ sumMap D f n) ≫ μ`; here one uses
`CartesianMonoidalCategory.lift (RPt.map e p) (RPt.map e q) = RPt.map e (lift p q)`.  Finally
descent is `Work.GroupChunk.smap_injective` (`Submission/Work/GroupChunk/landsIn_aux.lean`), which
is the injectivity of `RPt.map e` on points. -/
theorem isAddSumMap_of_isAddSumMapPow {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : 𝟙_ (Work.GCBasics.Sch K) ⟶ C.toOver} [Work.SpecLin.DivBase C]
    (D : Work.GroupChunk.Input C P0) [Work.Universal.SymQuotData C P0 D]
    {A : Work.GCBasics.Sch K} [GrpObj A] [IsCommMonObj A] (f : C.toOver ⟶ A)
    (h : Work.CurveFacts.IsAddSumMapPow D f) (m n : ℕ) :
    Work.CurveFacts.IsAddSumMap D f m n := by
  -- Pass to an algebraic closure `L` of `F`, so that the divisors can be split into points.
  intro F _ _ p q
  set e : F →ₐ[K] AlgebraicClosure F := IsScalarTower.toAlgHom K F (AlgebraicClosure F) with he
  obtain ⟨x, hx⟩ := (D.symGeom m).split (F' := AlgebraicClosure F) ((D.symGeom m).divOf p)
      ((D.symGeom m).divOf_isEffective p) ((D.symGeom m).divOf_deg p)
  obtain ⟨y, hy⟩ := (D.symGeom n).split (F' := AlgebraicClosure F) ((D.symGeom n).divOf q)
      ((D.symGeom n).divOf_isEffective q) ((D.symGeom n).divOf_deg q)
  rw [← he] at hx hy
  -- The base change of `p` (resp. `q`) to `L` is the `powMap` of the split points.
  have hp : RPt.map e p = (D.symGeom m).powMap x :=
    (D.symGeom m).divOf_injective (Work.SpecLin.RPt.map e p) ((D.symGeom m).powMap x) (by
      rw [(D.symGeom m).divOf_map e p, hx, (D.symGeom m).divOf_powMap])
  have hq : RPt.map e q = (D.symGeom n).powMap y :=
    (D.symGeom n).divOf_injective (Work.SpecLin.RPt.map e q) ((D.symGeom n).powMap y) (by
      rw [(D.symGeom n).divOf_map e q, hy, (D.symGeom n).divOf_powMap])
  -- It suffices to check the identity after base change to `L`, where it is `h` at `x`, `y`.
  apply Work.GroupChunk.smap_injective e
  rw [show RPt.map e ((lift p q ≫ D.addMap m n) ≫ Work.Universal.sumMap D f (m+n))
        = ((lift (RPt.map e p) (RPt.map e q) ≫ D.addMap m n) ≫ Work.Universal.sumMap D f (m+n))
      from by rw [rPt_map_comp', rPt_map_comp', rPt_map_lift]]
  rw [show RPt.map e ((p ≫ Work.Universal.sumMap D f m) * (q ≫ Work.Universal.sumMap D f n))
        = (RPt.map e p ≫ Work.Universal.sumMap D f m) * (RPt.map e q ≫ Work.Universal.sumMap D f n)
      from by rw [rPt_map_mul, rPt_map_comp', rPt_map_comp']]
  rw [hp, hq]
  exact h m n x y

end Work.CurveFacts
