import Mathlib
import Submission.Work.SymQuot.AddMap
import Submission.Work.SymQuot.SymGeomInst
import Submission.Work.SymQuot.DivOf.Complete.divOf_complete

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonoidalCategory

universe u

namespace Work.SymQuot.OfDiv

/-- Base change of points `RPt.map` commutes with postcomposition. -/
theorem RPt_map_comp_assoc {K : Type u} [Field K] {F F' : Type u} [Field F] [Field F']
    [Algebra K F] [Algebra K F'] {X Y : Work.SpecLin.Sch K} (e : F →ₐ[K] F')
    (q : Work.SpecLin.FPt X F) (g : X ⟶ Y) :
    Work.SpecLin.RPt.map e (q ≫ g) = Work.SpecLin.RPt.map e q ≫ g := by
  simp only [Work.SpecLin.RPt.map, Category.assoc]

open CategoryTheory Limits AlgebraicGeometry in
open scoped MonoidalCategory in
theorem addMap_divOf {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    [Work.SymQuot.CurveAffineCover C] {m n : ℕ} [NeZero m] [NeZero n]
    {X : Work.SpecLin.Sch K} (u : X ⟶ Work.SymQuot.Sym C m) (v : X ⟶ Work.SymQuot.Sym C n)
    {F : Type u} [Field F] [Algebra K F] (p : Work.SpecLin.FPt X F) :
    Work.SymQuot.DivOf.divOf F
        ((p ≫ CartesianMonoidalCategory.liftEquiv (u, v)) ≫ Work.SymQuot.addMap C m n)
      = Work.SymQuot.DivOf.divOf F (p ≫ u) + Work.SymQuot.DivOf.divOf F (p ≫ v) := by
  classical
  -- The point of `Sym^{m+n} C` whose divisor we compute.
  set w : Work.SpecLin.FPt (Work.SymQuot.Sym C (m + n)) F :=
    (p ≫ CartesianMonoidalCategory.liftEquiv (u, v)) ≫ Work.SymQuot.addMap C m n with hwdef
  -- The expected divisor: effective of degree `m + n`.
  set D : Work.SpecLin.Dv C F :=
    Work.SymQuot.DivOf.divOf F (p ≫ u) + Work.SymQuot.DivOf.divOf F (p ≫ v) with hDdef
  have hDeff : Work.CurveBasics.Curve.Div.IsEffective D := by
    rw [hDdef]
    exact Work.CurveBasics.Curve.Div.IsEffective.add
      (Work.SymQuot.DivOf.divOf_isEffective (p ≫ u))
      (Work.SymQuot.DivOf.divOf_isEffective (p ≫ v))
  have hDdeg : (C.baseChange F).deg D = ((m + n : ℕ) : ℤ) := by
    rw [hDdef, Work.CurveBasics.Curve.deg_add,
      Work.SymQuot.DivOf.divOf_deg (C := C) (n := m) (p ≫ u),
      Work.SymQuot.DivOf.divOf_deg (C := C) (n := n) (p ≫ v)]
    push_cast
    ring
  -- A point of `Sym^{m+n} C` with divisor `D`.
  obtain ⟨w', hw'⟩ :=
    Work.SymQuot.DivOf.Complete.divOf_complete (C := C) (n := m + n) D hDeff hDdeg
  -- Pass to an algebraic closure of `F`, where both points split into points of `C`.
  let e : F →ₐ[K] AlgebraicClosure F := IsScalarTower.toAlgHom K F (AlgebraicClosure F)
  obtain ⟨x, hx⟩ := Work.SymQuot.Sym.exists_powMap_eq (K := K) C m
    (Work.SpecLin.RPt.map e (p ≫ u))
  obtain ⟨y, hy⟩ := Work.SymQuot.Sym.exists_powMap_eq (K := K) C n
    (Work.SpecLin.RPt.map e (p ≫ v))
  -- Over the algebraic closure, `w` is the sum of the two splittings.
  have hprod :
      Work.SpecLin.RPt.map e p ≫ CartesianMonoidalCategory.liftEquiv (u, v) =
        CartesianMonoidalCategory.lift (Work.SymQuot.Sym.powMap C m x)
          (Work.SymQuot.Sym.powMap C n y) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, CartesianMonoidalCategory.liftEquiv_apply,
        CartesianMonoidalCategory.lift_fst]
      rw [← RPt_map_comp_assoc, ← hx]
    · simp only [Category.assoc, CartesianMonoidalCategory.liftEquiv_apply,
        CartesianMonoidalCategory.lift_snd]
      rw [← RPt_map_comp_assoc, ← hy]
  have hwL : Work.SpecLin.RPt.map e w =
      Work.SymQuot.Sym.powMap C (m + n) (Fin.append x y) := by
    rw [hwdef]
    rw [RPt_map_comp_assoc (X := Work.SymQuot.Sym C m ⊗ Work.SymQuot.Sym C n)
      (Y := Work.SymQuot.Sym C (m + n)) e
      (p ≫ CartesianMonoidalCategory.liftEquiv (u, v)) (Work.SymQuot.addMap C m n)]
    rw [RPt_map_comp_assoc (X := X) (Y := Work.SymQuot.Sym C m ⊗ Work.SymQuot.Sym C n) e p
      (CartesianMonoidalCategory.liftEquiv (u, v))]
    rw [hprod, Work.SymQuot.addMap_spec]
  -- The divisors of the two base-changed points agree.
  have hdiv_w : Work.SymQuot.DivOf.divOf (AlgebraicClosure F) (Work.SpecLin.RPt.map e w) =
      ∑ i : Fin (m + n), Work.SpecLin.ptDiv ((Fin.append x y) i) := by
    rw [hwL]
    exact Work.SymQuot.DivOf.divOf_powMapC1 (Fin.append x y)
  have hdiv_w' : Work.SymQuot.DivOf.divOf (AlgebraicClosure F) (Work.SpecLin.RPt.map e w') =
      ∑ i : Fin (m + n), Work.SpecLin.ptDiv ((Fin.append x y) i) := by
    calc Work.SymQuot.DivOf.divOf (AlgebraicClosure F) (Work.SpecLin.RPt.map e w')
        = Work.SpecLin.DivBase.bc e (Work.SymQuot.DivOf.divOf F w') :=
          Work.SymQuot.DivOf.divOf_map e w'
      _ = Work.SpecLin.DivBase.bc e D := by rw [hw']
      _ = Work.SpecLin.DivBase.bc e (Work.SymQuot.DivOf.divOf F (p ≫ u)) +
            Work.SpecLin.DivBase.bc e (Work.SymQuot.DivOf.divOf F (p ≫ v)) := by
          rw [hDdef, Work.SpecLin.DivBase.bc_add]
      _ = Work.SymQuot.DivOf.divOf (AlgebraicClosure F) (Work.SpecLin.RPt.map e (p ≫ u)) +
            Work.SymQuot.DivOf.divOf (AlgebraicClosure F) (Work.SpecLin.RPt.map e (p ≫ v)) := by
          rw [← Work.SymQuot.DivOf.divOf_map e (p ≫ u),
            ← Work.SymQuot.DivOf.divOf_map e (p ≫ v)]
      _ = (∑ i : Fin m, Work.SpecLin.ptDiv (x i)) +
            (∑ j : Fin n, Work.SpecLin.ptDiv (y j)) := by
          rw [← hx, ← hy, Work.SymQuot.DivOf.divOf_powMapC1,
            Work.SymQuot.DivOf.divOf_powMapC1]
      _ = ∑ i : Fin (m + n), Work.SpecLin.ptDiv ((Fin.append x y) i) := by
          rw [Fin.sum_univ_add]
          simp
  -- Hence the base changes agree, and so do the points themselves.
  have hpt : Work.SpecLin.RPt.map e w = Work.SpecLin.RPt.map e w' :=
    Work.SymQuot.DivOf.divOf_injective _ _ (by rw [hdiv_w, hdiv_w'])
  have hw_eq : w = w' := Work.GroupChunk.smap_injective e w w' hpt
  have hmain : Work.SymQuot.DivOf.divOf F w = D := by
    rw [hw_eq, hw']
  rw [hwdef, hDdef] at hmain
  exact hmain

end Work.SymQuot.OfDiv
