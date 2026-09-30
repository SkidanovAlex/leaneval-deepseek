import Mathlib
import Submission.Work.SymQuot.SymGeomInst
import Submission.Work.SymQuot.OfDiv.addMap_divOf
import Submission.Work.SymQuot.AddMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option linter.style.haveILetI false

universe u

namespace Work.SymQuot.OfDiv

open CategoryTheory Limits AlgebraicGeometry in
open scoped MonoidalCategory in
theorem addMap_divOf_zero_right {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    [Work.SymQuot.CurveAffineCover C] {m : ℕ} [NeZero m] {X : Work.SpecLin.Sch K}
    (u : X ⟶ Work.SymQuot.Sym C m) (v : X ⟶ Work.SymQuot.Sym C 0)
    {F : Type u} [Field F] [Algebra K F] (p : Work.SpecLin.FPt X F) :
    Work.SymQuot.DivOf.divOf F
        ((p ≫ CartesianMonoidalCategory.liftEquiv (u, v)) ≫ Work.SymQuot.addMap C m 0)
      = Work.SymQuot.DivOf.divOf F (p ≫ u) + (Work.SymQuot.symGeomZero C).divOf (p ≫ v) := by
  classical
  -- The point of `Sym^{m+0} C` whose divisor we compute.
  set w : Work.SpecLin.FPt (Work.SymQuot.Sym C (m + 0)) F :=
    (p ≫ CartesianMonoidalCategory.liftEquiv (u, v)) ≫ Work.SymQuot.addMap C m 0 with hwdef
  -- The expected divisor: effective of degree `m + 0` (the second summand is `0`).
  set D : Work.SpecLin.Dv C F :=
    Work.SymQuot.DivOf.divOf F (p ≫ u) + (Work.SymQuot.symGeomZero C).divOf (p ≫ v) with hDdef
  have hD0 : (Work.SymQuot.symGeomZero C).divOf (p ≫ v) = 0 := rfl
  have hDeff : Work.CurveBasics.Curve.Div.IsEffective D := by
    rw [hDdef, hD0, add_zero]
    exact Work.SymQuot.DivOf.divOf_isEffective (p ≫ u)
  have hDdeg : (C.baseChange F).deg D = ((m + 0 : ℕ) : ℤ) := by
    rw [hDdef, hD0, add_zero, Work.SymQuot.DivOf.divOf_deg (C := C) (n := m) (p ≫ u)]
    simp
  -- A point of `Sym^{m+0} C` with divisor `D`.
  obtain ⟨w', hw'⟩ :=
    Work.SymQuot.DivOf.Complete.divOf_complete (C := C) (n := m + 0) D hDeff hDdeg
  -- Pass to an algebraic closure of `F`, where `p ≫ u` splits into `m` points of `C`.
  let e : F →ₐ[K] AlgebraicClosure F := IsScalarTower.toAlgHom K F (AlgebraicClosure F)
  obtain ⟨x, hx⟩ := Work.SymQuot.Sym.exists_powMap_eq (K := K) C m
    (Work.SpecLin.RPt.map e (p ≫ u))
  -- The second component is a point of `Sym⁰ C`, where all morphisms are equal.
  let y : Fin 0 → Work.SpecLin.CurveFPt C (AlgebraicClosure F) := fun i => Fin.elim0 i
  have hy : Work.SymQuot.Sym.powMap C 0 y = Work.SpecLin.RPt.map e (p ≫ v) := by
    haveI : Subsingleton (Work.SpecLin.specOf (K := K) (AlgebraicClosure F) ⟶
        Work.SymQuot.Sym C 0) :=
      Work.SymQuot.Sym.subsingleton_hom_sym_zero C _
    exact Subsingleton.elim _ _
  -- Over the algebraic closure, `w` is the sum of the (base changes of the) two points.
  have hprod :
      Work.SpecLin.RPt.map e p ≫ CartesianMonoidalCategory.liftEquiv (u, v) =
        CartesianMonoidalCategory.lift (Work.SymQuot.Sym.powMap C m x)
          (Work.SymQuot.Sym.powMap C 0 y) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, CartesianMonoidalCategory.liftEquiv_apply,
        CartesianMonoidalCategory.lift_fst]
      rw [← RPt_map_comp_assoc, ← hx]
    · simp only [Category.assoc, CartesianMonoidalCategory.liftEquiv_apply,
        CartesianMonoidalCategory.lift_snd]
      rw [← RPt_map_comp_assoc, ← hy]
  have hwL : Work.SpecLin.RPt.map e w =
      Work.SymQuot.Sym.powMap C (m + 0) (Fin.append x y) := by
    rw [hwdef]
    rw [RPt_map_comp_assoc (X := Work.SymQuot.Sym C m ⊗ Work.SymQuot.Sym C 0)
      (Y := Work.SymQuot.Sym C (m + 0)) e
      (p ≫ CartesianMonoidalCategory.liftEquiv (u, v)) (Work.SymQuot.addMap C m 0)]
    rw [RPt_map_comp_assoc (X := X)
      (Y := Work.SymQuot.Sym C m ⊗ Work.SymQuot.Sym C 0) e p
      (CartesianMonoidalCategory.liftEquiv (u, v))]
    rw [hprod, Work.SymQuot.addMap_spec]
  -- The divisors of the two base-changed points agree.
  have hdiv_w : Work.SymQuot.DivOf.divOf (AlgebraicClosure F) (Work.SpecLin.RPt.map e w) =
      ∑ i : Fin (m + 0), Work.SpecLin.ptDiv ((Fin.append x y) i) := by
    rw [hwL]
    exact Work.SymQuot.DivOf.divOf_powMapC1 (Fin.append x y)
  have hdiv_w' : Work.SymQuot.DivOf.divOf (AlgebraicClosure F) (Work.SpecLin.RPt.map e w') =
      ∑ i : Fin (m + 0), Work.SpecLin.ptDiv ((Fin.append x y) i) := by
    calc Work.SymQuot.DivOf.divOf (AlgebraicClosure F) (Work.SpecLin.RPt.map e w')
        = Work.SpecLin.DivBase.bc e (Work.SymQuot.DivOf.divOf F w') :=
          Work.SymQuot.DivOf.divOf_map e w'
      _ = Work.SpecLin.DivBase.bc e D := by rw [hw']
      _ = Work.SpecLin.DivBase.bc e (Work.SymQuot.DivOf.divOf F (p ≫ u) +
            (Work.SymQuot.symGeomZero C).divOf (p ≫ v)) := by rw [hDdef]
      _ = Work.SpecLin.DivBase.bc e (Work.SymQuot.DivOf.divOf F (p ≫ u)) +
            Work.SpecLin.DivBase.bc e ((Work.SymQuot.symGeomZero C).divOf (p ≫ v)) := by
          rw [Work.SpecLin.DivBase.bc_add]
      _ = Work.SpecLin.DivBase.bc e (Work.SymQuot.DivOf.divOf F (p ≫ u)) + 0 := by
          rw [hD0, Work.SpecLin.DivBase.bc_zero]
      _ = Work.SpecLin.DivBase.bc e (Work.SymQuot.DivOf.divOf F (p ≫ u)) := by rw [add_zero]
      _ = Work.SymQuot.DivOf.divOf (AlgebraicClosure F)
            (Work.SpecLin.RPt.map e (p ≫ u)) := (Work.SymQuot.DivOf.divOf_map e (p ≫ u)).symm
      _ = Work.SymQuot.DivOf.divOf (AlgebraicClosure F)
            (Work.SymQuot.Sym.powMap C m x) := by rw [hx]
      _ = ∑ i : Fin m, Work.SpecLin.ptDiv (x i) := Work.SymQuot.DivOf.divOf_powMapC1 x
      _ = ∑ i : Fin (m + 0), Work.SpecLin.ptDiv ((Fin.append x y) i) := by
          rw [Fin.sum_univ_add]
          simp only [Fin.append_left, Fin.append_right, Fin.sum_univ_zero, add_zero]
  -- Hence the base changes agree, and so do the points themselves.
  have hpt : Work.SpecLin.RPt.map e w = Work.SpecLin.RPt.map e w' :=
    Work.SymQuot.DivOf.divOf_injective _ _ (by rw [hdiv_w, hdiv_w'])
  have hw_eq : w = w' := Work.GroupChunk.smap_injective e w w' hpt
  have hmain : Work.SymQuot.DivOf.divOf F w = D := by rw [hw_eq, hw']
  rw [hwdef, hDdef] at hmain
  exact hmain

end Work.SymQuot.OfDiv
