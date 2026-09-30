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


set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

namespace Work.SymQuot.OfDiv

open CategoryTheory Limits AlgebraicGeometry in
open scoped MonoidalCategory in
/-- Addition of symmetric powers, left-zero case: the divisor of the point
`(p ≫ liftEquiv (u, v)) ≫ addMap C 0 n` of `Sym^{0+n} C` is the divisor of `p ≫ v`, since the
`Sym^0 C`-component contributes the zero divisor.  The general statement `addMap_divOf` requires
`m ≠ 0`; this supplies the missing `m = 0` case. -/
theorem addMap_divOf_zero_left {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    [Work.SymQuot.CurveAffineCover C] {n : ℕ} [NeZero n] {X : Work.SpecLin.Sch K}
    (u : X ⟶ Work.SymQuot.Sym C 0) (v : X ⟶ Work.SymQuot.Sym C n)
    {F : Type u} [Field F] [Algebra K F] (p : Work.SpecLin.FPt X F) :
    Work.SymQuot.DivOf.divOf F
        ((p ≫ CartesianMonoidalCategory.liftEquiv (u, v)) ≫ Work.SymQuot.addMap C 0 n)
      = (Work.SymQuot.symGeomZero C).divOf (p ≫ u) + Work.SymQuot.DivOf.divOf F (p ≫ v) := by
  classical
  -- The `Sym^0 C`-component contributes the zero divisor.
  have hzero : (Work.SymQuot.symGeomZero C).divOf (p ≫ u) = 0 := rfl
  -- Work over an algebraic closure of `F`.
  let e : F →ₐ[K] AlgebraicClosure F := IsScalarTower.toAlgHom K F (AlgebraicClosure F)
  -- Base change of divisors along `e` is injective.
  have hbcinj : Function.Injective (Work.SpecLin.DivBase.bc (C := C) e) := by
    intro D D' h
    exact Work.SymQuot.DivOf.divMap_injective
      (Work.SymQuot.DivOf.bcSquareTower (C := C) F (AlgebraicClosure F)) h
  -- The core statement: `divOf` of the sum point is `divOf (p ≫ v)`.
  have hcore : Work.SymQuot.DivOf.divOf F
        ((p ≫ CartesianMonoidalCategory.liftEquiv (u, v)) ≫ Work.SymQuot.addMap C 0 n)
      = Work.SymQuot.DivOf.divOf F (p ≫ v) := by
    set w : Work.SpecLin.FPt (Work.SymQuot.Sym C (0 + n)) F :=
      (p ≫ CartesianMonoidalCategory.liftEquiv (u, v)) ≫ Work.SymQuot.addMap C 0 n with hwdef
    -- Split the two base-changed points into points of `C`.
    obtain ⟨x, hx⟩ := Work.SymQuot.Sym.exists_powMap_eq (K := K) C 0
      (Work.SpecLin.RPt.map e (p ≫ u))
    obtain ⟨y, hy⟩ := Work.SymQuot.Sym.exists_powMap_eq (K := K) C n
      (Work.SpecLin.RPt.map e (p ≫ v))
    -- Over the algebraic closure, `liftEquiv (u, v)` is the sum of the two splittings.
    have hprod : Work.SpecLin.RPt.map e p ≫ CartesianMonoidalCategory.liftEquiv (u, v) =
        CartesianMonoidalCategory.lift (Work.SymQuot.Sym.powMap C 0 x)
          (Work.SymQuot.Sym.powMap C n y) := by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc, CartesianMonoidalCategory.liftEquiv_apply,
          CartesianMonoidalCategory.lift_fst]
        rw [← Work.SymQuot.OfDiv.RPt_map_comp_assoc, ← hx]
      · simp only [Category.assoc, CartesianMonoidalCategory.liftEquiv_apply,
          CartesianMonoidalCategory.lift_snd]
        rw [← Work.SymQuot.OfDiv.RPt_map_comp_assoc, ← hy]
    -- Hence `w` base-changes to the sum of the appended splittings.
    have hwL : Work.SpecLin.RPt.map e w =
        Work.SymQuot.Sym.powMap C (0 + n) (Fin.append x y) := by
      rw [hwdef]
      rw [Work.SymQuot.OfDiv.RPt_map_comp_assoc (X := Work.SymQuot.Sym C 0 ⊗ Work.SymQuot.Sym C n)
        (Y := Work.SymQuot.Sym C (0 + n)) e
        (p ≫ CartesianMonoidalCategory.liftEquiv (u, v)) (Work.SymQuot.addMap C 0 n)]
      rw [Work.SymQuot.OfDiv.RPt_map_comp_assoc (X := X)
        (Y := Work.SymQuot.Sym C 0 ⊗ Work.SymQuot.Sym C n) e p
        (CartesianMonoidalCategory.liftEquiv (u, v))]
      rw [hprod, Work.SymQuot.addMap_spec]
    -- The base-changed divisors, computed by the point/divisor dictionary.
    have h1 : Work.SymQuot.DivOf.divOf (AlgebraicClosure F) (Work.SpecLin.RPt.map e w) =
        ∑ i : Fin (0 + n), Work.SpecLin.ptDiv ((Fin.append x y) i) := by
      rw [hwL]
      exact Work.SymQuot.DivOf.divOf_powMapC1 (C := C) (n := 0 + n) (Fin.append x y)
    have h2 : Work.SymQuot.DivOf.divOf (AlgebraicClosure F)
        (Work.SpecLin.RPt.map e (p ≫ v)) = ∑ j : Fin n, Work.SpecLin.ptDiv (y j) := by
      rw [← hy]
      exact Work.SymQuot.DivOf.divOf_powMapC1 (C := C) (n := n) y
    -- The two sums agree: the `Fin 0`-splitting contributes nothing.
    have hsum : (∑ i : Fin (0 + n), Work.SpecLin.ptDiv ((Fin.append x y) i)) =
        ∑ j : Fin n, Work.SpecLin.ptDiv (y j) := by
      rw [Fin.sum_univ_add]
      simp only [Fin.sum_univ_zero, zero_add]
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      exact Fin.append_right x y j
    -- Hence the base-changed divisors agree, so the divisors themselves agree.
    have hbc_eq : Work.SpecLin.DivBase.bc e (Work.SymQuot.DivOf.divOf F w) =
        Work.SpecLin.DivBase.bc e (Work.SymQuot.DivOf.divOf F (p ≫ v)) := by
      rw [← Work.SymQuot.DivOf.divOf_map e w, ← Work.SymQuot.DivOf.divOf_map e (p ≫ v)]
      rw [h1, h2, hsum]
    exact hbcinj hbc_eq
  rw [hzero]
  exact hcore.trans (zero_add (Work.SymQuot.DivOf.divOf F (p ≫ v))).symm

end Work.SymQuot.OfDiv
