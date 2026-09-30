/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A point of `Symⁿ C` is determined by its divisor (area SY, `divOf`)

This file proves `Work.SymQuot.DivOf.divOf_injective`, the two-sided half of the point/divisor
dictionary of the `n`-th symmetric power of a curve: two `F`-points `p q` of `Symⁿ C` with the
same associated divisor `divOf F p = divOf F q` are equal.

## Proof

Pass to an algebraically closed extension `F̄` of `F` (`AlgebraicClosure F`), along which the base
change of points `RPt.map` is injective (`Work.GroupChunk.smap_injective`, via `Spec F̄ ⟶ Spec F`
being an epimorphism).  Over `F̄` the two points split into `n` points of `C`
(`Work.SymQuot.Sym.exists_powMap_eq`), say `p̄ = powMap x` and `q̄ = powMap y` with
`x y : Fin n → C(F̄)`.  The hub lemma C1′ `Work.SymQuot.DivOf.divMap_divOfChart` computes the base
change of the divisor of a point in terms of such a splitting:

`divMap (divOf p) = ∑ m, ptDiv (x m)`,

so `divOf p = divOf q` gives `∑ m, ptDiv (x m) = ∑ m, ptDiv (y m)`.  Comparing multiplicities
(`Work.SymQuot.DivOf.ptDiv_sum_eq_iff`) exhibits a permutation `σ` with `y m = x (σ m)`, whence
`powMap y = powMap x` by `Work.SymQuot.Sym.powMap_eq_iff_exists_perm`, i.e. the base changes of
`p` and `q` agree.  Injectivity of the base change concludes.
-/
import Mathlib
import Submission.Work.SymQuot.Sym
import Submission.Work.SymQuot.DivOf.DivOf
import Submission.Work.SpecLin.Points.Basic
import Submission.Work.SymQuot.DivOf.divMap_divOfChart
import Submission.Work.SymQuot.DivOf.divMap_injective
import Submission.Work.SymQuot.DivOf.ptDiv_sum_eq_iff
import Submission.Work.SymQuot.Sym.exists_powMap_eq
import Submission.Work.SymQuot.Sym.powMap_eq_iff_exists_perm
import Submission.Work.GroupChunk.landsIn_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot.DivOf

open Work.CurveBasics

theorem divOf_injective {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    (p q : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F) :
    divOf F p = divOf F q → p = q := by
  intro hpq
  -- Work over an algebraically closed extension of `F`, over which both points split.
  set e : F →ₐ[K] AlgebraicClosure F := IsScalarTower.toAlgHom K F (AlgebraicClosure F) with he
  obtain ⟨x, hx⟩ := Work.SymQuot.Sym.exists_powMap_eq C n (Work.SpecLin.RPt.map e p)
  obtain ⟨y, hy⟩ := Work.SymQuot.Sym.exists_powMap_eq C n (Work.SpecLin.RPt.map e q)
  -- C1′ expresses the base change of `divOf` as the sum of the point divisors of a splitting.
  have hp : (bcSquareTower (C := C) F (AlgebraicClosure F)).divMap (divOf F p)
      = ∑ m, Work.SpecLin.ptDiv (x m) := by
    have : Nonempty (chartOf C n p).V := chartOf_nonempty C n p
    exact divMap_divOfChart (C := C) (n := n) (chartOf C n p) x hx
  have hq : (bcSquareTower (C := C) F (AlgebraicClosure F)).divMap (divOf F q)
      = ∑ m, Work.SpecLin.ptDiv (y m) := by
    have : Nonempty (chartOf C n q).V := chartOf_nonempty C n q
    exact divMap_divOfChart (C := C) (n := n) (chartOf C n q) y hy
  -- Hence the two splittings have the same sum of point divisors.
  have hsum : (∑ m, Work.SpecLin.ptDiv (x m)) = (∑ m, Work.SpecLin.ptDiv (y m)) := by
    rw [← hp, hpq, hq]
  have hperm := (ptDiv_sum_eq_iff x y).mp hsum
  -- Comparing the multiplicities: the two splittings differ by a permutation.
  have hpow : Work.SymQuot.Sym.powMap C n x = Work.SymQuot.Sym.powMap C n y :=
    (Work.SymQuot.Sym.powMap_eq_iff_exists_perm C n x y).mpr hperm
  -- So the base changes of `p` and `q` agree, and base change of points is injective.
  have hpe : Work.SpecLin.RPt.map e p = Work.SpecLin.RPt.map e q := by
    rw [← hx, ← hy]
    exact hpow
  exact Work.GroupChunk.smap_injective e p q hpe

end Work.SymQuot.DivOf
