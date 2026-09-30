import Mathlib
import Submission.Work.CurveFacts.SymSumMap
import Submission.Work.SymQuot.AddMap
import Submission.Work.SymQuot.RelQuot.exists_addMap

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

/-- **The compatibility of the addition of symmetric powers with the sum morphism, for the
concrete symmetric powers.**  For the concrete `n`-th symmetric power `Symⁿ C` and its sum
morphism `Work.CurveFacts.symSumMap C A f n` (built from `Work.SymQuot.Sym.desc`,
`Submission/Work/CurveFacts/SymSumMap.lean`), adding `m` points and `n` points and then summing is
the product of the two sums.

This is exactly the datum that `Work.GroupChunk.Input` does not record (its field `addMap` is
constrained only by the divisor-level `addMap_divOf`); it is
`Work.CurveFacts.IsAddSumMapPow` for a chart datum whose symmetric-power data is area `SY`'s.

Route, in two steps.
1. `Work.SymQuot.addMap_spec` (`Submission/Work/SymQuot/AddMap.lean`) says
   `CartesianMonoidalCategory.lift (Sym.powMap C m x) (Sym.powMap C n y) ≫ SymQuot.addMap C m n
     = Sym.powMap C (m + n) (Fin.append x y)`.
2. `Work.CurveFacts.symSumMap_powMap` says `Sym.powMap C k z ≫ symSumMap C A f k = ∏ i, (z i ≫ f)`
   (`Universal.prodHom`).  What is left is the splitting of the product over `Fin (m + n)` indexed
   by `Fin.append` into the product over `Fin m` times the product over `Fin n`: Mathlib's
   `Fin.prod_univ_add` together with `Fin.append_left`/`Fin.append_right`, and the fact that
   `Universal.prodHom` is a product in the group of morphisms into the commutative group object
   `A`.  A short proof is `rw [Work.SymQuot.addMap_spec]; rw [symSumMap_powMap, symSumMap_powMap,
   symSumMap_powMap]; rw [Fin.prod_univ_add]; simp [Fin.append_left, Fin.append_right]`. -/
theorem symSumMap_addMap {K : Type u} [Field K] (C : Work.CurveBasics.Curve K)
    (A : Work.GCBasics.Sch K) [GrpObj A] [IsCommMonObj A] (f : C.toOver ⟶ A) (m n : ℕ)
    {T : Work.GCBasics.Sch K} (x : Fin m → (T ⟶ C.toOver)) (y : Fin n → (T ⟶ C.toOver)) :
    (CartesianMonoidalCategory.lift (Work.SymQuot.Sym.powMap C m x)
        (Work.SymQuot.Sym.powMap C n y) ≫ Work.SymQuot.addMap C m n)
      ≫ Work.CurveFacts.symSumMap C A f (m + n) =
    (Work.SymQuot.Sym.powMap C m x ≫ Work.CurveFacts.symSumMap C A f m) *
      (Work.SymQuot.Sym.powMap C n y ≫ Work.CurveFacts.symSumMap C A f n) := by
  rw [Work.SymQuot.addMap_spec]
  rw [symSumMap_powMap, symSumMap_powMap, symSumMap_powMap]
  rw [Fin.prod_univ_add]
  simp [Fin.append_left, Fin.append_right]

end Work.CurveFacts
