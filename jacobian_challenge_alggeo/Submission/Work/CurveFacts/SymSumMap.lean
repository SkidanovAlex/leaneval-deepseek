/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area CurveFacts
-/
import Submission.Work.Universal.Basic
import Submission.Work.SymQuot.Sym
import Submission.Work.SymQuot.AddMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area `CurveFacts`: the sum morphism on the *concrete* symmetric powers

`Work.Universal.sumMap D f n` is the sum morphism `Σⁿ f : Symⁿ C ⟶ A` built from a chart datum
`D : Work.GroupChunk.Input C P0` through the quotient property `Work.Universal.SymQuotData`
(uniqueness of the factorisation of `Σ_m (pr_m ≫ f)` through the quotient map).

This file provides the *same* construction for the concrete symmetric powers of area `SY`, using
`Work.SymQuot.Sym.desc` (the universal property of `Sym C n = Cⁿ / Sₙ`) directly, with no
`GroupChunk.Input` in sight.  Its purpose is the additivity of `Σ f` recorded in
`Submission/Work/CurveFacts/AddCompat.lean`: `Work.GroupChunk.Input` does not carry the
compatibility of its `addMap` field with the sum morphism, and
`Work.CurveFacts.symSumMap_addMap` below supplies that compatibility for the concrete symmetric
powers (where `Work.SymQuot.RelQuot.addMap_spec` and `Work.SymQuot.RelQuot.relQuot_epi` are
available), so that a builder of `GroupChunk.Input` can discharge the hypothesis `hadd` of
`Work.CurveFacts.kl_add_of_input`.
-/
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical MonObj

universe u

namespace Work.CurveFacts

/-- The underlying-scheme morphism of `Work.SymQuot.symAction` is the underlying morphism of the
permutation automorphism `Work.SymQuot.permIso`. -/
theorem symAction_hom_left {K : Type u} [Field K] (C : Work.CurveBasics.Curve K) (n : ℕ)
    (σ : ULift.{u} (Equiv.Perm (Fin n))) :
    (Work.SymQuot.symAction C n).hom σ = (Work.SymQuot.permIso C.toOver σ.down).hom.left :=
  rfl

/-- `Work.Universal.sumTerm C f n` is invariant under the `Sₙ`-action on `Cⁿ`. -/
theorem sumTerm_symAction {K : Type u} [Field K] (C : Work.CurveBasics.Curve K)
    (A : Work.GCBasics.Sch K) [GrpObj A] [IsCommMonObj A] (f : C.toOver ⟶ A) (n : ℕ) :
    ∀ σ : ULift.{u} (Equiv.Perm (Fin n)),
      (Work.SymQuot.symAction C n).hom σ ≫ (Universal.sumTerm C f n).left =
        (Universal.sumTerm C f n).left := by
  intro σ
  rw [symAction_hom_left, ← Over.comp_left, Universal.sumTerm_perm C f n σ.down]

/-- **The sum morphism `Σⁿ f` on the concrete symmetric power `Symⁿ C`**: the unique morphism
`Sym C n ⟶ A` whose composite with the quotient map `Cⁿ ⟶ Symⁿ C` is `Σ_m (pr_m ≫ f)`
(`Work.SymQuot.Sym.desc`).  For `n = 0` it is the constant map at the neutral element, and for
`n ≥ 1` it agrees with `Work.Universal.sumMap` for any chart datum built from area `SY`'s
`SymGeom` data (see `Work.CurveFacts.kl_add_of_input` and `NOTES.md`). -/
noncomputable def symSumMap {K : Type u} [Field K] (C : Work.CurveBasics.Curve K)
    (A : Work.GCBasics.Sch K) [GrpObj A] [IsCommMonObj A] (f : C.toOver ⟶ A) (n : ℕ) :
    Work.SymQuot.Sym C n ⟶ A :=
  Classical.choose (Work.SymQuot.Sym.desc C n (Universal.sumTerm C f n)
    (sumTerm_symAction C A f n))

/-- The defining property of `Work.CurveFacts.symSumMap`. -/
theorem symSumMap_spec {K : Type u} [Field K] (C : Work.CurveBasics.Curve K)
    (A : Work.GCBasics.Sch K) [GrpObj A] [IsCommMonObj A] (f : C.toOver ⟶ A) (n : ℕ) :
    Work.SymQuot.Sym.quot C n ≫ symSumMap C A f n = Universal.sumTerm C f n :=
  (Classical.choose_spec (Work.SymQuot.Sym.desc C n (Universal.sumTerm C f n)
    (sumTerm_symAction C A f n))).1

/-- **The value of `symSumMap` on `n` points of `C`**: the sum of the images of the points. -/
theorem symSumMap_powMap {K : Type u} [Field K] (C : Work.CurveBasics.Curve K)
    (A : Work.GCBasics.Sch K) [GrpObj A] [IsCommMonObj A] (f : C.toOver ⟶ A) (n : ℕ)
    {T : Work.GCBasics.Sch K} (x : Fin n → (T ⟶ C.toOver)) :
    Work.SymQuot.Sym.powMap C n x ≫ symSumMap C A f n = ∏ m, (x m ≫ f) := by
  have hpow : Work.SymQuot.Sym.powMap C n x
      = Limits.Pi.lift x ≫ Work.SymQuot.Sym.quot C n := rfl
  calc Work.SymQuot.Sym.powMap C n x ≫ symSumMap C A f n
      = (Limits.Pi.lift x ≫ Work.SymQuot.Sym.quot C n) ≫ symSumMap C A f n := by rw [hpow]
    _ = Limits.Pi.lift x ≫ (Work.SymQuot.Sym.quot C n ≫ symSumMap C A f n) :=
        Category.assoc _ _ _
    _ = Limits.Pi.lift x ≫ Universal.sumTerm C f n :=
        congrArg (fun u => Limits.Pi.lift x ≫ u) (symSumMap_spec C A f n)
    _ = ∏ m, (x m ≫ f) := by
        show Limits.Pi.lift x ≫ (∏ m, (Universal.proj C n m ≫ f)) = ∏ m, (x m ≫ f)
        exact (Universal.comp_prod (Limits.Pi.lift x) (fun m => Universal.proj C n m ≫ f)).trans
          (Finset.prod_congr rfl (fun m _ => (Category.assoc _ _ _).symm.trans
            (congrArg (fun u => u ≫ f)
              (Limits.Pi.lift_comp_π (f := fun _ : Fin n => C.toOver) x m))))

end Work.CurveFacts
