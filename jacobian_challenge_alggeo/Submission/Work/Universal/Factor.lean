/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area UP — the morphism `factor : G D ⟶ A`

For a morphism `f : C ⟶ A` into a commutative group scheme, `factor f : G D ⟶ A` is the
morphism glued from the chart maps `chartMap f i` (the `i`-th translate `Σ^g f / Σ^g f(E i)`
of the sum morphism); the compatibility of the chart maps on the transition domains is the
KL computation `factorCompat_holds` (`Submission/Work/Universal/factorCompat_holds.lean`).
-/
import Submission.Work.Universal.Basic
import Submission.Work.Universal.factorCompat_holds

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical MonObj
open scoped Work.GCBasics

universe u

namespace Work.Universal

noncomputable section

open Work.GCBasics Work.GroupChunk

variable {K : Type u} [Field K]
variable {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver} [SpecLin.DivBase C]
  [D : GroupChunk.Input C P0] [U : Input C P0]

/-- **The morphism `factor : G D ⟶ A`** attached to a morphism `f : C ⟶ A` into a commutative
group scheme: the gluing of the chart maps `D ↦ Σ f(D) / Σ f(E i)`. -/
def factor {A : Sch K} [GrpObj A] [IsCommMonObj A] [IsProper A.hom] (f : C.toOver ⟶ A) : U.glued.G ⟶ A :=
  factorWith (D := D) f (factorCompat_holds (D := D) f)

/-- **The restriction of `factor f` to the `i`-th chart** is the chart map `chartMap f i`. -/
theorem factor_eq_chartMap {A : Sch K} [GrpObj A] [IsCommMonObj A] [IsProper A.hom] (f : C.toOver ⟶ A)
    (i : D.Idx) : U.glued.chart i ≫ factor (D := D) f = chartMap (D := D) f i :=
  factorWith_spec (D := D) f _ i

/-- **The defining property of `factor`**: it is the unique morphism out of `G D` whose
restriction to every chart is the chart map `chartMap f i`. -/
theorem factor_unique {A : Sch K} [GrpObj A] [IsCommMonObj A] [IsProper A.hom] (f : C.toOver ⟶ A)
    (g : U.glued.G ⟶ A) (hg : ∀ i : D.Idx, U.glued.chart i ≫ g = chartMap (D := D) f i) :
    g = factor (D := D) f :=
  (Classical.choose_spec
    (U.descG (fun i => chartMap (D := D) f i) (factorCompat_holds (D := D) f))).2 g hg

end

end Work.Universal
