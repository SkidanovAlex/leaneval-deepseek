import Mathlib
import Submission.Work.GroupChunk.Gluing.DoubleIntersection

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area GC — the cocycle of the gluing datum

The pointwise cocycle `tr'_cocycle_V` on the chart and the cocycle identity `tr'_cocycle` for the
transition data.  The proof is split into small lemmas, each with a short associativity chain, so
that every kernel check stays small.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

universe u

namespace Work.GroupChunk

noncomputable section

open Work.GCBasics

variable {K : Type u} [Field K]
variable {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver} [SpecLin.DivBase C]
  [D : Input C P0]

namespace CocycleAux

/-- `U i i = ⊤`, so every point of the chart lands in `U i i`. -/
theorem landsIn_U_ii (i : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (p : FPt (Opens.toOver D.V) F) : RPt.LandsIn p (U i i) := by
  rw [U_self i]
  exact RPt.landsIn_top p

/-- **The pointwise triple cocycle for `tpq`**. -/
theorem tpq_triple (i j k : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (p : FPt (Opens.toOver D.V) F) (hpij : RPt.LandsIn p (U i j))
    (hpik : RPt.LandsIn p (U i k)) :
    tpq k i (tpq j k (tpq i j p)) = p := by
  rw [tpq_comp i j k p hpij hpik (tpq_landsIn i j k p hpij hpik)]
  exact tpq_inv i k p hpik (tpq_landsIn i k i p hpik (landsIn_U_ii i p))

/-- **Step 1 of the pointwise cocycle.** -/
theorem cocycle_step₁ (i j k : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (e : FPt (Pb i j k) F) :
    (((e ≫ tr' i j k) ≫ tr' j k i) ≫ tr' k i j) ≫ pbToV i j k
      = tpq k i ((((e ≫ tr' i j k) ≫ tr' j k i) ≫ pbFst k i j) ≫ Opens.ιOver (U k i)) := by
  have h := (tpq_eq_of_lift k i
    ((((e ≫ tr' i j k) ≫ tr' j k i) ≫ pbFst k i j) ≫ Opens.ιOver (U k i))
    (((e ≫ tr' i j k) ≫ tr' j k i) ≫ pbFst k i j) rfl).symm
  rw [Category.assoc, tr'_VM k i j, ← Category.assoc]
  exact h

/-- **Step 2 of the pointwise cocycle.** -/
theorem cocycle_step₂ (i j k : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (e : FPt (Pb i j k) F) :
    ((((e ≫ tr' i j k) ≫ tr' j k i) ≫ pbFst k i j) ≫ Opens.ιOver (U k i))
      = tpq j k (((e ≫ tr' i j k) ≫ pbFst j k i) ≫ Opens.ιOver (U j k)) := by
  have h := (tpq_eq_of_lift j k (((e ≫ tr' i j k) ≫ pbFst j k i) ≫ Opens.ιOver (U j k))
    ((e ≫ tr' i j k) ≫ pbFst j k i) rfl).symm
  rw [Category.assoc, Category.assoc, tr'_VM j k i, ← Category.assoc]
  exact h

/-- **Step 3 of the pointwise cocycle.** -/
theorem cocycle_step₃ (i j k : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (e : FPt (Pb i j k) F) :
    ((e ≫ tr' i j k) ≫ pbFst j k i) ≫ Opens.ιOver (U j k)
      = tpq i j ((e ≫ pbFst i j k) ≫ Opens.ιOver (U i j)) := by
  have h := (tpq_eq_of_lift i j ((e ≫ pbFst i j k) ≫ Opens.ιOver (U i j))
    (e ≫ pbFst i j k) rfl).symm
  rw [Category.assoc, Category.assoc, tr'_VM i j k, ← Category.assoc]
  exact h

/-- The point reached at the end of the chain lands in `U i j`. -/
theorem landsIn_end (i j k : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (e : FPt (Pb i j k) F) :
    RPt.LandsIn ((e ≫ pbFst i j k) ≫ Opens.ιOver (U i j)) (U i j) :=
  landsIn_ιOver_self (U i j) (e ≫ pbFst i j k)

/-- The point reached at the end of the chain lands in `U i k`. -/
theorem landsIn_end' (i j k : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (e : FPt (Pb i j k) F) :
    RPt.LandsIn ((e ≫ pbFst i j k) ≫ Opens.ιOver (U i j)) (U i k) := by
  have h : (e ≫ pbFst i j k) ≫ Opens.ιOver (U i j)
      = (e ≫ pbSnd i j k) ≫ Opens.ιOver (U i k) := by
    rw [Category.assoc, pb_cond i j k, ← Category.assoc]
  rw [h]
  exact landsIn_ιOver_self (U i k) (e ≫ pbSnd i j k)

/-- **The pointwise cocycle** for the composite of the three transitions. -/
theorem tr'_cocycle_pt (i j k : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (e : FPt (Pb i j k) F) :
    (((e ≫ tr' i j k) ≫ tr' j k i) ≫ tr' k i j) ≫ pbToV i j k
      = (e ≫ pbFst i j k) ≫ Opens.ιOver (U i j) := by
  have h₁ := cocycle_step₁ i j k e
  have h₂ := congrArg (tpq k i) (cocycle_step₂ i j k e)
  have h₃ := congrArg (fun z => tpq k i (tpq j k z)) (cocycle_step₃ i j k e)
  have h₄ := tpq_triple i j k ((e ≫ pbFst i j k) ≫ Opens.ιOver (U i j))
    (landsIn_end i j k e) (landsIn_end' i j k e)
  exact h₁.trans (h₂.trans (h₃.trans h₄))

end CocycleAux

open CocycleAux in
/-- **The pointwise cocycle**: the composite of the three transitions, followed by the
inclusion of the chart, is the inclusion of the chart. -/
theorem tr'_cocycle_V (i j k : D.Idx) :
    tr' i j k ≫ tr' j k i ≫ tr' k i j ≫ pbToV i j k = pbToV i j k := by
  apply hom_ext_of_resPt (X := Pb i j k) (Y := Opens.toOver D.V)
  intro x
  conv_lhs => rw [← Category.assoc, ← Category.assoc, ← Category.assoc]
  conv_rhs => rw [← Category.assoc]
  exact tr'_cocycle_pt i j k (resPt (Pb i j k) x)

open CocycleAux in
/-- **The cocycle** of the gluing datum. -/
theorem tr'_cocycle (i j k : D.Idx) :
    tr' i j k ≫ tr' j k i ≫ tr' k i j = 𝟙 (Pb i j k) := by
  apply (cancel_mono (pbToV i j k)).mp
  rw [Category.id_comp, Category.assoc, Category.assoc]
  exact tr'_cocycle_V i j k

end

end Work.GroupChunk
