import Mathlib
import Submission.Work.GroupChunk.Gluing.Transitions

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area GC — the double intersections of the charts

The pullback `Pb i j k` of the two inclusions `U i j ↪ V` and `U i k ↪ V`, the transition `tr'`
between the two double intersections, and its elementary properties.
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


/-- The scheme of the double intersection `U i j ⊓ U i k`, as the pullback of the two
inclusions into the chart. -/
abbrev Pb (i j k : D.Idx) : Sch K :=
  pullback (Opens.ιOver (U i j)) (Opens.ιOver (U i k))

abbrev pbFst (i j k : D.Idx) : Pb i j k ⟶ Opens.toOver (U i j) := pullback.fst _ _

abbrev pbSnd (i j k : D.Idx) : Pb i j k ⟶ Opens.toOver (U i k) := pullback.snd _ _

/-- The inclusion of the double intersection into the chart. -/
abbrev pbToV (i j k : D.Idx) : Pb i j k ⟶ Opens.toOver D.V :=
  pbFst i j k ≫ Opens.ιOver (U i j)

theorem pb_cond (i j k : D.Idx) :
    pbFst i j k ≫ Opens.ιOver (U i j) = pbSnd i j k ≫ Opens.ιOver (U i k) :=
  pullback.condition

instance instIsReducedPb (i j k : D.Idx) : IsReduced (Pb i j k).left := by
  haveI : IsReduced (pullback ((Over.forget (Spec (CommRingCat.of K))).map (Opens.ιOver (U i j)))
      ((Over.forget (Spec (CommRingCat.of K))).map (Opens.ιOver (U i k)))) :=
    show IsReduced (pullback (Opens.ιOver (U i j)).left (Opens.ιOver (U i k)).left) from
      isReduced_of_isOpenImmersion (pullback.fst (Opens.ιOver (U i j)).left
        (Opens.ιOver (U i k)).left)
  exact isReduced_of_isOpenImmersion
    (PreservesPullback.iso (Over.forget (Spec (CommRingCat.of K)))
      (Opens.ιOver (U i j)) (Opens.ιOver (U i k))).hom

/-- **The transition carries `U i j ⊓ U i k` into `U j k`.** -/
theorem tr'_range (i j k : D.Idx) :
    Set.range (pbFst i j k ≫ tq i j).left ⊆ (U j k : Set _) := by
  rw [range_subset_iff_landsIn]
  intro x
  let F : Type u := resField (Pb i j k) x
  set e : FPt (Pb i j k) F := resPt (Pb i j k) x with he
  have hpij : RPt.LandsIn ((e ≫ pbFst i j k) ≫ Opens.ιOver (U i j)) (U i j) :=
    landsIn_ιOver_self (U i j) (e ≫ pbFst i j k)
  have hpk : RPt.LandsIn ((e ≫ pbFst i j k) ≫ Opens.ιOver (U i j)) (U i k) := by
    have h2 : (e ≫ pbFst i j k) ≫ Opens.ιOver (U i j)
        = (e ≫ pbSnd i j k) ≫ Opens.ιOver (U i k) := by
      rw [Category.assoc, pb_cond i j k, ← Category.assoc]
    rw [h2]
    exact landsIn_ιOver_self (U i k) (e ≫ pbSnd i j k)
  have h1 := tpq_landsIn (D := D) i j k ((e ≫ pbFst i j k) ≫ Opens.ιOver (U i j)) hpij hpk
  rw [tpq_eq_of_lift i j _ (e ≫ pbFst i j k) rfl] at h1
  have hgoal : e ≫ pbFst i j k ≫ tq i j = (e ≫ pbFst i j k) ≫ tq i j := by
    rw [← Category.assoc]
  rw [hgoal]
  exact h1


/-- The map on double intersections induced by the transition `tr i j`. -/
def tr' (i j k : D.Idx) : Pb i j k ⟶ Pb j k i :=
  pullback.lift
    (Classical.choose (exists_factor_of_range_subset (U j k) (pbFst i j k ≫ tq i j)
      (tr'_range i j k)))
    (pbFst i j k ≫ tr i j)
    (by
      rw [(Classical.choose_spec (exists_factor_of_range_subset (U j k) (pbFst i j k ≫ tq i j)
        (tr'_range i j k))).1, ← tr_ιOver, Category.assoc])

theorem tr'_fst (i j k : D.Idx) : tr' i j k ≫ pbFst j k i =
    Classical.choose (exists_factor_of_range_subset (U j k) (pbFst i j k ≫ tq i j)
      (tr'_range i j k)) :=
  pullback.lift_fst _ _ _

theorem tr'_snd (i j k : D.Idx) : tr' i j k ≫ pbSnd j k i = pbFst i j k ≫ tr i j :=
  pullback.lift_snd _ _ _

/-- The class of the point reached by the transition, computed on the double intersection. -/
theorem tr'_VM (i j k : D.Idx) : tr' i j k ≫ pbToV j k i = pbFst i j k ≫ tq i j := by
  rw [← Category.assoc, tr'_fst]
  exact (Classical.choose_spec (exists_factor_of_range_subset (U j k) (pbFst i j k ≫ tq i j)
    (tr'_range i j k))).1

theorem tr'_fac (i j k : D.Idx) :
    tr' i j k ≫ pbSnd j k i = pbFst i j k ≫ tr i j := tr'_snd i j k

end

end Work.GroupChunk
