import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLComp.Misiurewicz.Defs
import Submission.Work.EKLComp.Core
import Submission.Work.EKLComp.Entropy

/-!
# Subadditivity of `Hfam` along the time splitting `N = a + b`

The join `joinSets T P (a+b)` of the finite partition `P` over the first `a+b` iterates of `T`
splits at the cut `a` into the join over the first `a` iterates and the "window join" over the
times `[a, a+b)`:

`Work.EKLContract.joinSets T P (a+b) (Fin.append u v) = joinSets T P a u ∩ T^[a] ⁻¹' joinSets T P b v`

(`Work.EKLComp.Core.joinSets_append`).  The two families

`u ↦ joinSets T P a u`   and   `v ↦ T^[a] ⁻¹' joinSets T P b v`

are separately finite measurable partitions of `X`, and the entropy of a common refinement of two
partitions is at most the sum of the entropies (`Work.EKLComp.Core.Hfam_inter_le`).  Hence

`Hfam μ (joinSets T P (a+b)) ≤ Hfam μ (joinSets T P a) + Hfam μ (T^[a] ⁻¹' joinSets T P b ·)`.

Nothing here needs `μ` to be invariant under `T`: the second summand is the entropy of the
*pullback* family, which is exactly what `Work.EKLComp.winJoin T P a b` is
(`Work.EKLComp.winJoin_eq_preimage`).  This is the difference from
`Work.EKLComp.Core.Hfam_joinSets_add_le`, which compares the two *aligned* joins `a` and `b` and
therefore consumes the measure-preservation hypothesis.
-/

namespace Work.Misiurewicz

open MeasureTheory
open scoped BigOperators

set_option maxHeartbeats 2000000

/-- The `Hfam` of the join over `a + b` iterates of `T` is at most the `Hfam` of the join over
the first `a` iterates plus the `Hfam` of the pullback `T^[a] ⁻¹' joinSets T P b` of the join
over the next `b` iterates.  No invariance of `μ` under `T` is required. -/
theorem Hfam_joinSets_window_le {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ]
    (T : X → X) (hT : Measurable T) (P : Work.EKLContract.FinPart X) (a b : ℕ) :
    Work.EKLContract.Hfam μ (Work.EKLContract.joinSets T P (a + b)) ≤
      Work.EKLContract.Hfam μ (Work.EKLContract.joinSets T P a) +
        Work.EKLContract.Hfam μ
          (fun v : Fin b → Fin P.n => T^[a] ⁻¹' Work.EKLContract.joinSets T P b v) := by
  classical
  have hB : Work.EKLComp.Core.IsMPart
      (fun v : Fin b → Fin P.n => T^[a] ⁻¹' Work.EKLContract.joinSets T P b v) :=
    ⟨fun v => (Work.EKLComp.Core.joinSets_measurable hT P b v).preimage (hT.iterate a),
      fun u v huv => (Work.EKLComp.Core.joinSets_disjoint T P b huv).preimage (T^[a]),
      by rw [← Set.preimage_iUnion, Work.EKLComp.Core.joinSets_iUnion T P b, Set.preimage_univ]⟩
  have hsplit : Work.EKLContract.Hfam μ (Work.EKLContract.joinSets T P (a + b)) =
      Work.EKLContract.Hfam μ (fun q : (Fin a → Fin P.n) × (Fin b → Fin P.n) =>
        Work.EKLContract.joinSets T P a q.1 ∩
          T^[a] ⁻¹' Work.EKLContract.joinSets T P b q.2) := by
    rw [← Work.EKLComp.Core.Hfam_equiv μ (Fin.appendEquiv (α := Fin P.n) a b)
      (Work.EKLContract.joinSets T P (a + b))]
    refine Finset.sum_congr rfl fun q _ => ?_
    dsimp only
    rw [show Work.EKLContract.joinSets T P (a + b)
          (Fin.appendEquiv (α := Fin P.n) a b q) =
        Work.EKLContract.joinSets T P a q.1 ∩
          T^[a] ⁻¹' Work.EKLContract.joinSets T P b q.2 from
      Work.EKLComp.Core.joinSets_append T P a b q.1 q.2]
  calc Work.EKLContract.Hfam μ (Work.EKLContract.joinSets T P (a + b))
      = Work.EKLContract.Hfam μ (fun q : (Fin a → Fin P.n) × (Fin b → Fin P.n) =>
          Work.EKLContract.joinSets T P a q.1 ∩
            T^[a] ⁻¹' Work.EKLContract.joinSets T P b q.2) := hsplit
    _ ≤ Work.EKLContract.Hfam μ (Work.EKLContract.joinSets T P a) +
          Work.EKLContract.Hfam μ
            (fun v : Fin b → Fin P.n => T^[a] ⁻¹' Work.EKLContract.joinSets T P b v) :=
        Work.EKLComp.Core.Hfam_inter_le μ
          (Work.EKLComp.Core.joinSets_isMPart hT P a) hB

theorem Hfam_joinSets_add (μ : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsProbabilityMeasure μ]
    (T : Work.EKLContract.X3 → Work.EKLContract.X3) (hT : Measurable T)
    (P : Work.EKLContract.FinPart Work.EKLContract.X3) (a b : ℕ) :
    Work.EKLContract.Hfam μ (Work.EKLContract.joinSets T P (a + b)) ≤
      Work.EKLContract.Hfam μ (Work.EKLContract.joinSets T P a) +
        Work.EKLContract.Hfam μ (Work.EKLComp.winJoin T P a b) := by
  have h := Hfam_joinSets_window_le μ T hT P a b
  have hfun : (fun v : Fin b → Fin P.n => T^[a] ⁻¹' Work.EKLContract.joinSets T P b v) =
      Work.EKLComp.winJoin T P a b :=
    funext fun v => (Work.EKLComp.winJoin_eq_preimage T P a b v).symm
  rwa [hfun] at h

end Work.Misiurewicz
