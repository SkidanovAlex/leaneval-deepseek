import Mathlib
import Submission.Work.EKLComp.Entropy

namespace Work.EKLComp

open MeasureTheory
open Work.EKLContract

/-- The `(M*(m+1))`-fold join along `T` refines the `M`-fold join along `T^[m+1]`: the latter
records `P` at the times `0, m+1, 2(m+1), …, (M-1)(m+1)`, all of which are times seen by the
former.  Indexing the words of the former by `Fin (M*(m+1)) → Fin P.n`, the reindexing map is
`v ↦ (k ↦ v (k*(m+1)))`. -/
theorem joinSets_iterate_subset {X : Type} [MeasurableSpace X] (T : X → X) (P : FinPart X)
    (m M : ℕ) (v : Fin (M * (m + 1)) → Fin P.n) :
    joinSets T P (M * (m + 1)) v ⊆
      joinSets (T^[m+1]) P M
        (fun k : Fin M => v ⟨k.val * (m + 1),
          Nat.mul_lt_mul_of_pos_right k.isLt (Nat.succ_pos m)⟩) := by
  intro x hx
  simp only [joinSets, Set.mem_iInter, Set.mem_preimage] at hx ⊢
  intro k
  have h1 := hx ⟨k.val * (m + 1), Nat.mul_lt_mul_of_pos_right k.isLt (Nat.succ_pos m)⟩
  have h2 : (T^[m+1])^[k.val] x = T^[k.val * (m + 1)] x := by
    rw [← Function.iterate_mul T (m + 1) k.val, Nat.mul_comm]
  rwa [h2]

theorem joinSets_iterate_le {X : Type} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] {T : X → X} (hT : Measurable T)
    (P : Work.EKLContract.FinPart X) (m M : ℕ) :
    Work.EKLContract.Hfam μ (Work.EKLContract.joinSets (T^[m+1]) P M)
      ≤ Work.EKLContract.Hfam μ (Work.EKLContract.joinSets T P (M * (m+1))) := by
  classical
  refine Core.Hfam_mono μ (Core.joinSets_isMPart (hT.iterate (m+1)) P M)
    (Core.joinSets_isMPart hT P (M * (m + 1)))
    (fun v : Fin (M * (m + 1)) → Fin P.n => fun k : Fin M => v ⟨k.val * (m + 1),
      Nat.mul_lt_mul_of_pos_right k.isLt (Nat.succ_pos m)⟩) ?_
  intro v
  exact joinSets_iterate_subset T P m M v

end Work.EKLComp
