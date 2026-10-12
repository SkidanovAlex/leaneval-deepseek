import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB1.Defs
import Submission.Work.SlotWord.chiSmallB_support_mem_dlBox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

theorem nCountB_slotComb_eq {M : ℕ} (hM : 1 ≤ M) {L d : ℝ} (hL : 0 < L) (hd : 0 < d)
    {N : ℕ} (u : EuclideanSpace ℝ (Fin 3)) (S : Finset (Fin N))
    (z : Work.PerSector.SlotIn N S → EuclideanSpace ℝ (Fin 3))
    (y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))
    (hz : ∀ i : Work.PerSector.SlotIn N S, z i ∈ Submission.BoseGases.dlBox L d u)
    (hy : ∀ j : Work.PerSector.SlotOut N S, y j ∉ Submission.BoseGases.dlBox L d u) :
    Work.BoseFixB1.nCountB M L d u (Work.PerSector.slotComb S z y)
      = ∑ i : Work.PerSector.SlotIn N S, (Submission.BoseGases.chiSmallB M L d u (z i)) ^ 2 := by
  rw [Work.BoseFixB1.nCountB]
  -- every slot outside `S` carries an outside coordinate, where the cutoff vanishes
  have hzero : ∀ j ∈ (Finset.univ : Finset (Fin N)), j ∉ S →
      (Submission.BoseGases.chiSmallB M L d u (Work.PerSector.slotComb S z y j)) ^ 2 = 0 := by
    intro j _ hj
    have h : Submission.BoseGases.chiSmallB M L d u (Work.PerSector.slotComb S z y j) = 0 := by
      by_contra hne
      have hmem := Work.SlotWord.chiSmallB_support_mem_dlBox hM hL hd hne
      have hjeq : Work.PerSector.slotComb S z y j = y ⟨j, hj⟩ := by
        rw [Work.PerSector.slotComb_apply, dif_neg hj]
      rw [hjeq] at hmem
      exact hy ⟨j, hj⟩ hmem
    rw [h]; ring
  rw [(Finset.sum_subset (Finset.subset_univ S) hzero).symm]
  rw [Finset.sum_subtype S (fun x => Iff.rfl)
      (fun i => (Submission.BoseGases.chiSmallB M L d u (Work.PerSector.slotComb S z y i)) ^ 2)]
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [Work.PerSector.slotComb_apply, dif_pos a.2]

end Work.BoseB1Cube
