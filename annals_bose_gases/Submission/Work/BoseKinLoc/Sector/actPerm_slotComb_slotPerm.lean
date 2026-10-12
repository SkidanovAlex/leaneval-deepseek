import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseKinLoc.Sector.slotPermDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseKinLoc.Sector

theorem actPerm_slotComb_slotPerm {N : ℕ} (S : Finset (Fin N)) (σ : Equiv.Perm (Fin S.card))
    (z : Work.PerSector.SlotIn N S → EuclideanSpace ℝ (Fin 3))
    (y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.actPerm N (Work.BoseKinLoc.Sector.slotPerm S σ)
        (Work.PerSector.slotComb S z y)
      = Work.PerSector.slotComb S (fun i => z (Work.BoseKinLoc.Sector.slotPermIn S σ i)) y := by
  funext i
  simp only [Submission.BoseGases.actPerm]
  rw [Work.PerSector.slotComb_apply, Work.PerSector.slotComb_apply]
  by_cases hi : i ∈ S
  · rw [dif_pos hi, slotPerm_apply_of_mem σ hi, dif_pos (slotPermIn S σ ⟨i, hi⟩).2]
  · rw [dif_neg hi, slotPerm_apply_of_notMem σ hi, dif_neg hi]

end Work.BoseKinLoc.Sector
