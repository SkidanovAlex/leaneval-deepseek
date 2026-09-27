import Mathlib
import Submission.Work.EKLC6Core.CellWDefs

namespace Work.EKLC6Core

/-- Inside the cell `Q k` the clipped generator `genCW S O k m` is the `mkX`-image of the
intersection of the lifted ball `lifted (δ k) (g k)` with the `U`-saturation `satU U (O m)`; the
lift `liftW S k y` is the unique element of the lifted ball mapping to `y`, so
`y ∈ genCW S O k m` holds exactly when `liftW S k y` already lies in `satU U (O m)`. -/
theorem genCW_mem_iff {μ : MeasureTheory.Measure Work.EKLContract.X3}
    {U : Subgroup Work.EKLContract.SL3} (S : Work.EKLC6Core.CellW μ U)
    (O : ℕ → Set Work.EKLContract.SL3) (k m : ℕ) {y : Work.EKLContract.X3} (hy : y ∈ S.Q k) :
    y ∈ Work.EKLC6Core.genCW S O k m ↔
      Work.EKLC6Core.liftW S k y ∈ Work.EKLC6Core.satU U (O m) := by
  constructor
  · intro h
    obtain ⟨⟨w, ⟨hwsat, hwl⟩, hwz⟩, -⟩ := h
    have hw : w = liftW S k y :=
      mkX_inj_liftedW S k hwl (liftW_mem S k hy)
        (by rw [hwz, mkX_liftW S k hy])
    rwa [hw] at hwsat
  · intro h
    exact ⟨⟨liftW S k y, ⟨h, liftW_mem S k hy⟩, mkX_liftW S k hy⟩, hy⟩

end Work.EKLC6Core
