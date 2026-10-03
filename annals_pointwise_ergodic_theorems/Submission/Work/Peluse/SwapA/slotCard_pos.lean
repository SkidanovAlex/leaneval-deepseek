import Mathlib
import Submission.Work.Peluse.Holds.SwapDefs

namespace Work.Peluse.SwapA

/-- The KKL slot set is nonempty for every `s ≥ 1`: the triple with pivot `j = s-1`,
`ε ≡ 1`, `ε' ≡ 0` satisfies both defining conditions. -/
theorem slotCard_pos : ∀ s : ℕ, 1 ≤ s → 1 ≤ Work.Peluse.LadderP.Swap.slotCard s := by
  intro s hs
  have hmem : (⟨s - 1, by omega⟩, fun _ => true, fun _ => false) ∈
      Work.Peluse.LadderP.Swap.slotSet s := by
    rw [Work.Peluse.LadderP.Swap.slotSet]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro r hr
      have hlt := r.isLt
      omega
    · intro r _
      trivial
  have hpos : 0 < Work.Peluse.LadderP.Swap.slotCard s := by
    rw [Work.Peluse.LadderP.Swap.slotCard]
    exact Finset.card_pos.mpr ⟨_, hmem⟩
  omega

end Work.Peluse.SwapA
