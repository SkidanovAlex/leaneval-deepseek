import Mathlib
import Submission.Work.Cohomology.EZShuffle

namespace Work.Cohomology

/-- `shuffleId p q` is the set of `i : Fin (p+q)` with `i.val < p`; it is the image of
`Fin p` under the inclusion `Fin p ↪ Fin (p+q)`, hence has `p` elements. -/
theorem shuffleId_card (p q : ℕ) : (Work.Cohomology.shuffleId p q).card = p := by
  rw [Work.Cohomology.shuffleId]
  have h : (Finset.univ.filter (fun i : Fin (p + q) => i.val < p))
      = (Finset.univ : Finset (Fin p)).map (Fin.castLEEmb (Nat.le_add_right p q)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro hx
      exact ⟨⟨x.val, hx⟩, rfl⟩
    · rintro ⟨y, _hy, rfl⟩
      exact y.isLt
  rw [h, Finset.card_map, Finset.card_univ, Fintype.card_fin]

end Work.Cohomology
