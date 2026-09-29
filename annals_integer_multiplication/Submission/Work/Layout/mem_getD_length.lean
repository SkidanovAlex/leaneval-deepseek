import Mathlib
import Submission.Work.Layout.chunksOfDefs

namespace Work.Layout

theorem mem_getD_length {ch : List (List HvdH.Val)} {m : ℕ}
    (hlen : ∀ i, i < ch.length → (ch.getD i ([] : List HvdH.Val)).length = m) :
    ∀ c ∈ ch, c.length = m := by
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
  rw [← hlen i hi, List.getD_eq_getElem ch ([] : List HvdH.Val) hi]

end Work.Layout
