import Mathlib
import Submission.Work.PL.Generic.Hull

namespace Work.Generic

theorem getElem_notMem_take_of_le {α : Type*} {l : List α} (hl : l.Nodup) {j k : ℕ}
    (hj : j ≤ k) (hk : k < l.length) : l[k] ∉ l.take j := by
  intro hmem
  obtain ⟨i, hi, hik⟩ := List.mem_iff_getElem.mp hmem
  have hi' : i < l.length :=
    lt_of_lt_of_le hi (by rw [List.length_take]; exact Nat.min_le_right _ _)
  have hij : i < j :=
    lt_of_lt_of_le hi (by rw [List.length_take]; exact Nat.min_le_left _ _)
  have hli : l[i] = l[k] := (List.getElem_take (h := hi)).symm.trans hik
  have hik_eq : i = k := (hl.getElem_inj_iff (hi := hi') (hj := hk)).mp hli
  omega

end Work.Generic
