import Mathlib

namespace Work.WilE3.Frame

theorem mem_take_finRange_lt {k : ℕ} (l : Fin k) {x : Fin k} (hx : x ∈ (List.finRange k).take l.val) :
    (x : ℕ) < l.val := by
  have hx' : x ∈ List.finRange k := (List.take_subset l.val (List.finRange k)) hx
  rw [List.mem_take_iff_idxOf_lt hx', List.idxOf_finRange] at hx
  exact hx

end Work.WilE3.Frame
