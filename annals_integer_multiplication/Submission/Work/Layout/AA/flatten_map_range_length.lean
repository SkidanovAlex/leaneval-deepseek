import Mathlib

namespace Work.Layout.AA

theorem flatten_map_range_length {α : Type*} (m C1 : ℕ) (row : ℕ → List α)
    (hlen : ∀ j, j < m → (row j).length = C1) :
    (((List.range m).map row).flatten).length = m * C1 := by
  rw [List.length_flatten, List.map_map]
  have hmap : (List.range m).map (List.length ∘ row) = (List.range m).map (fun _ => C1) := by
    apply List.map_congr_left
    intro j hj
    exact hlen j (List.mem_range.mp hj)
  rw [hmap, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]

end Work.Layout.AA
