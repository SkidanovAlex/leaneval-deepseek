import Mathlib

namespace Work.Transform

/-- For `t ≥ 2` we have `2 ≤ t.size`, whence `t.size + 2 ≤ 4 * (t.size - 1)`. -/
private lemma size_add_two_le_four_mul (t : ℕ) (h : 2 ≤ t) :
    t.size + 2 ≤ 4 * (t.size - 1) := by
  have hs : 2 ≤ t.size := by
    have h1 : ¬ t.size ≤ 1 := by
      intro hc
      have h2 : t < 2 ^ 1 := Nat.size_le.mp hc
      omega
    omega
  omega

theorem ztpSisz (l : List ℕ) :
    ((l.filter (fun t => 2 ≤ t)).map (fun t => t.size + 2)).sum ≤
      4 * ((l.filter (fun t => 2 ≤ t)).map (fun t => t.size - 1)).sum := by
  calc
    ((l.filter (fun t => 2 ≤ t)).map (fun t => t.size + 2)).sum
        ≤ ((l.filter (fun t => 2 ≤ t)).map (fun t => 4 * (t.size - 1))).sum := by
          apply List.sum_le_sum
          intro t ht
          exact size_add_two_le_four_mul t (by simpa using (List.mem_filter.mp ht).2)
    _ = 4 * ((l.filter (fun t => 2 ≤ t)).map (fun t => t.size - 1)).sum :=
          List.sum_map_mul_left _ _ 4

end Work.Transform
