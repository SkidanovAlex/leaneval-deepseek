import Mathlib

namespace Work.Transform

/-- For `t ≥ 2`, the binary size of `t` is at least `2`: `t < 2 ^ t.size` and `t ≥ 2`
rule out `t.size ≤ 1`. -/
theorem size_ge_two {t : ℕ} (h : 2 ≤ t) : 2 ≤ t.size := by
  by_contra hc
  have hle : t.size ≤ 1 := by omega
  have hlt : t < 2 := by
    simpa using (Nat.size_le.mp hle)
  omega

theorem ztpBsz (l : List ℕ) :
    ((l.filter (fun t => 2 ≤ t)).map Nat.size).sum ≤
      2 * ((l.filter (fun t => 2 ≤ t)).map (fun t => t.size - 1)).sum := by
  set m := l.filter (fun t => 2 ≤ t) with hm
  have hstep : (m.map Nat.size).sum ≤ (m.map (fun t => 2 * (t.size - 1))).sum := by
    apply List.sum_le_sum
    intro t ht
    have h2 : 2 ≤ t := by
      have := (List.mem_filter.mp ht).2
      simpa using this
    have hs : 2 ≤ t.size := size_ge_two h2
    omega
  have hmul : (m.map (fun t => 2 * (t.size - 1))).sum = 2 * (m.map (fun t => t.size - 1)).sum :=
    List.sum_map_mul_left m (fun t => t.size - 1) 2
  rw [hmul] at hstep
  exact hstep

end Work.Transform
