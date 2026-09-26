import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

open Set

namespace Commons.Analysis.RealIntervals

/-- A point `c` strictly inside `(0,1)` that is the right endpoint of a
left interval `(p, c)` lies in the closure (in ℝ) of `(p, c) ∩ (0,1)`
whenever `p < c`: points just below `c` (within `(0,1)`) belong to the
interval.  (The `∩ (0,1)` makes the set sit inside the open unit
interval, as the coordinate strip of an arc chart does.) -/
theorem mem_closure_left_interval {p c : ℝ} (hpc : p < c) (hc0 : 0 < c)
    (hc1 : c < 1) : c ∈ closure (Set.Ioo p c ∩ Set.Ioo (0 : ℝ) 1) := by
  let m : ℝ := max p 0
  have hmc : m < c := by
    dsimp [m]
    exact max_lt hpc hc0
  have hsub : Set.Ioo m c ⊆ Set.Ioo p c ∩ Set.Ioo (0 : ℝ) 1 := by
    intro x hx
    rcases Set.mem_Ioo.mp hx with ⟨hmx, hxc⟩
    have hpmax : p < x ∧ (0 : ℝ) < x := max_lt_iff.mp (by simpa [m] using hmx)
    have hx1 : x < 1 := lt_trans hxc hc1
    exact ⟨⟨hpmax.1, hxc⟩, ⟨hpmax.2, hx1⟩⟩
  have hccl : c ∈ closure (Set.Ioo m c) := by
    rw [closure_Ioo (ne_of_lt hmc)]
    exact ⟨le_of_lt hmc, le_rfl⟩
  exact closure_mono hsub hccl

end Commons.Analysis.RealIntervals