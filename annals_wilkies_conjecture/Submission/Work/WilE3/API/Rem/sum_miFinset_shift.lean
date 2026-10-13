import Mathlib
import Submission.Work.WilE3.API.RemDefs

namespace Work.WilE3.API.Rem

theorem sum_miFinset_shift {k : ℕ} (F : (Fin k → ℕ) → ℝ) (N : ℕ) (i : Fin k) :
    ∑ m ∈ (Work.WilE3.API.miFinset k (N + 1)).filter (fun m => 0 < m i),
        F (Work.WilE3.API.miS m i)
      = ∑ n ∈ Work.WilE3.API.miFinset k N, F n := by
  -- The map `m ↦ miS m i` is a bijection from the multi-indices of total degree
  -- `≤ N + 1` with positive `i`-th coordinate onto those of total degree `≤ N`,
  -- with inverse `n ↦ n + e_i`.
  refine Finset.sum_bij' (fun m _ => Work.WilE3.API.miS m i)
    (fun n _ => n + Work.WilE3.API.eMI i) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    exact Work.WilE3.API.miS_mem_miFinset (Finset.mem_filter.mp ha).1
      (Finset.mem_filter.mp ha).2
  · intro a ha
    rw [Finset.mem_filter]
    exact ⟨Work.WilE3.API.eMI_mem_miFinset ha, by simp [Work.WilE3.API.eMI_apply]⟩
  · intro a ha
    exact Work.WilE3.API.miS_add_eMI (Finset.mem_filter.mp ha).2
  · intro a ha
    exact Work.WilE3.API.miS_eMI a i
  · intro a ha
    rfl

end Work.WilE3.API.Rem
