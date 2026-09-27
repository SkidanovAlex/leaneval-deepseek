import Mathlib
import Submission.Work.PL.Shell.Basic

namespace Work.PL.Shell

open Set Metric Finset

theorem preUnion_eq_iUnion_take {N : ℕ} (l : List (Finset (PL.E N))) (i : ℕ) (hi : i ≤ l.length) :
    Work.PL.Shell.preUnion l i = ⋃ x ∈ (l.take i).toFinset, PL.simp x := by
  unfold preUnion
  ext y
  simp only [Set.mem_iUnion, Finset.mem_range]
  constructor
  · rintro ⟨j, hj, hy⟩
    have hjl : j < l.length := lt_of_lt_of_le hj hi
    refine ⟨l.getD j ∅, ?_, hy⟩
    rw [List.getD_eq_getElem l ∅ hjl, List.mem_toFinset, List.getElem_take' hjl hj]
    exact List.getElem_mem _
  · rintro ⟨x, hx, hy⟩
    rw [List.mem_toFinset] at hx
    obtain ⟨k, hk, hk_eq⟩ := List.getElem_of_mem hx
    have hki : k < i := by
      have h := hk; rw [List.length_take] at h; omega
    have hkl : k < l.length := by
      have h := hk; rw [List.length_take] at h; omega
    refine ⟨k, hki, ?_⟩
    rw [List.getD_eq_getElem l ∅ hkl]
    rw [show l[k] = x from (List.getElem_take (h := hk)).symm.trans hk_eq]
    exact hy

end Work.PL.Shell
