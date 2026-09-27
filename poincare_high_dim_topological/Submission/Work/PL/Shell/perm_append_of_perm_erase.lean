import Mathlib
import Submission.Work.PL.Shell.Basic

namespace Work.PL.Shell

/-- Two `Nodup` lists with the same `toFinset` are permutations; consequently if `l` is a
permutation of `(τ.erase v).toList` and `v ∈ τ`, then appending `v` to `l` yields a
permutation of `τ.toList`. -/
theorem perm_append_of_perm_erase {N : ℕ} {τ : Finset (PL.E N)} {v : PL.E N} (hv : v ∈ τ)
    {l : List (PL.E N)} (hl : l.Perm (τ.erase v).toList) : (l ++ [v]).Perm τ.toList := by
  classical
  -- `l` is a nodup enumeration of `τ.erase v`.
  have hfin : l.toFinset = τ.erase v := by
    rw [List.toFinset_eq_of_perm _ _ hl, Finset.toList_toFinset]
  have hvnl : v ∉ l := by
    intro hmem
    exact Finset.notMem_erase v τ (hfin ▸ List.mem_toFinset.mpr hmem)
  have hnodup : (l ++ [v]).Nodup := by
    rw [List.nodup_append']
    refine ⟨hl.nodup_iff.mpr (Finset.nodup_toList _), by simp, ?_⟩
    intro a ha ha'
    rw [List.mem_singleton] at ha'
    subst ha'
    exact hvnl ha
  -- Its `toFinset` is `τ`, matching that of `τ.toList`.
  refine List.perm_of_nodup_nodup_toFinset_eq hnodup (Finset.nodup_toList τ) ?_
  rw [List.toFinset_append, hfin, Finset.toList_toFinset]
  simp [Finset.insert_erase hv]

end Work.PL.Shell
