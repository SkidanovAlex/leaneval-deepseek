import Mathlib
import Submission.Work.WilG4c.StepHigherDefs

namespace Work.WilG4c

/-- Every list of elements of `Fin (n+1)` is a permutation of `j` copies of `0` followed by
the `Fin.succ`-image of a list of elements of `Fin n`, with the count `j` chosen so that the
total length is preserved. -/
theorem exists_canonical_perm_aux {n : ℕ} (l : List (Fin (n + 1))) :
    ∃ (j : ℕ) (M : List (Fin n)), j + M.length = l.length ∧
      l.Perm (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) := by
  induction l with
  | nil => exact ⟨0, [], rfl, List.Perm.refl _⟩
  | cons a t ih =>
      obtain ⟨j, M, hlen, hperm⟩ := ih
      by_cases h : a = 0
      · refine ⟨j + 1, M, ?_, ?_⟩
        · simp only [List.length_cons] at hlen ⊢
          omega
        · rw [List.replicate_succ, List.cons_append, h]
          exact List.Perm.cons 0 hperm
      · refine ⟨j, M ++ [Fin.pred a h], ?_, ?_⟩
        · have h1 : (M ++ [Fin.pred a h]).length = M.length + 1 := by simp
          simp only [List.length_cons, h1] at hlen ⊢
          omega
        · have hsucc : Fin.succ (Fin.pred a h) = a := Fin.succ_pred a h
          rw [List.map_append, List.map_singleton, hsucc, ← List.append_assoc]
          refine (List.Perm.cons a hperm).trans ?_
          simpa using (List.perm_append_comm (l₁ := [a])
            (l₂ := List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ))

theorem exists_canonical_perm {n m : ℕ} (v : Fin m → Fin (n + 1)) :
    ∃ (j : ℕ) (M : List (Fin n)), j + M.length = m ∧
      (List.ofFn v).Perm (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) := by
  obtain ⟨j, M, hlen, hperm⟩ := exists_canonical_perm_aux (List.ofFn v)
  rw [List.length_ofFn] at hlen
  exact ⟨j, M, hlen, hperm⟩

end Work.WilG4c
