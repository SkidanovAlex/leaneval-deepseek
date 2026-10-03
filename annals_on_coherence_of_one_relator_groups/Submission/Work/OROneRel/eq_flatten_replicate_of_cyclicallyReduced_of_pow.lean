import Mathlib
import Submission.Work.OROneRel.exists_common_power

namespace Work.OROneRel

universe u

/-- A word of the shape `c ++ M ++ invRev c` with `c ≠ []` is never cyclically reduced: its first
letter is the head of `c` and its last letter is the inverse of that same head, so the two cancel. -/
theorem not_isCyclicallyReduced_append_invRev {α : Type u} {M c : List (α × Bool)} (hc : c ≠ []) :
    ¬ FreeGroup.IsCyclicallyReduced (c ++ M ++ FreeGroup.invRev c) := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hc
  intro hcyc
  have hhead : ((x :: xs) ++ M ++ FreeGroup.invRev (x :: xs)).head? = some x := by simp
  have hlast : ((x :: xs) ++ M ++ FreeGroup.invRev (x :: xs)).getLast? = some (x.1, !x.2) := by
    have hq : FreeGroup.invRev [x] = [(x.1, !x.2)] := by simp [FreeGroup.invRev]
    rw [FreeGroup.invRev_cons, hq]
    have hassoc : (x :: xs) ++ M ++ (FreeGroup.invRev xs ++ [(x.1, !x.2)])
        = ((x :: xs) ++ M ++ FreeGroup.invRev xs) ++ [(x.1, !x.2)] := by
      simp only [List.append_assoc]
    rw [hassoc, List.getLast?_concat]
  have hb : x ∈ ((x :: xs) ++ M ++ FreeGroup.invRev (x :: xs)).head? := by
    rw [hhead]; exact Option.mem_def.mpr rfl
  have ha : (x.1, !x.2) ∈ ((x :: xs) ++ M ++ FreeGroup.invRev (x :: xs)).getLast? := by
    rw [hlast]; exact Option.mem_def.mpr rfl
  have hcancel := hcyc.2 _ ha _ hb rfl
  rcases x with ⟨y, b⟩
  cases b <;> simp at hcancel

/-- If the reduced word `G` is cyclically reduced and represents a `k`-th power (`k ≥ 2`) in the
free group, then `G` is literally the `k`-fold concatenation of a single block.

The point is that the cyclic reduction of the reduced word of `U ^ k` is
`conjugator w ++ (reduceCyclically w)^k ++ invRev (conjugator w)` with `w = U.toWord`; since `G` is
already reduced this is an equality of words, and since `G` is in addition cyclically reduced the
conjugating prefix `conjugator w` has to be empty (otherwise the first and last letters of `G`
would cancel). -/
theorem eq_flatten_replicate_of_cyclicallyReduced_of_pow {α : Type u} {G : List (α × Bool)}
    (hred : FreeGroup.IsReduced G) (hcyc : FreeGroup.IsCyclicallyReduced G)
    {U : FreeGroup α} {k : ℕ} (hk : 2 ≤ k) (h : FreeGroup.mk G = U ^ k) :
    ∃ A : List (α × Bool), G = (List.replicate k A).flatten := by
  classical
  have hk0 : k ≠ 0 := by omega
  refine ⟨FreeGroup.reduceCyclically (FreeGroup.toWord U), ?_⟩
  have hstep : G = FreeGroup.reduceCyclically.conjugator (FreeGroup.toWord U) ++
      (List.replicate k (FreeGroup.reduceCyclically (FreeGroup.toWord U))).flatten ++
      FreeGroup.invRev (FreeGroup.reduceCyclically.conjugator (FreeGroup.toWord U)) := by
    have h1 : FreeGroup.toWord (FreeGroup.mk G) = FreeGroup.toWord (U ^ k) :=
      congrArg FreeGroup.toWord h
    rw [FreeGroup.toWord_mk, hred.reduce_eq, FreeGroup.toWord_pow,
      FreeGroup.reduceCyclically.reduce_flatten_replicate FreeGroup.isReduced_toWord k,
      if_neg hk0] at h1
    exact h1
  have hc : FreeGroup.reduceCyclically.conjugator (FreeGroup.toWord U) = [] := by
    by_contra hcne
    refine (not_isCyclicallyReduced_append_invRev (M :=
      (List.replicate k (FreeGroup.reduceCyclically (FreeGroup.toWord U))).flatten) hcne) ?_
    rw [← hstep]
    exact hcyc
  rw [hstep, hc]
  simp

end Work.OROneRel
