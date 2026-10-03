import Mathlib
import Submission.Work.OROneRel.magnus_step_root

/-!
# The Magnus root of a cyclically reduced relator is cyclically reduced

For a cyclically reduced relator `u : FreeGroup α` of exponent sum zero in a generator `t`, the
Magnus rewriting `mmW t u` is cyclically reduced, and the `l`-fold concatenation of its transported
copies is the Magnus rewriting of `u ^ l` (`Work.OROneRel.mmWL_pow_trans`).  Since the latter is
cyclically reduced, so is a single copy; this gives the lemma below.

The auxiliary list lemma `FreeGroup.IsCyclicallyReduced.of_flatten_replicate` is the converse of
Mathlib's `FreeGroup.IsCyclicallyReduced.flatten_replicate`: a single block whose repeated
concatenation is cyclically reduced is itself cyclically reduced.
-/

universe u

namespace FreeGroup

variable {α : Type u}

/-- Converse of `FreeGroup.IsCyclicallyReduced.flatten_replicate`: if the concatenation of `n ≥ 1`
copies of a word is cyclically reduced, then the word itself is cyclically reduced.  Indeed the word
is an infix of the concatenation (so it is reduced), and its head and last letter are those of the
concatenation (`List.head?_flatten_replicate`, `List.getLast?_flatten_replicate`). -/
theorem IsCyclicallyReduced.of_flatten_replicate {L : List (α × Bool)} {n : ℕ} (hn : n ≠ 0)
    (h : FreeGroup.IsCyclicallyReduced (List.replicate n L).flatten) :
    FreeGroup.IsCyclicallyReduced L := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [List.replicate_succ, List.flatten_cons] at h
  have hlast : (L ++ (List.replicate m L).flatten).getLast? = L.getLast? := by
    rw [← List.flatten_cons, ← List.replicate_succ]
    exact List.getLast?_flatten_replicate (Nat.succ_ne_zero m) L
  have hhead : (L ++ (List.replicate m L).flatten).head? = L.head? := by
    rw [← List.flatten_cons, ← List.replicate_succ]
    exact List.head?_flatten_replicate (Nat.succ_ne_zero m) L
  refine ⟨h.1.infix ⟨[], (List.replicate m L).flatten, by simp⟩, ?_⟩
  intro a ha b hb hab
  exact h.2 a (by rw [hlast]; exact ha) b (by rw [hhead]; exact hb) hab

end FreeGroup

namespace Work.ORLyndon

theorem isCyclicallyReducedRelator_rootW {α : Type u} [DecidableEq α] (t : α) (u : FreeGroup α) (l : ℕ)
    (hu : Work.OROneRel.IsCyclicallyReducedRelator u) (he : Work.OROneRel.eps t u = 0) (hl : 1 ≤ l) :
    Work.OROneRel.IsCyclicallyReducedRelator (Work.OROneRel.rootW t u l hu he hl) := by
  classical
  have hl0 : l ≠ 0 := by omega
  have hcyc' : Work.OROneRel.IsCyclicallyReducedRelator (u ^ l) :=
    Work.OROneRel.isCyclicallyReducedRelator_pow hu l
  have he' : Work.OROneRel.eps t (u ^ l) = 0 := by
    have h1 : Work.OROneRel.sigma t (u ^ l) = 1 := by
      rw [map_pow, (Work.OROneRel.eps_eq_zero_iff_sigma_eq_one t u).mp he, one_pow]
    exact (Work.OROneRel.eps_eq_zero_iff_sigma_eq_one t (u ^ l)).mpr h1
  have hM : FreeGroup.IsCyclicallyReduced (Work.OROneRel.mmWL t (u ^ l)) :=
    Work.OROneRel.mmWL_isCyclicallyReduced t (u ^ l) hcyc' he'
  rw [Work.OROneRel.mmWL_pow_trans t u l hu he hl] at hM
  have hL : FreeGroup.IsCyclicallyReduced
      ((Work.OROneRel.mmWL t u).map (fun q => (Work.OROneRel.mmTransFun t u l hu he hl q.1, q.2))) :=
    FreeGroup.IsCyclicallyReduced.of_flatten_replicate hl0 hM
  rw [Work.OROneRel.rootW_eq]
  rw [Work.OROneRel.IsCyclicallyReducedRelator, FreeGroup.toWord_mk, hL.1.reduce_eq]
  exact hL

end Work.ORLyndon
