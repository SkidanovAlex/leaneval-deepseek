import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Nat

namespace Commons.Combinatorics.Finset

theorem card_le_mul_card_image_succAbove (d : ℕ) {α : Type*} [Fintype α] [DecidableEq α]
    (j : Fin (d+1)) (T : Finset (Fin (d+1) → α)) :
    T.card ≤ (T.image (fun x => fun k : Fin d => x (Fin.succAbove j k))).card * Fintype.card α := by
  classical
  rw [mul_comm]
  refine Finset.card_le_mul_card_image T (Fintype.card α) ?_
  intro b _
  let S : Finset (Fin (d+1) → α) :=
    T.filter (fun x => (fun k : Fin d => x (j.succAbove k)) = b)
  have hS : S.card ≤ Fintype.card α := by
    rw [← Finset.card_univ (α := α)]
    refine Finset.card_le_card_of_injOn (fun x => x j) ?_ ?_
    · intro x _
      exact Finset.mem_univ _
    · intro x hx y hy hxy
      have hx2 : (fun k : Fin d => x (j.succAbove k)) = b :=
        (Finset.mem_filter.mp (show x ∈ S from hx)).2
      have hy2 : (fun k : Fin d => y (j.succAbove k)) = b :=
        (Finset.mem_filter.mp (show y ∈ S from hy)).2
      funext i
      by_cases hi : i = j
      · subst hi; exact hxy
      · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq_iff.mpr hi
        rw [← hk]
        rw [congrFun hx2 k, congrFun hy2 k]
  simpa [S] using hS

end Commons.Combinatorics.Finset