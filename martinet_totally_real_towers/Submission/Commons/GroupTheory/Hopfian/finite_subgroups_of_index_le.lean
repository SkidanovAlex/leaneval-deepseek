import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Finiteness
import Submission.Commons.GroupTheory.Hopfian.finite_subgroups_of_index

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Commons.GroupTheory.Hopfian

/-- There are finitely many finite-index subgroups of index at most `m` in a finitely
generated group: the collection is the finite union over `n ≤ m` of the (finite) sets of
subgroups of index exactly `n`. -/
theorem finite_subgroups_of_index_le {G : Type*} [Group G] [Group.FG G] (m : ℕ) :
    Finite {H : Subgroup G // H.FiniteIndex ∧ H.index ≤ m} := by
  classical
  let D := Σ n : Fin (m + 1), {H : Subgroup G // H.FiniteIndex ∧ H.index = n.val}
  let f : D → {H : Subgroup G // H.FiniteIndex ∧ H.index ≤ m} := fun X =>
    ⟨X.2.1, X.2.2.1, by
      rw [X.2.2.2]
      exact Nat.le_of_lt_succ X.1.isLt⟩
  have hfib : ∀ n : Fin (m + 1),
      Finite {H : Subgroup G // H.FiniteIndex ∧ H.index = n.val} :=
    fun n => finite_subgroups_of_index (G := G) n.val
  haveI : ∀ n : Fin (m + 1),
      Finite {H : Subgroup G // H.FiniteIndex ∧ H.index = n.val} := hfib
  have hD : Finite D := by
    dsimp [D]
    infer_instance
  refine Finite.of_surjective (α := D) (β := {H : Subgroup G // H.FiniteIndex ∧ H.index ≤ m})
    f ?_
  intro H
  refine ⟨⟨⟨H.1.index, Nat.lt_succ_of_le H.2.2⟩, ⟨H.1, H.2.1, rfl⟩⟩, ?_⟩
  dsimp [f]
