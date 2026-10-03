import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.letters_closure_iff

namespace Work.OROneRel

universe u

/-- A nontrivial relator whose letters generate at most one generator is a power of that
generator, hence terminal.  Combining this with `IsTerminalRelator` gives the contrapositive
of the statement below. -/
private theorem isTerminalRelator_of_letters_subset_singleton {α : Type u} {u : FreeGroup α}
    {x : α} (hsub : relatorLetters u ⊆ ({x} : Set α)) : IsTerminalRelator u := by
  classical
  have hu : u ∈ Subgroup.closure (FreeGroup.of '' ({x} : Set α)) :=
    (letters_closure_iff u _).2 hsub
  rw [Set.image_singleton] at hu
  obtain ⟨m, hm⟩ := Subgroup.mem_closure_singleton.mp hu
  rcases eq_or_ne m 0 with hm0 | hm0
  · exact Or.inl (by rw [← hm, hm0]; simp)
  · exact Or.inr ⟨x, m, hm0, hm.symm⟩

set_option linter.unusedVariables false in
theorem two_letters_of_not_terminal {α : Type u} {u : FreeGroup α}
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u) (h1 : u ≠ 1)
    (hnt : ¬ Work.OROneRel.IsTerminalRelator u) :
    ∃ x : α, x ∈ Work.OROneRel.relatorLetters u ∧
      ∃ y : α, y ∈ Work.OROneRel.relatorLetters u ∧ x ≠ y := by
  classical
  by_contra h
  push Not at h
  rcases Set.eq_empty_or_nonempty (relatorLetters u) with hem | ⟨x, hx⟩
  · exfalso
    have hmem : u ∈ Subgroup.closure (FreeGroup.of '' (∅ : Set α)) := by
      rw [letters_closure_iff]
      intro a ha
      rw [hem] at ha
      exact (Set.notMem_empty a) ha
    have hu1 : u = 1 := by simpa using hmem
    exact h1 hu1
  · exact hnt (isTerminalRelator_of_letters_subset_singleton fun y hy => (h x hx y hy).symm)

end Work.OROneRel
