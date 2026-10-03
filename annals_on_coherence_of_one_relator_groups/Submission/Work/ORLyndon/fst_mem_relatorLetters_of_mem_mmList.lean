import Mathlib
import Submission.Work.OROneRel.mmStepData_of_expsum_zero

namespace Work.ORLyndon

/-- Every decorated letter occurring in the Magnus rewriting `rewriteAux t i L` of a word `L`
comes from an actual letter of `L`: if `p` is a symbol of `rewriteAux t i L`, then the underlying
generator `p.1.1 : {a // a ≠ t}` is (as an element of `α`) the first coordinate of some letter of
`L`. -/
private lemma mem_rewriteAux_of_mem {α : Type*} (t : α) (i : ℤ) :
    ∀ {L : List (α × Bool)} {p : ({a : α // a ≠ t} × ℤ) × Bool},
      p ∈ Work.OROneRel.rewriteAux t i L → ((p.1.1 : α), p.2) ∈ L := by
  intro L p
  induction L generalizing i with
  | nil =>
      intro hp
      simp [Work.OROneRel.rewriteAux] at hp
  | cons q L ih =>
      intro hp
      obtain ⟨q1, q2⟩ := q
      by_cases h : q1 = t
      · rw [show Work.OROneRel.rewriteAux t i ((q1, q2) :: L) =
            Work.OROneRel.rewriteAux t (i + (if q2 then 1 else -1)) L
            from by simp [Work.OROneRel.rewriteAux, h]] at hp
        exact List.mem_cons_of_mem _ (ih (i + (if q2 then 1 else -1)) hp)
      · rw [show Work.OROneRel.rewriteAux t i ((q1, q2) :: L) =
            ((⟨q1, h⟩, i), q2) :: Work.OROneRel.rewriteAux t i L
            from by simp [Work.OROneRel.rewriteAux, h]] at hp
        rcases List.mem_cons.mp hp with hpq | hpt
        · rw [hpq]
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih i hpt)

theorem fst_mem_relatorLetters_of_mem_mmList {α : Type*} [DecidableEq α] (t : α) (u : FreeGroup α)
    {p : ({a : α // a ≠ t} × ℤ) × Bool} (hp : p ∈ Work.OROneRel.mmList t u) :
    (p.1.1 : α) ∈ Work.OROneRel.relatorLetters u := by
  classical
  rw [Work.OROneRel.relatorLetters, Set.mem_ofPred_eq]
  rw [Work.OROneRel.mmList, Work.OROneRel.magRew_zero_eq_rewrite] at hp
  exact ⟨p.2, mem_rewriteAux_of_mem t 0 hp⟩

end Work.ORLyndon
