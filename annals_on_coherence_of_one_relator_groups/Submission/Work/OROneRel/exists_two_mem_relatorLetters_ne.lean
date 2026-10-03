import Mathlib
import Submission.Work.OROneRel.MagnusRewrite
import Submission.Work.OROneRel.isReduced_replicate_of_fst_eq

namespace Work.OROneRel

universe u

theorem exists_two_mem_relatorLetters_ne {α : Type u} (u : FreeGroup α) (hn : 2 ≤ Work.OROneRel.relatorNorm u) (hu : ¬ Work.OROneRel.IsProperPower u) : ∃ x : α, x ∈ Work.OROneRel.relatorLetters u ∧ ∃ y : α, y ∈ Work.OROneRel.relatorLetters u ∧ x ≠ y := by
  classical
  by_contra h
  push Not at h
  -- `h : ∀ x ∈ relatorLetters u, ∀ y ∈ relatorLetters u, x = y`
  have hwlen : 2 ≤ (FreeGroup.toWord u).length := by
    simpa only [relatorNorm, FreeGroup.norm] using hn
  have hwne : FreeGroup.toWord u ≠ [] := by
    intro hc
    rw [hc] at hwlen
    simp at hwlen
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ hwne
  obtain ⟨c, hc⟩ := isReduced_replicate_of_fst_eq (A := FreeGroup.toWord u)
    FreeGroup.isReduced_toWord
    (fun q hq => h q.1 ⟨q.2, hq⟩ p.1 ⟨p.2, hp⟩)
  refine hu ⟨FreeGroup.mk [c], (FreeGroup.toWord u).length, hwlen, ?_⟩
  conv_lhs => rw [← FreeGroup.mk_toWord (x := u), hc]
  rw [FreeGroup.pow_mk, List.flatten_replicate_singleton]

end Work.OROneRel
