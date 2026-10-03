import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.exists_hnnStepCore

namespace Work.OROneRel

/-- `relatorLetters` is computed from the reduced word `toWord`, and an injective relabelling of the
generators does not create cancellations, so it acts on the reduced word by relabelling letters
letterwise (`toWord_map_of_injective_classical`). Since `f` is injective, this letterwise
relabelling is injective on letters, which gives the stated membership equivalence. -/
theorem mem_relatorLetters_map_iff {β γ : Type*} (f : β → γ) (hf : Function.Injective f)
    (v : FreeGroup β) (y : β) :
    (y ∈ Work.OROneRel.relatorLetters v) ↔
      (f y ∈ Work.OROneRel.relatorLetters (FreeGroup.map f v)) := by
  classical
  have hw := toWord_map_of_injective_classical f hf v
  show (∃ b : Bool, (y, b) ∈ FreeGroup.toWord v) ↔
    (∃ b : Bool, (f y, b) ∈ FreeGroup.toWord (FreeGroup.map f v))
  rw [hw]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, List.mem_map.mpr ⟨(y, b), hb, rfl⟩⟩
  · rintro ⟨b, hb⟩
    obtain ⟨⟨a₁, a₂⟩, ha, hm⟩ := List.mem_map.mp hb
    simp only [Prod.mk.injEq] at hm
    exact ⟨a₂, by rw [← hf hm.1]; exact ha⟩

end Work.OROneRel
