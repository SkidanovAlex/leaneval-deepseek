import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.MagnusRewrite
import Submission.Work.OROneRel.exists_hnnStepCore

/-!
# The exponent sum of a generator transports along an injective relabelling

`Work.OROneRel.eps_map_of_injective` : the exponent sum of the generator `t` in a word
`v ∈ F(β)` equals the exponent sum of the generator `f t` in the image of `v` under an injective
relabelling `f : β → γ` of the generators.

The proof is a reduction to a statement about words: an injective relabelling creates no
cancellations, so the reduced word of `FreeGroup.map f v` is the image of the reduced word of `v`
(`Work.OROneRel.toWord_map_of_injective_classical`), and the exponent sum is computed letterwise.
-/

namespace Work.OROneRel

universe u

/-- A letter not equal to `t` does not contribute to the exponent sum. -/
private theorem letterSign_map {β γ : Type*} (f : β → γ) (hf : Function.Injective f)
    (t : β) (p : β × Bool) :
    Work.OROneRel.letterSign (f t) (f p.1, p.2) = Work.OROneRel.letterSign t p := by
  obtain ⟨a, b⟩ := p
  by_cases h : a = t
  · simp [Work.OROneRel.letterSign, h]
  · have h' : ¬ (f a = f t) := fun hh => h (hf.eq_iff.mp hh)
    simp only [Work.OROneRel.letterSign, h, h', ↓reduceIte]

/-- The exponent sum of a word is the sum of the letter signs. -/
private theorem wordEps_eq_map_letterSign {α : Type*} (t : α) (L : List (α × Bool)) :
    Work.OROneRel.wordEps t L = (L.map (Work.OROneRel.letterSign t)).sum := by
  unfold Work.OROneRel.wordEps Work.OROneRel.letterSign
  rfl

/-- The exponent sum is computed letterwise, so an injective relabelling of the generators
preserves it. -/
private theorem wordEps_map {β γ : Type*} (f : β → γ) (hf : Function.Injective f)
    (t : β) (L : List (β × Bool)) :
    Work.OROneRel.wordEps (f t) (L.map (fun p => (f p.1, p.2))) = Work.OROneRel.wordEps t L := by
  classical
  rw [wordEps_eq_map_letterSign (f t), wordEps_eq_map_letterSign t]
  induction L with
  | nil => simp
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    simp only [List.map_cons, List.sum_cons]
    rw [ih, letterSign_map f hf t (a, b)]

theorem eps_map_of_injective {β γ : Type*} (f : β → γ) (hf : Function.Injective f)
    (t : β) (v : FreeGroup β) :
    Work.OROneRel.eps (f t) (FreeGroup.map f v) = Work.OROneRel.eps t v := by
  classical
  unfold Work.OROneRel.eps
  rw [Work.OROneRel.toWord_map_of_injective_classical f hf v]
  exact wordEps_map f hf t v.toWord

end Work.OROneRel
