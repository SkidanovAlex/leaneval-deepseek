import Mathlib
import Submission.Work.OROneRel.FreiheitssatzDefs

namespace Work.OROneRel

universe u

/-- The product of the `Multiplicative.ofAdd`-images of a list of integers is the `ofAdd` of the
sum of those integers. -/
lemma prod_map_ofAdd {β : Type*} (L : List β) (g : β → ℤ) :
    (L.map (fun x => Multiplicative.ofAdd (g x))).prod =
      Multiplicative.ofAdd ((L.map g).sum) := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

theorem sigma_mk {α : Type u} (t : α) (L : List (α × Bool)) :
    Work.OROneRel.sigma t (FreeGroup.mk L) =
      Multiplicative.ofAdd (Work.OROneRel.sigmaList t L) := by
  classical
  have h1 : Work.OROneRel.sigma t (FreeGroup.mk L)
      = (L.map (fun x => Multiplicative.ofAdd (Work.OROneRel.letterSign t x))).prod := by
    unfold Work.OROneRel.sigma
    rw [FreeGroup.lift_mk]
    congr 1
    apply List.map_congr_left
    intro x _
    obtain ⟨a, b⟩ := x
    simp only [Work.OROneRel.letterSign]
    by_cases h : a = t
    · subst h
      cases b <;> simp
    · cases b <;> simp [h]
  rw [h1]
  unfold Work.OROneRel.sigmaList
  exact prod_map_ofAdd L (Work.OROneRel.letterSign t)

end Work.OROneRel
