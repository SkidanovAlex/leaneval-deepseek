import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.exists_hnnStepCore

namespace Work.OROneRel

open FreeGroup

/-- The maximal reduction of a word commutes with applying an injective relabelling
of the generators.  This is the structural heart of the counting lemma: cancellation
of adjacent inverse letters is preserved exactly because the relabelling is injective. -/
theorem reduce_map_eq_map_reduce {β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (f : β → γ) (hf : Function.Injective f) (L : List (β × Bool)) :
    FreeGroup.reduce (L.map (fun p => (f p.1, p.2))) =
      (FreeGroup.reduce L).map (fun p => (f p.1, p.2)) := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨a, c⟩ := hd
    cases hred : FreeGroup.reduce tl with
    | nil =>
      have ihn : FreeGroup.reduce (tl.map (fun p => (f p.1, p.2))) =
          ([] : List (γ × Bool)) := by
        rw [ih, hred]; rfl
      simp only [List.map_cons, FreeGroup.reduce.cons, hred, ihn]
      simp
    | cons hd2 tl2 =>
      obtain ⟨y, d⟩ := hd2
      have ihn : FreeGroup.reduce (tl.map (fun p => (f p.1, p.2))) =
          (f y, d) :: tl2.map (fun p => (f p.1, p.2)) := by
        rw [ih, hred]; rfl
      simp only [List.map_cons, FreeGroup.reduce.cons, hred, ihn]
      rw [apply_ite (fun (l : List (β × Bool)) => l.map (fun p => (f p.1, p.2)))]
      simp only [List.map_cons]
      by_cases h : a = y ∧ c = !d
      · have h' : f a = f y ∧ c = !d := ⟨congrArg f h.1, h.2⟩
        rw [if_pos h, if_pos h']
      · have h' : ¬(f a = f y ∧ c = !d) := fun ⟨h1, h2⟩ => h ⟨hf h1, h2⟩
        rw [if_neg h, if_neg h']

theorem count_toWord_map_of_injective {β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (f : β → γ) (hf : Function.Injective f) (v : FreeGroup β) (x : β) (b : Bool) :
    (FreeGroup.toWord (FreeGroup.map f v)).count (f x, b) =
      (FreeGroup.toWord v).count (x, b) := by
  have hg : Function.Injective (fun p : β × Bool => (f p.1, p.2)) := by
    intro p q h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (hf h.1) h.2
  conv_lhs => rw [← FreeGroup.mk_toWord (x := v)]
  rw [FreeGroup.map.mk, FreeGroup.toWord_mk,
    reduce_map_eq_map_reduce f hf (FreeGroup.toWord v)]
  rw [List.count_map_of_injective _ _ hg (x, b), FreeGroup.reduce_toWord]

end Work.OROneRel
