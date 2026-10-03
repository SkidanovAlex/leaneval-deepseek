import Mathlib
import Submission.Work.ORHughesFree.Tree
import Submission.Work.ORHughesFree.Tree.permRel_nil_right

namespace Work.ORHughesFree.Tree

/-- Auxiliary predicate: each list is a singleton whose element is `Iso`-equivalent to the
element of the other (in both directions).  It is preserved by every generator of `PermRel`. -/
private def PSing (l l' : List Work.ORHughesFree.MTree) : Prop :=
  (∀ a, l = [a] → ∃ b, l' = [b] ∧ Work.ORHughesFree.Iso a b) ∧
  (∀ b, l' = [b] → ∃ a, l = [a] ∧ Work.ORHughesFree.Iso a b)

theorem permRel_singleton {l : List Work.ORHughesFree.MTree} {t : Work.ORHughesFree.MTree}
    (h : Work.ORHughesFree.PermRel l [t]) : ∃ a, l = [a] ∧ Work.ORHughesFree.Iso a t :=
  (PermRel.rec (motive_1 := fun _ _ _ => True) (motive_2 := fun l l' _ => PSing l l')
    (fun {l l'} _ _ => trivial)
    (⟨fun a ha => by simp at ha, fun b hb => by simp at hb⟩)
    (fun {x y l l'} hxy hlr _ ihlr => by
      refine ⟨?_, ?_⟩
      · intro a ha
        obtain ⟨hxa, hl⟩ := (List.cons.injEq x l a []).mp ha
        have hl' : l' = [] := by
          rw [hl] at hlr
          exact permRel_nil_right (PermRel.symm hlr)
        exact ⟨y, by rw [hl'], by rw [← hxa]; exact hxy⟩
      · intro b hb
        obtain ⟨hyb, hl'⟩ := (List.cons.injEq y l' b []).mp hb
        have hl : l = [] := by
          rw [hl'] at hlr
          exact permRel_nil_right hlr
        exact ⟨x, by rw [hl], by rw [← hyb]; exact hxy⟩)
    (fun x y l => ⟨fun a ha => by simp at ha, fun b hb => by simp at hb⟩)
    (fun l => ⟨fun a ha => ⟨a, ha, Iso.refl a⟩, fun b hb => ⟨b, hb, Iso.refl b⟩⟩)
    (fun {l l'} _ ihlr => by
      refine ⟨?_, ?_⟩
      · intro a ha
        obtain ⟨a₁, ha₁, hiso⟩ := ihlr.2 a ha
        exact ⟨a₁, ha₁, Iso.symm hiso⟩
      · intro b hb
        obtain ⟨b₁, hb₁, hiso⟩ := ihlr.1 b hb
        exact ⟨b₁, hb₁, Iso.symm hiso⟩)
    (fun {l l' l''} _ _ ihlr ihlr' => by
      refine ⟨?_, ?_⟩
      · intro a ha
        obtain ⟨b', hb', hab'⟩ := ihlr.1 a ha
        obtain ⟨b'', hb'', hb''ish⟩ := ihlr'.1 b' hb'
        exact ⟨b'', hb'', Iso.trans hab' hb''ish⟩
      · intro b hb
        obtain ⟨b', hb', hb'ish⟩ := ihlr'.2 b hb
        obtain ⟨a', ha', ha'ish⟩ := ihlr.2 b' hb'
        exact ⟨a', ha', Iso.trans ha'ish hb'ish⟩)
    h).2 t rfl

end Work.ORHughesFree.Tree
