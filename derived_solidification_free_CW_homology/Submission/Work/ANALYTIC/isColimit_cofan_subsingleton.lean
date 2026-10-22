import Mathlib

namespace Work.ANALYTIC

open CategoryTheory Limits in
theorem isColimit_cofan_subsingleton {C : Type*} [Category C] {α : Type*} [Subsingleton α]
    [Nonempty α] {Q' : α → C} {W : C} (g : ∀ x, Q' x ⟶ W) (hg : ∀ x, IsIso (g x)) :
    Nonempty (IsColimit (Cofan.mk W g)) := by
  obtain ⟨a⟩ := ‹Nonempty α›
  refine ⟨Cofan.IsColimit.mk _ (fun s => inv (g a) ≫ s.inj a) ?_ ?_⟩
  · intro s j
    obtain rfl : j = a := Subsingleton.elim j a
    have hI := hg j
    exact IsIso.hom_inv_id_assoc (g j) (s.inj j)
  · intro s m h
    have ha := h a
    rw [← ha]
    have hI := hg a
    exact (IsIso.inv_hom_id_assoc (g a) m).symm

end Work.ANALYTIC
