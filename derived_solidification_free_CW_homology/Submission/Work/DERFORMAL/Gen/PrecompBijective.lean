import Mathlib

namespace Work.DERFORMAL.Gen

open CategoryTheory

theorem PrecompBijective {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) : IsIso f ↔ ∀ (Z : C), Function.Bijective (fun g : Y ⟶ Z => f ≫ g) := by
  constructor
  · intro hf Z
    obtain ⟨inv, h1, h2⟩ := hf.out
    exact ⟨fun a b h => by
        have := congrArg (fun t => inv ≫ t) h
        simpa [← Category.assoc, h2] using this,
      fun b => ⟨inv ≫ b, by simp [← Category.assoc, h1]⟩⟩
  · intro h
    obtain ⟨g, hg⟩ : ∃ g : Y ⟶ X, f ≫ g = 𝟙 X := (h X).2 (𝟙 X)
    exact IsIso.mk ⟨g, hg, (h Y).1 (by simp [← Category.assoc, hg])⟩

end Work.DERFORMAL.Gen
