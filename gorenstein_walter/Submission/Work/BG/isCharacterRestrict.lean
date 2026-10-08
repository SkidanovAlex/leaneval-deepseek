import Mathlib
import Submission.Work.BG.CharBridge

namespace Work.BG

theorem isCharacterRestrict {H : Type} [Group H] [Finite H]
    {θ : OddOrder.RepresentationTheory.ClassFunction H ℂ}
    (hθ : OddOrder.RepresentationTheory.IsCharacter θ) (A : Subgroup H) :
    OddOrder.RepresentationTheory.IsCharacter
      (OddOrder.RepresentationTheory.ClassFunction.restrict A θ) := by
  obtain ⟨V, _, _, _, ρ, hρ⟩ := hθ
  -- Replace `θ` by the class function of its witnessing representation.
  have hθeq : θ = OddOrder.RepresentationTheory.repCharacterClassFunction ρ :=
    OddOrder.RepresentationTheory.ClassFunction.ext fun g => by
      rw [OddOrder.RepresentationTheory.repCharacterClassFunction_apply]
      exact congrFun hρ g
  rw [hθeq,
    OddOrder.RepresentationTheory.ClassFunction.restrict_repCharacterClassFunction A ρ]
  -- The restricted representation witnesses that the restriction is a character.
  exact OddOrder.RepresentationTheory.repCharacterClassFunction_isCharacter
    (ρ.comp A.subtype)

end Work.BG
