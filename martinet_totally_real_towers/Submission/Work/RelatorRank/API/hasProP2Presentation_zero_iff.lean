import Mathlib
import Submission.Work.RelatorRank.Bridge

namespace Work.RelatorRank.API

/-- **A presentation of `Γ` with zero relations is exactly an injective dense generating family.**

`HasProP2Presentation Γ d 0` means: `Γ` has a dense generating family `gen : Fin d → Γ` whose
presentation kernel `ker (FreeGroup.lift gen)` is the normal closure of a relator set of size `≤ 0`
-- i.e. of the empty set, so `ker (FreeGroup.lift gen) = ⊥`.  Since `ker f = ⊥` is precisely
injectivity of `f`, the presentation data is the same thing as a dense generating family on which
the canonical presentation map `FreeGroup (Fin d) →* Γ` embeds. -/
theorem hasProP2Presentation_zero_iff {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] {d : ℕ} :
    HasProP2Presentation Γ d 0 ↔ ∃ gen : Fin d → Γ,
      DenseGenerating gen ∧ Function.Injective (FreeGroup.lift gen) := by
  constructor
  · rintro ⟨P⟩
    refine ⟨P.gen, P.dense, ?_⟩
    have hrel : P.rel = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero P.card_le)
    have hker : MonoidHom.ker (FreeGroup.lift P.gen) = ⊥ := by
      rw [P.ker_eq, hrel, Finset.coe_empty, Subgroup.normalClosure_empty]
    exact (MonoidHom.ker_eq_bot_iff (FreeGroup.lift P.gen)).mp hker
  · rintro ⟨gen, hgen, hinj⟩
    have hker : MonoidHom.ker (FreeGroup.lift gen) =
        Subgroup.normalClosure ((∅ : Finset (FreeGroup (Fin d))) : Set (FreeGroup (Fin d))) := by
      rw [Finset.coe_empty, Subgroup.normalClosure_empty,
        (MonoidHom.ker_eq_bot_iff (FreeGroup.lift gen)).mpr hinj]
    exact ⟨{ gen := gen, rel := ∅, dense := hgen, card_le := le_refl 0, ker_eq := hker }⟩

end Work.RelatorRank.API
