import Mathlib
import Submission.Work.WilC5.SatSetup
import Submission.Work.WilC5.SatBuild
import Submission.Work.WilC5.SatCore
import Submission.Work.WilC5.SatMain

open FirstOrder Language

set_option autoImplicit false
noncomputable section

namespace Work.WilC5

/-- The language map induced by the identity on the constants is the identity language
homomorphism. -/
theorem SatLangMap_id {L : FirstOrder.Language.{0, 0}} {C : Type} :
    SatLangMap (L := L) (id : C → C) = LHom.id (L[[C]]) := by
  apply LHom.funext
  · funext n x
    cases x with
    | inl f => rfl
    | inr c =>
      cases n with
      | zero => rfl
      | succ k => exact isEmptyElim c
  · funext n x
    cases x with
    | inl f => rfl
    | inr c => exact isEmptyElim c

/-- The image of a sentence under the identity language map is the sentence itself. -/
theorem SatLangMap_id_apply {L : FirstOrder.Language.{0, 0}} {C : Type}
    (ρ : (SatLang L C).Sentence) :
    (SatLangMap (L := L) (id : C → C)).onSentence ρ = ρ := by
  rw [SatLangMap_id]
  simp [LHom.onSentence, LHom.onFormula]

/-- **Monotonicity of the level theories.** If `y ≤ z` and `σ` belongs to the complete theory of
the structure at level `y`, then its image under the inclusion of the constant sets belongs to the
complete theory of the structure at level `z`.

For `y < z` this is exactly the statement that the specification `SatSpecG z` at level `z` contains
the images of the lower theories and is realized by `SatMod3 z` (`SatMain`).  For `y = z` the
inclusion is the identity and the claim is trivial. -/
theorem SatTh3Mono {L : FirstOrder.Language.{0, 0}} {M : Type} [instM : L.Structure M]
    {κ : Cardinal.{0}} (hM : Nonempty M) {y z : SatIdx κ} (h : y ≤ z)
    (σ : (SatLang L (SatC L M κ y)).Sentence) (hσ : σ ∈ SatTh3 L M κ y) :
    (SatLangMap (SatInc L M κ h)).onSentence σ ∈ SatTh3 L M κ z := by
  rcases lt_or_eq_of_le h with hlt | heq
  · -- `y < z`: the image of `σ` lies in the specification at level `z`, which `SatMod3 z` realizes.
    letI := SatStruc3 L M κ z
    have hmem : (SatLangMap (SatInc L M κ h)).onSentence σ ∈ SatSpecG L M κ z := by
      rw [mem_SatSpecG]
      refine Or.inr (Or.inl ⟨y, hlt, σ, hσ, ?_⟩)
      rw [SatInc_proof_irrel L M κ h (le_of_lt hlt)]
    have hreal := (SatMain L M κ hM z).2 _ hmem
    rw [SatTh3, mem_completeTheory]
    exact hreal
  · -- `y = z`: the inclusion is the identity, so the sentence is unchanged.
    subst heq
    have hEq : (SatLangMap (SatInc L M κ h)).onSentence σ = σ := by
      have h1 : SatInc L M κ h = id := by
        rw [SatInc_proof_irrel L M κ h (le_refl y), SatInc_id]
      rw [h1, SatLangMap_id_apply]
    rwa [hEq]

end Work.WilC5
