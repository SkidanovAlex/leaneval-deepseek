import Submission.NK.ReconstructField.Input
import Submission.NK.ReconstructField.exists_twist_of_mapsBase
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The two forms of the reconstruction input are equivalent

`NK.ReconstructField.ReconstructionInput` (σ-free: a base-field isomorphism and a Galois twist)
and `NK.ReconstructField.ReconstructionInputSigma` (σ-based: a MapsBase isomorphism of the
separable closures realizing the place correspondence) are equivalent.  This makes precise the
sense in which the main theorem of this chapter produces `σ` *from* the realization of the place
correspondence rather than *assuming* it.
-/

set_option linter.unusedVariables false

namespace NK.ReconstructField

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The σ-based form of the reconstruction input implies the σ-free one**: every MapsBase
isomorphism of the separable closures is a Galois twist of the lift of the base-field isomorphism it
induces (`NK.ReconstructField.exists_twist_of_mapsBase`). -/
theorem reconstructionInput_of_reconstructionInputSigma
    {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} {hϕ : IsHomeomorph ϕ}
    {a : NK.Reconstruct.LocalCorrespondence ϕ} (h : ReconstructionInputSigma hϕ a) :
    ReconstructionInput hϕ a := by
  obtain ⟨σ, hσ, hreal⟩ := h
  obtain ⟨τ, h, rfl⟩ := exists_twist_of_mapsBase σ hσ
  exact ⟨τ, h, hreal⟩

/-- **The two forms of the reconstruction input are equivalent.** -/
theorem reconstructionInput_iff_reconstructionInputSigma
    {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} {hϕ : IsHomeomorph ϕ}
    {a : NK.Reconstruct.LocalCorrespondence ϕ} :
    ReconstructionInput hϕ a ↔ ReconstructionInputSigma hϕ a :=
  ⟨reconstructionInputSigma_of_reconstructionInput,
    reconstructionInput_of_reconstructionInputSigma⟩

end NK.ReconstructField
