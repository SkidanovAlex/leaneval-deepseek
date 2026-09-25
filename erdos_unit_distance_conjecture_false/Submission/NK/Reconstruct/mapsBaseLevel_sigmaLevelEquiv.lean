import Mathlib
import Submission.NK.Reconstruct.Transport

namespace NK.Reconstruct

/-- **The level isomorphism `σ⁻¹ : ↥(σ L) ≃+* ↥L` is compatible with the base fields.**

`sigmaLevelEquiv σ hσ L` is the restriction of `σ.symm`; since `σ` maps the embedded copy of `K₂`
onto the embedded copy of `K₁` (`MapsBase`), `σ.symm` carries the embedded copy of `K₁` into that
of `K₂`, and `σ` carries the embedded copy of `K₂` into that of `K₁`.  Hence the transported level
isomorphism is a `MapsBaseLevel`. -/
theorem mapsBaseLevel_sigmaLevelEquiv {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂]
    [Field K₁'] [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (L : IntermediateField K₂ K₂') :
    NK.Reconstruct.MapsBaseLevel (NK.Reconstruct.sigmaLevel σ hσ L) L
      (NK.Reconstruct.sigmaLevelEquiv σ hσ L) := by
  constructor
  · -- `σ⁻¹` carries the embedded `K₁` into the embedded `K₂`
    intro a
    obtain ⟨c, hc⟩ := Submission.NeukirchUchida.mapsBase_mem_symm (algebraMap K₁ K₁')
      (algebraMap K₂ K₂') hσ (x := algebraMap K₁ K₁' a) ⟨a, rfl⟩
    exact ⟨c, by ext; simp [NK.Reconstruct.sigmaLevelEquiv_apply, hc]⟩
  · -- `σ` carries the embedded `K₂` into the embedded `K₁`
    intro b
    obtain ⟨c, hc⟩ := Submission.NeukirchUchida.mapsBase_mem (algebraMap K₁ K₁')
      (algebraMap K₂ K₂') hσ (x := algebraMap K₂ K₂' b) ⟨b, rfl⟩
    exact ⟨c, by ext; simp [NK.Reconstruct.sigmaLevelEquiv, hc]⟩

end NK.Reconstruct
