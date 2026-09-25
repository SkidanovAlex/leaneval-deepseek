import Mathlib
import Submission.NK.Reconstruct.Transport

/-!
# The restriction of the conjugation by `σ` to a finite level

`Submission.NeukirchUchida.conjHomEquiv hσ` is the isomorphism `Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)` given by
conjugation `x ↦ σ⁻¹ (g (σ x))` with `σ : K₂' ≃+* K₁'` (the "easy half" of CoNF XII §12.2).  This
file computes its restriction to a finite level `L ⊆ K₂'`: on `L` it is the conjugation by the
level isomorphism `sigmaLevelEquiv σ hσ L : σ(L) ≃+* L`.
-/

namespace NK.Reconstruct

theorem restrictNormalHom_conjHomEquiv {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂]
    [Field K₁'] [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (L : IntermediateField K₂ K₂') [FiniteDimensional K₂ L] [Normal K₂ L] [NumberField ↥L]
    [FiniteDimensional K₁ ↥(NK.Reconstruct.sigmaLevel σ hσ L)]
    [Normal K₁ ↥(NK.Reconstruct.sigmaLevel σ hσ L)]
    {h : NK.Reconstruct.MapsBaseLevel (NK.Reconstruct.sigmaLevel σ hσ L) L
      (NK.Reconstruct.sigmaLevelEquiv σ hσ L)} (g : Gal(K₁'/K₁)) :
    AlgEquiv.restrictNormalHom L (Submission.NeukirchUchida.conjHomEquiv hσ g) =
      NK.Reconstruct.conjAlgEquiv (NK.Reconstruct.sigmaLevelEquiv σ hσ L) h
        (AlgEquiv.restrictNormalHom (NK.Reconstruct.sigmaLevel σ hσ L) g) := by
  set τ := NK.Reconstruct.sigmaLevelEquiv σ hσ L with hτ
  have hsymm : ∀ y : ↥L, ((τ.symm y : ↥(NK.Reconstruct.sigmaLevel σ hσ L)) : K₁')
      = σ (y : K₂') := by
    intro y
    have h2 := NK.Reconstruct.sigmaLevelEquiv_apply σ hσ L (τ.symm y)
    rw [show τ (τ.symm y) = y from τ.apply_symm_apply y] at h2
    have h3 : σ (σ.symm ((τ.symm y : ↥(NK.Reconstruct.sigmaLevel σ hσ L)) : K₁'))
        = σ (y : K₂') := congrArg (fun z => σ z) h2.symm
    simpa using h3
  ext y
  simp only [AlgEquiv.restrictNormalHom_apply]
  rw [show ((Submission.NeukirchUchida.conjHomEquiv hσ) g) = Submission.NeukirchUchida.conj hσ g
    from rfl]
  rw [Submission.NeukirchUchida.conj_apply, NK.Reconstruct.conjAlgEquiv_apply,
    NK.Reconstruct.sigmaLevelEquiv_apply, AlgEquiv.restrictNormalHom_apply]
  rw [hsymm]

end NK.Reconstruct
