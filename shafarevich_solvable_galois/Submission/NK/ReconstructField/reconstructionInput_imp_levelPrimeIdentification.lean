import Mathlib
import Submission.NK.ReconstructField.MainWeakNU
import Submission.NK.Reconstruct.agreesOnLevels_of_realizesPlaceMap
import Submission.NK.ReconstructField.primeTransport_eq_primeMap_of_realizesPlaceCorrespondence
import Submission.NK.ReconstructField.primeOf_comap_eq_primeTransport
import Submission.NK.Reconstruct.frobeniusCorrespondence_of_place
import Submission.NK.ReconstructField.exists_finitePlace_of_prime_level
import Submission.NK.ReconstructField.LevelPrime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.ReconstructField

open NK.Reconstruct
open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The level isomorphism `↥L ≃+* ↥L₂` induced by `σ⁻¹`**, when `σ` carries `L₂` onto `L`
(i.e. `sigmaLevel σ hσ L₂ = L`).  Its underlying function is `σ.symm`. -/
noncomputable def levelEquivOfSigma {σ : K₂' ≃+* K₁'}
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (L : IntermediateField K₁ K₁') (L₂ : IntermediateField K₂ K₂')
    (hL : NK.Reconstruct.sigmaLevel σ hσ L₂ = L) : ↥L ≃+* ↥L₂ where
  toFun x := ⟨σ.symm (x : K₁'), by
    have hx : (x : K₁') ∈ NK.Reconstruct.sigmaLevel σ hσ L₂ := by
      rw [hL]; exact x.2
    exact NK.Reconstruct.mem_sigmaLevel.mp hx⟩
  invFun y := ⟨σ (y : K₂'), by
    rw [← hL]
    exact NK.Reconstruct.mem_sigmaLevel.mpr (by simpa using y.2)⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_mul' x y := by ext; simp
  map_add' x y := by ext; simp

@[simp] lemma levelEquivOfSigma_apply_coe {σ : K₂' ≃+* K₁'}
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (L : IntermediateField K₁ K₁') (L₂ : IntermediateField K₂ K₂')
    (hL : NK.Reconstruct.sigmaLevel σ hσ L₂ = L) (x : ↥L) :
    ((levelEquivOfSigma hσ L L₂ hL x : ↥L₂) : K₂') = σ.symm (x : K₁') := rfl

theorem reconstructionInput_imp_levelPrimeIdentification {K₁ K₂ K₁' K₂' : Type*} [Field K₁]
    [Field K₂] [Field K₁'] [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁']
    [Algebra K₂ K₂'] [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ) (τ₀ : K₁ ≃+* K₂)
    (h : ∃ (σ : K₂' ≃+* K₁')
      (_ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ),
      (∀ x : K₁, σ (algebraMap K₂ K₂' (τ₀ x)) = algebraMap K₁ K₁' x) ∧
        (∀ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
          (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1)) :
    NK.ReconstructField.LevelPrimeIdentification ϕ hϕ a τ₀ := by
  obtain ⟨σ, hσ, hbase, hreal⟩ := h
  -- `ϕ` and the conjugation by `σ` induce the same correspondence of levels
  have hlvl : NK.Reconstruct.AgreesOnLevels ϕ hϕ σ hσ :=
    NK.Reconstruct.agreesOnLevels_of_realizesPlaceMap hϕ a σ hσ hreal
  intro L _ _ _ _ _ _ _
  -- the transported level `σ(levelMap ϕ L)` is `L`
  have hL : NK.Reconstruct.sigmaLevel σ hσ (NK.Reconstruct.levelMap ϕ L) = L := by
    haveI : FiniteDimensional K₁
        (NK.Reconstruct.sigmaLevel σ hσ (NK.Reconstruct.levelMap ϕ L)) :=
      NK.Reconstruct.finiteDimensional_sigmaLevel σ hσ (NK.Reconstruct.levelMap ϕ L)
    have h1 := NK.ReconstructField.levelMap_symm_levelMap ϕ hϕ
      (NK.Reconstruct.sigmaLevel σ hσ (NK.Reconstruct.levelMap ϕ L))
    rw [hlvl (NK.Reconstruct.levelMap ϕ L)] at h1
    exact h1.symm.trans (NK.ReconstructField.levelMap_symm_levelMap ϕ hϕ L)
  refine ⟨levelEquivOfSigma hσ L (NK.Reconstruct.levelMap ϕ L) hL, ?_, ?_⟩
  · funext P
    obtain ⟨A, hAspec⟩ := NK.ReconstructField.exists_finitePlace_of_prime_level L P
    rw [NK.ReconstructField.levelPrimeMap_spec ϕ hϕ a L P A hAspec]
    refine Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
      (K := ↥(NK.Reconstruct.levelMap ϕ L)) ?_
    rw [← NK.Reconstruct.primeOfLevel_spec (a.placeMap A).1 (NK.Reconstruct.levelMap ϕ L)
          (NK.Reconstruct.comap_level_ne_top (a.placeMap A).2 (NK.Reconstruct.levelMap ϕ L)),
        NK.Reconstruct.comap_placeMap_level a σ hreal
          (levelEquivOfSigma hσ L (NK.Reconstruct.levelMap ϕ L) hL) (fun x => rfl) A,
        hAspec, NK.Reconstruct.valuationSubringAtPrime_primeTransport
          (levelEquivOfSigma hσ L (NK.Reconstruct.levelMap ϕ L) hL) P]
  · intro x
    apply Subtype.ext
    rw [levelEquivOfSigma_apply_coe]
    rw [show ((algebraMap K₁ ↥L x : ↥L) : K₁') = algebraMap K₁ K₁' x from
        IsScalarTower.algebraMap_apply K₁ ↥L K₁' x,
      show ((algebraMap K₂ ↥(NK.Reconstruct.levelMap ϕ L) (τ₀ x) :
          ↥(NK.Reconstruct.levelMap ϕ L)) : K₂') = algebraMap K₂ K₂' (τ₀ x) from
        IsScalarTower.algebraMap_apply K₂ ↥(NK.Reconstruct.levelMap ϕ L) K₂' (τ₀ x)]
    exact σ.symm_apply_eq.mpr (hbase x).symm

end NK.ReconstructField
