import Submission.NK.EndgameRepair.ExistsSigma
import Submission.NK.ReconstructEndgame.All

/-!
# The repaired Shimizu endgame

`Submission/Work/ReconstructEndgame/` and `Submission/Work/Mine/` assemble Neukirch–Uchida from the
Shimizu route, but every one of their capstones carries the three `rankGamma`-inputs
`HausRankInput`, `RankStrictMonoLevelInputGen`, `ResRankInputGen` — of which the first is **false**
(`NK.RankTheoryDeep.not_hausRankInput`) and the third is stated on the invariant that is *not*
Shimizu's `r_ℓ(K)` (`rankGamma` is `Module.finrank` of the torsion-free quotient, which is `0` as
soon as the rank is infinite).  Their capstones are therefore vacuous.

This file re-runs the *same* assembly with the rank inputs replaced by the single corrected
hypothesis `NK.EndgameRepair.Fourf5InputGenDerived K₁ K₁' ℓ` (or, at the very top, the corrected
residual `NK.RankTheoryDeep.CorrectedResidualsDerived K₁ K₁' ℓ`).

## Contents

* `NK.EndgameRepair.neukirch_uchida_of_preserves_corrected_inst` — the `∃!` form from
  `Submission.NeukirchUchida.PreservesDecompositionGroups ϕ`, the per-prime local structure bundles
  `NK.PTorsionTop.LocalGaloisInputsTop`, the σ-free Frobenius correspondence `hb` and
  `Fourf5InputGen` (ambient `ℚ`-algebra structure on `K₁'`); this is
  `NK.ReconstructEndgame.neukirch_uchida_of_preserves_shimizu_inst` repaired.
* `NK.EndgameRepair.neukirch_uchida_of_preserves_corrected` — the same with the `ℚ`-algebra
  structure on `K₁'` derived (`Fourf5InputGenDerived`, `ChebotarevInputDerived`).
* `NK.EndgameRepair.neukirch_uchida_of_localStructureData_corrected` — block (i) in the
  `HasseTwist`/`Indecomposed` form, block (ii) in the core
  `TowerRankCore`/`ArtinReciprocity` form, and the Frobenius correspondence discharged by
  `NK.ResidueFrob.LocalStructureData` at every finite place; this is
  `NK.ReconstructEndgame.neukirch_uchida_of_localStructureData` repaired.
* `NK.EndgameRepair.neukirch_uchida_of_localStructureData_correctedResiduals` — the same with the
  single rank hypothesis `NK.RankTheoryDeep.CorrectedResidualsDerived K₁ K₁' ℓ`; this is
  `NK.Mine.neukirch_uchida_of_localStructureData_residuals` repaired.
* the `exists_sigma_` (existence-half) forms of all of the above.

None of these theorems nor their hypotheses mention the three `rankGamma`-inputs, `Residuals` or
`ResidualsDerived` (see `README.md` §"audit").
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace NK.EndgameRepair

universe u

section WithInstances

/-! ## The repaired endgame with an ambient `ℚ`-algebra structure on `K₁'` -/

variable {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
  [Algebra ℚ K₁'] [IsGalois ℚ K₁'] [IsSepClosure ℚ K₁']

/-- **Neukirch–Uchida (CoNF XII Thm 12.2.1) from `PreservesDecompositionGroups ϕ`, the per-prime
local structure bundles, the Frobenius correspondence, Shimizu's Proposition 4f.5 and Čebotarev.**

This is `NK.ReconstructEndgame.neukirch_uchida_of_preserves_shimizu_inst` with the three
`rankGamma`-inputs replaced by `NK.Reconstruct.Fourf5InputGen K₁' ℓ`. -/
theorem neukirch_uchida_of_preserves_corrected_inst
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (h : Submission.NeukirchUchida.PreservesDecompositionGroups ϕ)
    (k₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ, p.Prime ∧
        CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K₁)) p ∧
        NK.PTorsionTop.LocalGaloisInputsTop K₁ 𝔭
          (SeparableClosure (𝔭.adicCompletion K₁)) p)
    (k₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ p : ℕ, p.Prime ∧
        CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K₂)) p ∧
        NK.PTorsionTop.LocalGaloisInputsTop K₂ 𝔮
          (SeparableClosure (𝔮.adicCompletion K₂)) p)
    (hb : ∀ a : NK.Reconstruct.LocalCorrespondence ϕ,
      NK.Reconstruct.FrobeniusCorrespondencePlace ϕ he a)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (h45 : NK.Reconstruct.Fourf5InputGen K₁' ℓ)
    (hc : NK.Reconstruct.ChebotarevInput ℚ K₁')
    : ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm)
 := by
  have k₁' : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ, p.Prime ∧
        NK.LocalInputs.LocalFieldInputs K₁ 𝔭 p ∧
        NK.PTorsionTop.LocalGaloisInputsTop K₁ 𝔭
          (SeparableClosure (𝔭.adicCompletion K₁)) p := by
    intro 𝔭
    obtain ⟨p, hp, hres, hG⟩ := k₁ 𝔭
    exact ⟨p, hp, NK.LocalInputs.PowerQuotient.localFieldInputs_of_prime 𝔭 hp hres, hG⟩
  have k₂' : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ q : ℕ, q.Prime ∧
        NK.LocalInputs.LocalFieldInputs K₂ 𝔮 q ∧
        NK.PTorsionTop.LocalGaloisInputsTop K₂ 𝔮
          (SeparableClosure (𝔮.adicCompletion K₂)) q := by
    intro 𝔮
    obtain ⟨q, hq, hres, hG⟩ := k₂ 𝔮
    exact ⟨q, hq, NK.LocalInputs.PowerQuotient.localFieldInputs_of_prime 𝔮 hq hres, hG⟩
  have hres := NK.Mine.residueChar_preserved_of_topInputs ϕ h k₁' k₂'
  have hldeg := NK.Mine.localDegree_preserved_of_topInputs ϕ he h k₁' k₂'
  let a : NK.Reconstruct.LocalCorrespondence ϕ :=
    Submission.NeukirchUchida.localCorrespondenceOf ϕ h hres hldeg
  obtain ⟨σ, hσ⟩ :=
    NK.EndgameRepair.exists_sigma_of_localCorrespondence_corrected ϕ he a (hb a) ℓ h45 hc
  exact ⟨σ, hσ, fun y hy => Submission.NeukirchUchida.unique_sigma ϕ he hy hσ⟩

/-- The existence half of `neukirch_uchida_of_preserves_corrected_inst`. -/
theorem exists_sigma_of_preserves_corrected_inst
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (h : Submission.NeukirchUchida.PreservesDecompositionGroups ϕ)
    (k₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ, p.Prime ∧
        CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K₁)) p ∧
        NK.PTorsionTop.LocalGaloisInputsTop K₁ 𝔭
          (SeparableClosure (𝔭.adicCompletion K₁)) p)
    (k₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ p : ℕ, p.Prime ∧
        CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K₂)) p ∧
        NK.PTorsionTop.LocalGaloisInputsTop K₂ 𝔮
          (SeparableClosure (𝔮.adicCompletion K₂)) p)
    (hb : ∀ a : NK.Reconstruct.LocalCorrespondence ϕ,
      NK.Reconstruct.FrobeniusCorrespondencePlace ϕ he a)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (h45 : NK.Reconstruct.Fourf5InputGen K₁' ℓ)
    (hc : NK.Reconstruct.ChebotarevInput ℚ K₁')
    : ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ := by
  obtain ⟨σ, hσ, _⟩ :=
    neukirch_uchida_of_preserves_corrected_inst ϕ he h k₁ k₂ hb ℓ h45 hc
  exact ⟨σ, hσ⟩

end WithInstances

section Derived

/-! ## The repaired endgame with the `ℚ`-structure derived -/

variable {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The `∃!` form**, with the `ℚ`-algebra structure on `K₁'` derived and the rank hypothesis
`NK.EndgameRepair.Fourf5InputGenDerived K₁ K₁' ℓ`. -/
theorem neukirch_uchida_of_preserves_corrected
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (h : Submission.NeukirchUchida.PreservesDecompositionGroups ϕ)
    (k₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ, p.Prime ∧
        CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K₁)) p ∧
        NK.PTorsionTop.LocalGaloisInputsTop K₁ 𝔭
          (SeparableClosure (𝔭.adicCompletion K₁)) p)
    (k₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ p : ℕ, p.Prime ∧
        CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K₂)) p ∧
        NK.PTorsionTop.LocalGaloisInputsTop K₂ 𝔮
          (SeparableClosure (𝔮.adicCompletion K₂)) p)
    (hb : ∀ a : NK.Reconstruct.LocalCorrespondence ϕ,
      NK.Reconstruct.FrobeniusCorrespondencePlace ϕ he a)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (h45 : Fourf5InputGenDerived K₁ K₁' ℓ)
    (hc : NK.ReconstructEndgame.ChebotarevInputDerived K₁ K₁')
    : ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm)
 := by
  letI : Algebra ℚ K₁' := NK.ReconstructEndgame.ratAlgebra K₁ K₁'
  haveI : IsSepClosure ℚ K₁' :=
    NK.ReconstructEndgame.isSepClosure_rat_of_numberField K₁ K₁'
  haveI : IsGalois ℚ K₁' := NK.ReconstructEndgame.isGalois_rat_of_numberField K₁ K₁'
  exact neukirch_uchida_of_preserves_corrected_inst ϕ he h k₁ k₂ hb ℓ h45 hc

/-- The existence half of `neukirch_uchida_of_preserves_corrected`. -/
theorem exists_sigma_of_preserves_corrected
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (h : Submission.NeukirchUchida.PreservesDecompositionGroups ϕ)
    (k₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ, p.Prime ∧
        CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K₁)) p ∧
        NK.PTorsionTop.LocalGaloisInputsTop K₁ 𝔭
          (SeparableClosure (𝔭.adicCompletion K₁)) p)
    (k₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ p : ℕ, p.Prime ∧
        CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K₂)) p ∧
        NK.PTorsionTop.LocalGaloisInputsTop K₂ 𝔮
          (SeparableClosure (𝔮.adicCompletion K₂)) p)
    (hb : ∀ a : NK.Reconstruct.LocalCorrespondence ϕ,
      NK.Reconstruct.FrobeniusCorrespondencePlace ϕ he a)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (h45 : Fourf5InputGenDerived K₁ K₁' ℓ)
    (hc : NK.ReconstructEndgame.ChebotarevInputDerived K₁ K₁')
    : ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ := by
  obtain ⟨σ, hσ, _⟩ := neukirch_uchida_of_preserves_corrected ϕ he h k₁ k₂ hb ℓ h45 hc
  exact ⟨σ, hσ⟩

/-- **Neukirch–Uchida (CoNF XII Thm 12.2.1) from the Shimizu route with the Frobenius correspondence
discharged by `NK.ResidueFrob.LocalStructureData` at every finite place.**

This is `NK.ReconstructEndgame.neukirch_uchida_of_localStructureData` repaired: block (i) in the
`HasseTwist`/`Indecomposed` form, block (ii) in the core `TowerRankCore`/`ArtinReciprocity` form,
the local structure data at every finite place (which supplies `hb` through
`NK.ResidueFrob.frobeniusCorrespondencePlace_of_localStructureData`), the corrected rank
hypothesis and Čebotarev. -/
theorem neukirch_uchida_of_localStructureData_corrected
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (hB₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ,
        NK.HasseTwist.Sha2Input p K₂ K₂' (𝔭.adicCompletion K₁)
          (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        NK.Indecomposed.RankData p K₂ K₂' (𝔭.adicCompletion K₁)
          (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        NK.Indecomposed.LocalReconstruction p K₂ K₂' (𝔭.adicCompletion K₁)
          (SeparableClosure (𝔭.adicCompletion K₁)))
    (hB₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ p : ℕ,
        NK.HasseTwist.Sha2Input p K₁ K₁' (𝔮.adicCompletion K₂)
          (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        NK.Indecomposed.RankData p K₁ K₁' (𝔮.adicCompletion K₂)
          (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        NK.Indecomposed.LocalReconstruction p K₁ K₁' (𝔮.adicCompletion K₂)
          (SeparableClosure (𝔮.adicCompletion K₂)))
    (k₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      NK.LocalStructure.TowerRankCore K₁ 𝔭 (SeparableClosure (𝔭.adicCompletion K₁))
        (ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K₁))) ∧
      Nonempty (NK.LocalCFT.ArtinReciprocity (𝔭.adicCompletion K₁)
        (SeparableClosure (𝔭.adicCompletion K₁))))
    (k₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      NK.LocalStructure.TowerRankCore K₂ 𝔮 (SeparableClosure (𝔮.adicCompletion K₂))
        (ringChar (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K₂))) ∧
      Nonempty (NK.LocalCFT.ArtinReciprocity (𝔮.adicCompletion K₂)
        (SeparableClosure (𝔮.adicCompletion K₂))))
    (h₁ : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K₁ K₁',
      NK.ResidueFrob.LocalStructureData K₁ K₁' A)
    (h₂ : ∀ B : NK.FrobeniusBridge.FinitePlaceOf K₂ K₂',
      NK.ResidueFrob.LocalStructureData K₂ K₂' B)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (h45 : Fourf5InputGenDerived K₁ K₁' ℓ)
    (hc : NK.ReconstructEndgame.ChebotarevInputDerived K₁ K₁')
    : ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm)
 :=
  neukirch_uchida_of_preserves_corrected ϕ he
    (NK.Indecomposed.preservesDecompositionGroups_of_hasseAt ϕ he hB₁ hB₂)
    (fun 𝔭 => NK.ReconstructEndgame.exists_localGaloisInputsTop_of_coreData K₁ 𝔭 (k₁ 𝔭))
    (fun 𝔮 => NK.ReconstructEndgame.exists_localGaloisInputsTop_of_coreData K₂ 𝔮 (k₂ 𝔮))
    (NK.ReconstructEndgame.forall_frobeniusCorrespondencePlace_of_localStructureData ϕ he h₁ h₂)
    ℓ h45 hc

/-- The existence half of `neukirch_uchida_of_localStructureData_corrected`. -/
theorem exists_sigma_of_localStructureData_corrected
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (hB₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ,
        NK.HasseTwist.Sha2Input p K₂ K₂' (𝔭.adicCompletion K₁)
          (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        NK.Indecomposed.RankData p K₂ K₂' (𝔭.adicCompletion K₁)
          (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        NK.Indecomposed.LocalReconstruction p K₂ K₂' (𝔭.adicCompletion K₁)
          (SeparableClosure (𝔭.adicCompletion K₁)))
    (hB₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ p : ℕ,
        NK.HasseTwist.Sha2Input p K₁ K₁' (𝔮.adicCompletion K₂)
          (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        NK.Indecomposed.RankData p K₁ K₁' (𝔮.adicCompletion K₂)
          (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        NK.Indecomposed.LocalReconstruction p K₁ K₁' (𝔮.adicCompletion K₂)
          (SeparableClosure (𝔮.adicCompletion K₂)))
    (k₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      NK.LocalStructure.TowerRankCore K₁ 𝔭 (SeparableClosure (𝔭.adicCompletion K₁))
        (ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K₁))) ∧
      Nonempty (NK.LocalCFT.ArtinReciprocity (𝔭.adicCompletion K₁)
        (SeparableClosure (𝔭.adicCompletion K₁))))
    (k₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      NK.LocalStructure.TowerRankCore K₂ 𝔮 (SeparableClosure (𝔮.adicCompletion K₂))
        (ringChar (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K₂))) ∧
      Nonempty (NK.LocalCFT.ArtinReciprocity (𝔮.adicCompletion K₂)
        (SeparableClosure (𝔮.adicCompletion K₂))))
    (h₁ : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K₁ K₁',
      NK.ResidueFrob.LocalStructureData K₁ K₁' A)
    (h₂ : ∀ B : NK.FrobeniusBridge.FinitePlaceOf K₂ K₂',
      NK.ResidueFrob.LocalStructureData K₂ K₂' B)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (h45 : Fourf5InputGenDerived K₁ K₁' ℓ)
    (hc : NK.ReconstructEndgame.ChebotarevInputDerived K₁ K₁')
    : ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ := by
  obtain ⟨σ, hσ, _⟩ :=
    neukirch_uchida_of_localStructureData_corrected ϕ he hB₁ hB₂ k₁ k₂ h₁ h₂ ℓ h45 hc
  exact ⟨σ, hσ⟩

end Derived

section DerivedResidual

/-! ## The repaired `NK.Mine`-shaped capstone on the corrected residual

`NK.RankTheoryDeep.CorrectedResidualsDerived K K' ℓ` is stated for `K`, `K'` in a common
universe, so this section uses the uniform universe `Type u` (as does
`NK.Mine.ClassicalChaptersDeep`). -/

variable {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The `∃!` form of Neukirch–Uchida on the corrected residual, in the shape of
`NK.Mine.neukirch_uchida_of_localStructureData_residuals`.**

The single rank hypothesis is `NK.RankTheoryDeep.CorrectedResidualsDerived K₁ K₁' ℓ`, and the
remaining hypotheses are exactly those of the on-disk theorem (block (i), block (ii), the local
structure data at every finite place, and Čebotarev). -/
theorem neukirch_uchida_of_localStructureData_correctedResiduals
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (hB₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ,
        NK.HasseTwist.Sha2Input p K₂ K₂' (𝔭.adicCompletion K₁)
          (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        NK.Indecomposed.RankData p K₂ K₂' (𝔭.adicCompletion K₁)
          (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        NK.Indecomposed.LocalReconstruction p K₂ K₂' (𝔭.adicCompletion K₁)
          (SeparableClosure (𝔭.adicCompletion K₁)))
    (hB₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ p : ℕ,
        NK.HasseTwist.Sha2Input p K₁ K₁' (𝔮.adicCompletion K₂)
          (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        NK.Indecomposed.RankData p K₁ K₁' (𝔮.adicCompletion K₂)
          (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        NK.Indecomposed.LocalReconstruction p K₁ K₁' (𝔮.adicCompletion K₂)
          (SeparableClosure (𝔮.adicCompletion K₂)))
    (k₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      NK.LocalStructure.TowerRankCore K₁ 𝔭 (SeparableClosure (𝔭.adicCompletion K₁))
        (ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K₁))) ∧
      Nonempty (NK.LocalCFT.ArtinReciprocity (𝔭.adicCompletion K₁)
        (SeparableClosure (𝔭.adicCompletion K₁))))
    (k₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      NK.LocalStructure.TowerRankCore K₂ 𝔮 (SeparableClosure (𝔮.adicCompletion K₂))
        (ringChar (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K₂))) ∧
      Nonempty (NK.LocalCFT.ArtinReciprocity (𝔮.adicCompletion K₂)
        (SeparableClosure (𝔮.adicCompletion K₂))))
    (h₁ : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K₁ K₁',
      NK.ResidueFrob.LocalStructureData K₁ K₁' A)
    (h₂ : ∀ B : NK.FrobeniusBridge.FinitePlaceOf K₂ K₂',
      NK.ResidueFrob.LocalStructureData K₂ K₂' B)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hres : NK.RankTheoryDeep.CorrectedResidualsDerived K₁ K₁' ℓ)
    (hc : NK.ReconstructEndgame.ChebotarevInputDerived K₁ K₁')
    : ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) :=
  neukirch_uchida_of_localStructureData_corrected ϕ he hB₁ hB₂ k₁ k₂ h₁ h₂ ℓ
    (fourf5GenDerived_of_correctedResidualsDerived hres) hc

/-- The existence half of `neukirch_uchida_of_localStructureData_correctedResiduals`. -/
theorem exists_sigma_of_localStructureData_correctedResiduals
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (hB₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ,
        NK.HasseTwist.Sha2Input p K₂ K₂' (𝔭.adicCompletion K₁)
          (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        NK.Indecomposed.RankData p K₂ K₂' (𝔭.adicCompletion K₁)
          (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        NK.Indecomposed.LocalReconstruction p K₂ K₂' (𝔭.adicCompletion K₁)
          (SeparableClosure (𝔭.adicCompletion K₁)))
    (hB₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ p : ℕ,
        NK.HasseTwist.Sha2Input p K₁ K₁' (𝔮.adicCompletion K₂)
          (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        NK.Indecomposed.RankData p K₁ K₁' (𝔮.adicCompletion K₂)
          (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        NK.Indecomposed.LocalReconstruction p K₁ K₁' (𝔮.adicCompletion K₂)
          (SeparableClosure (𝔮.adicCompletion K₂)))
    (k₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      NK.LocalStructure.TowerRankCore K₁ 𝔭 (SeparableClosure (𝔭.adicCompletion K₁))
        (ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K₁))) ∧
      Nonempty (NK.LocalCFT.ArtinReciprocity (𝔭.adicCompletion K₁)
        (SeparableClosure (𝔭.adicCompletion K₁))))
    (k₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      NK.LocalStructure.TowerRankCore K₂ 𝔮 (SeparableClosure (𝔮.adicCompletion K₂))
        (ringChar (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K₂))) ∧
      Nonempty (NK.LocalCFT.ArtinReciprocity (𝔮.adicCompletion K₂)
        (SeparableClosure (𝔮.adicCompletion K₂))))
    (h₁ : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K₁ K₁',
      NK.ResidueFrob.LocalStructureData K₁ K₁' A)
    (h₂ : ∀ B : NK.FrobeniusBridge.FinitePlaceOf K₂ K₂',
      NK.ResidueFrob.LocalStructureData K₂ K₂' B)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hres : NK.RankTheoryDeep.CorrectedResidualsDerived K₁ K₁' ℓ)
    (hc : NK.ReconstructEndgame.ChebotarevInputDerived K₁ K₁')
    : ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ := by
  obtain ⟨σ, hσ, _⟩ :=
    neukirch_uchida_of_localStructureData_correctedResiduals ϕ he hB₁ hB₂ k₁ k₂ h₁ h₂ ℓ hres hc
  exact ⟨σ, hσ⟩

end DerivedResidual

end NK.EndgameRepair
