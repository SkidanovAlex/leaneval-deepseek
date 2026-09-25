import Submission.NK.ReconstructEndgame.Basic
import Submission.NK.Mine.FinalLeaves

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open IsDedekindDomain.HeightOneSpectrum

universe u

namespace NK.ReconstructEndgame

/-! ## Block (ii): from the core local data to `LocalGaloisInputsTop` -/

/-- **Block (ii) at a single finite prime.**  The local structure input
`NK.LocalStructure.TowerRankCore` together with `NK.LocalCFT.ArtinReciprocity` at the completion
`𝔭.adicCompletion K` (with `p` the residue characteristic) produces the bundle
`NK.PTorsionTop.LocalGaloisInputsTop` consumed by the local chapter, with the prime `p` pinned to
`ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))`.

This is the per-prime `k₁'`/`k₂'` computation of `NK.Mine.neukirch_uchida_of_finalLeaves`,
isolated so that the variants below can share it. -/
theorem exists_localGaloisInputsTop_of_coreData (K : Type u) [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (NK.LocalStructure.TowerRankCore K 𝔭 (SeparableClosure (𝔭.adicCompletion K))
        (ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))) ∧
      Nonempty (NK.LocalCFT.ArtinReciprocity (𝔭.adicCompletion K)
        (SeparableClosure (𝔭.adicCompletion K)))) →
    ∃ p : ℕ, p.Prime ∧
      CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p ∧
      NK.PTorsionTop.LocalGaloisInputsTop K 𝔭
        (SeparableClosure (𝔭.adicCompletion K)) p := by
  intro h
  have hp : (ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))).Prime :=
    NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  have hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))
      (ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))) :=
    NK.Mine.charP_ringChar_residueField_adicCompletion 𝔭
  exact ⟨_, hp, hchar,
    NK.Mine.localGaloisInputsTop_of_coreData 𝔭 hp hchar h.1 h.2
      (fun H hH hN => NK.Mine.isOpen_of_index_prime_of_towerRankCorePoly 𝔭 h.1 hH hN)⟩

section WithInstances

/-! ## The Shimizu endgame for an ambient `ℚ`-algebra structure on `K₁'`

The theorems in this section carry the `ℚ`-algebra structure on `K₁'` (and the instances
`IsGalois ℚ K₁'`, `IsSepClosure ℚ K₁'`) as ordinary hypotheses — exactly the ambient data of
`NK.Reconstruct.exists_sigma_of_localCorrespondence`.  They are the workhorses: the un-suffixed
statements of the next section derive these instances and delegate to this one. -/

variable {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
  [Algebra ℚ K₁'] [IsGalois ℚ K₁'] [IsSepClosure ℚ K₁']

/-- **The existence half of Neukirch–Uchida from a place correspondence and the Shimizu
inputs.**  This is `NK.Reconstruct.exists_sigma_of_localCorrespondence` restated: the local
correspondence (a) is given, together with the Frobenius correspondence *for that `a`*, a prime `ℓ`
and the three rank inputs and Čebotarev. -/
theorem exists_sigma_of_localCorrespondence_shimizu_inst
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (b : NK.Reconstruct.FrobeniusCorrespondencePlace ϕ he a)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hH : NK.Reconstruct.HausRankInput K₁' ℓ)
    (hM : NK.Reconstruct.RankStrictMonoLevelInputGen K₁' ℓ)
    (hR : NK.Reconstruct.ResRankInputGen K₁' ℓ)
    (hc : NK.Reconstruct.ChebotarevInput ℚ K₁')
    : ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ
 :=
  NK.Reconstruct.exists_sigma_of_localCorrespondence ϕ he a b ℓ hH hM hR hc

/-- **Neukirch–Uchida from a place correspondence and the Shimizu inputs**, in the `∃!` form: the
existence half is `exists_sigma_of_localCorrespondence_shimizu`, the uniqueness half the *proved*
`Submission.NeukirchUchida.unique_sigma`. -/
theorem neukirch_uchida_of_localCorrespondence_shimizu_inst
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (b : NK.Reconstruct.FrobeniusCorrespondencePlace ϕ he a)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hH : NK.Reconstruct.HausRankInput K₁' ℓ)
    (hM : NK.Reconstruct.RankStrictMonoLevelInputGen K₁' ℓ)
    (hR : NK.Reconstruct.ResRankInputGen K₁' ℓ)
    (hc : NK.Reconstruct.ChebotarevInput ℚ K₁')
    : ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm)
 := by
  obtain ⟨σ, hσ⟩ :=
    exists_sigma_of_localCorrespondence_shimizu_inst ϕ he a b ℓ hH hM hR hc
  exact ⟨σ, hσ, fun y hy => Submission.NeukirchUchida.unique_sigma ϕ he hy hσ⟩

/-- **The existence half of Neukirch–Uchida from the group-theoretic input (a), block (ii) in the
`LocalGaloisInputsTop` form, and the Shimizu inputs.**

`h` is `Submission.NeukirchUchida.PreservesDecompositionGroups ϕ` (CoNF (12.1.9) "if"), and the
per-prime inputs are the local structure bundles `NK.PTorsionTop.LocalGaloisInputsTop` with the
residue characteristic pinned by `CharP` (the shape of `NK.Mine.neukirch_uchida_of_topData`).
The two arithmetic fields of the place correspondence are *derived* from them by
`NK.Mine.residueChar_preserved_of_topInputs` and `NK.Mine.localDegree_preserved_of_topInputs`,
and the σ-free correspondence is assembled by
`Submission.NeukirchUchida.localCorrespondenceOf`. -/
theorem exists_sigma_of_preserves_shimizu_inst
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
    (hH : NK.Reconstruct.HausRankInput K₁' ℓ)
    (hM : NK.Reconstruct.RankStrictMonoLevelInputGen K₁' ℓ)
    (hR : NK.Reconstruct.ResRankInputGen K₁' ℓ)
    (hc : NK.Reconstruct.ChebotarevInput ℚ K₁')
    : ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ
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
  exact NK.Reconstruct.exists_sigma_of_localCorrespondence ϕ he a (hb a) ℓ hH hM hR hc

/-- **Neukirch–Uchida (CoNF XII Thm 12.2.1) from the group-theoretic input (a), block (ii) in the
`LocalGaloisInputsTop` form, and the Shimizu inputs.**  This is the variant in which
`PreservesDecompositionGroups ϕ` is taken *directly*: a caller who already has block (i) need not
redo the per-prime bookkeeping. -/
theorem neukirch_uchida_of_preserves_shimizu_inst
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
    (hH : NK.Reconstruct.HausRankInput K₁' ℓ)
    (hM : NK.Reconstruct.RankStrictMonoLevelInputGen K₁' ℓ)
    (hR : NK.Reconstruct.ResRankInputGen K₁' ℓ)
    (hc : NK.Reconstruct.ChebotarevInput ℚ K₁')
    : ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm)
 := by
  obtain ⟨σ, hσ⟩ := exists_sigma_of_preserves_shimizu_inst ϕ he h k₁ k₂ hb ℓ hH hM hR hc
  exact ⟨σ, hσ, fun y hy => Submission.NeukirchUchida.unique_sigma ϕ he hy hσ⟩

/-- **Neukirch–Uchida (CoNF XII Thm 12.2.1) from block (i) in the `HasseTwist`/`Indecomposed` form,
block (ii) *already reduced* to the `LocalGaloisInputsTop` form (with the residue characteristic
pinned by `CharP`, as in `NK.Mine.neukirch_uchida_of_topData`), and the Shimizu inputs.**

Block (i) is converted into `PreservesDecompositionGroups ϕ` by
`NK.Indecomposed.preservesDecompositionGroups_of_hasseAt`
(`NK.BrauerTwist.preservesDecompositionGroups_of_localGalois` + the per-prime rank data). -/
theorem neukirch_uchida_of_shimizu_inst
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
    (hH : NK.Reconstruct.HausRankInput K₁' ℓ)
    (hM : NK.Reconstruct.RankStrictMonoLevelInputGen K₁' ℓ)
    (hR : NK.Reconstruct.ResRankInputGen K₁' ℓ)
    (hc : NK.Reconstruct.ChebotarevInput ℚ K₁')
    : ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm)
 :=
  neukirch_uchida_of_preserves_shimizu_inst ϕ he
    (NK.Indecomposed.preservesDecompositionGroups_of_hasseAt ϕ he hB₁ hB₂)
    k₁ k₂ hb ℓ hH hM hR hc

/-- **Neukirch–Uchida (CoNF XII Thm 12.2.1) from block (i) in the `NK.BrauerTwist` form, block (ii)
in the core `TowerRankCore`/`ArtinReciprocity` form, and the Shimizu inputs.**

This is the same endgame with the alternative leaf shape of block (i) used by
`NK.Mine.neukirch_uchida_of_topData`: per finite prime the triple `LocalH2Input`,
`Sha2Vanishing`, `LocalDecompositionCriterion`, converted into `PreservesDecompositionGroups ϕ` by
`NK.BrauerTwist.preservesDecompositionGroups_of_localGalois`. -/
theorem neukirch_uchida_of_brauerTwistLeaves_inst
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (hB₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ, p.Prime ∧
        NK.BrauerTwist.LocalH2Input p K₂ K₂' (𝔭.adicCompletion K₁)
          (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        NK.BrauerTwist.Sha2Vanishing p K₂ K₂' (𝔭.adicCompletion K₁)
          (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        NK.BrauerTwist.LocalDecompositionCriterion p K₂ K₂' (𝔭.adicCompletion K₁)
          (SeparableClosure (𝔭.adicCompletion K₁)))
    (hB₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ p : ℕ, p.Prime ∧
        NK.BrauerTwist.LocalH2Input p K₁ K₁' (𝔮.adicCompletion K₂)
          (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        NK.BrauerTwist.Sha2Vanishing p K₁ K₁' (𝔮.adicCompletion K₂)
          (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        NK.BrauerTwist.LocalDecompositionCriterion p K₁ K₁' (𝔮.adicCompletion K₂)
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
    (hb : ∀ a : NK.Reconstruct.LocalCorrespondence ϕ,
      NK.Reconstruct.FrobeniusCorrespondencePlace ϕ he a)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hH : NK.Reconstruct.HausRankInput K₁' ℓ)
    (hM : NK.Reconstruct.RankStrictMonoLevelInputGen K₁' ℓ)
    (hR : NK.Reconstruct.ResRankInputGen K₁' ℓ)
    (hc : NK.Reconstruct.ChebotarevInput ℚ K₁')
    : ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm)
 :=
  neukirch_uchida_of_preserves_shimizu_inst ϕ he
    (NK.BrauerTwist.preservesDecompositionGroups_of_localGalois ϕ he hB₁ hB₂)
    (fun 𝔭 => exists_localGaloisInputsTop_of_coreData K₁ 𝔭 (k₁ 𝔭))
    (fun 𝔮 => exists_localGaloisInputsTop_of_coreData K₂ 𝔮 (k₂ 𝔮))
    hb ℓ hH hM hR hc

/-- **Neukirch–Uchida (CoNF XII Thm 12.2.1), the endgame of the Shimizu route.**

Inputs:

* **block (i)**, per finite prime of `K₁` and of `K₂`: the `HasseTwist`/`Indecomposed` triple
  `∃ p, Sha2Input p · ∧ RankData p · ∧ LocalReconstruction p ·` (converted into
  `PreservesDecompositionGroups ϕ` by `NK.Indecomposed.preservesDecompositionGroups_of_hasseAt`);
* **block (ii)**, per finite prime: the local class field theory pair
  `NK.LocalStructure.TowerRankCore k 𝔭 (SeparableClosure (𝔭.adicCompletion k)) (ringChar ...)` and
  `Nonempty (NK.LocalCFT.ArtinReciprocity (𝔭.adicCompletion k) (SeparableClosure ...))`
  (converted into `LocalGaloisInputsTop` by `exists_localGaloisInputsTop_of_coreData`);
* **the Shimizu inputs**: a Frobenius correspondence `hb` (σ-free), a prime `ℓ` with
  `[Fact ℓ.Prime]`, the three rank inputs of Shimizu's §4 and Čebotarev;
* the `ℚ`-algebra structure on `K₁'`, its `IsSepClosure` and `IsGalois` are **derived** from
  `[NumberField K₁] [Algebra K₁ K₁'] [IsSepClosure K₁ K₁']` by
  `NK.ReconstructEndgame.ratAlgebra`, `NK.ReconstructEndgame.isSepClosure_rat_of_numberField`
  and `NK.ReconstructEndgame.isGalois_rat_of_numberField`, and the Shimizu hypotheses are stated
  in the `ℚ`-algebra forms of `Submission/Work/ReconstructEndgame/Basic.lean`.

Existence comes from `NK.Reconstruct.exists_sigma_of_localCorrespondence` (block (iii) is exactly
its remaining leaf list), uniqueness from the *proved* `Submission.NeukirchUchida.unique_sigma`. -/
theorem neukirch_uchida_of_reconstructLeaves_inst
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
    (hb : ∀ a : NK.Reconstruct.LocalCorrespondence ϕ,
      NK.Reconstruct.FrobeniusCorrespondencePlace ϕ he a)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hH : NK.Reconstruct.HausRankInput K₁' ℓ)
    (hM : NK.Reconstruct.RankStrictMonoLevelInputGen K₁' ℓ)
    (hR : NK.Reconstruct.ResRankInputGen K₁' ℓ)
    (hc : NK.Reconstruct.ChebotarevInput ℚ K₁')
    : ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm)
 :=
  neukirch_uchida_of_shimizu_inst ϕ he hB₁ hB₂
    (fun 𝔭 => exists_localGaloisInputsTop_of_coreData K₁ 𝔭 (k₁ 𝔭))
    (fun 𝔮 => exists_localGaloisInputsTop_of_coreData K₂ 𝔮 (k₂ 𝔮))
    hb ℓ hH hM hR hc

/-- **The existence half of Neukirch–Uchida from the leaves of the Shimizu route**: block (i) in the
`HasseTwist`/`Indecomposed` form, block (ii) in the core `TowerRankCore`/`ArtinReciprocity` form, and
the Shimizu inputs, producing `∃ σ, Conjugates σ ϕ` (no uniqueness). -/
theorem exists_sigma_of_reconstructLeaves_inst
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
    (hb : ∀ a : NK.Reconstruct.LocalCorrespondence ϕ,
      NK.Reconstruct.FrobeniusCorrespondencePlace ϕ he a)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hH : NK.Reconstruct.HausRankInput K₁' ℓ)
    (hM : NK.Reconstruct.RankStrictMonoLevelInputGen K₁' ℓ)
    (hR : NK.Reconstruct.ResRankInputGen K₁' ℓ)
    (hc : NK.Reconstruct.ChebotarevInput ℚ K₁')
    : ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ
 := by
  obtain ⟨σ, hσ, _⟩ :=
    neukirch_uchida_of_reconstructLeaves_inst ϕ he hB₁ hB₂ k₁ k₂ hb ℓ hH hM hR hc
  exact ⟨σ, hσ⟩

/-- **Neukirch–Uchida (CoNF XII Thm 12.2.1) from `PreservesDecompositionGroups ϕ` together
with the two arithmetic fields of the place correspondence (the residue characteristic and
the local degree) and the Shimizu inputs (`_inst` form).**

This mirrors `NK.Mine.neukirch_uchida_of_decompositionGroups`, with its level-wise input
replaced by the Shimizu inputs and the `σ` produced by
`NK.Reconstruct.exists_sigma_of_localCorrespondence`. -/
theorem neukirch_uchida_of_decompositionGroups_shimizu_inst
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (h : Submission.NeukirchUchida.PreservesDecompositionGroups ϕ)
    (residueChar : ∀ (A : NK.Reconstruct.FinitePlaceOf K₁ K₁') (ℓ : ℕ),
      CharP (NumberField.RingOfIntegers K₁ ⧸
          (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal) ℓ →
        CharP (NumberField.RingOfIntegers K₂ ⧸
          (Submission.NeukirchUchida.primeOf
            (Submission.NeukirchUchida.placeMap ϕ h A).1
            (Submission.NeukirchUchida.placeMap ϕ h A).2).asIdeal) ℓ)
    (localDegree : ∀ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
      (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal.inertiaDeg ℤ *
          (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal.ramificationIdx ℤ =
        (Submission.NeukirchUchida.primeOf
            (Submission.NeukirchUchida.placeMap ϕ h A).1
            (Submission.NeukirchUchida.placeMap ϕ h A).2).asIdeal.inertiaDeg ℤ *
          (Submission.NeukirchUchida.primeOf
            (Submission.NeukirchUchida.placeMap ϕ h A).1
            (Submission.NeukirchUchida.placeMap ϕ h A).2).asIdeal.ramificationIdx ℤ)
    (hb : ∀ a : NK.Reconstruct.LocalCorrespondence ϕ,
      NK.Reconstruct.FrobeniusCorrespondencePlace ϕ he a)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hH : NK.Reconstruct.HausRankInput K₁' ℓ)
    (hM : NK.Reconstruct.RankStrictMonoLevelInputGen K₁' ℓ)
    (hR : NK.Reconstruct.ResRankInputGen K₁' ℓ)
    (hc : NK.Reconstruct.ChebotarevInput ℚ K₁')
    : ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm)
 := by
  exact neukirch_uchida_of_localCorrespondence_shimizu_inst ϕ he
    (Submission.NeukirchUchida.localCorrespondenceOf ϕ h residueChar localDegree)
    (hb (Submission.NeukirchUchida.localCorrespondenceOf ϕ h residueChar localDegree))
    ℓ hH hM hR hc

end WithInstances

section Derived

/-! ## The Shimizu endgame with the `ℚ`-structure derived

The theorems in this section carry **no** `ℚ`-algebra hypothesis on `K₁'`: the structure
`NK.ReconstructEndgame.ratAlgebra K₁ K₁'`, the instance `IsSepClosure ℚ K₁'` and (through it)
`IsGalois ℚ K₁'` are derived from `[NumberField K₁] [Algebra K₁ K₁'] [IsSepClosure K₁ K₁']` inside
the proofs by `NK.ReconstructEndgame.isSepClosure_rat_of_numberField` and
`NK.ReconstructEndgame.isGalois_rat_of_numberField`, and the Shimizu hypotheses are stated in the
`ℚ`-algebra forms `HausRankInputDerived`, `RankStrictMonoLevelInputGenDerived`,
`ResRankInputGenDerived`, `ChebotarevInputDerived` of
`Submission/Work/ReconstructEndgame/Basic.lean`. -/

variable {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The existence half of Neukirch–Uchida from a place correspondence and the Shimizu
inputs.**  This is `NK.Reconstruct.exists_sigma_of_localCorrespondence` restated: the local
correspondence (a) is given, together with the Frobenius correspondence *for that `a`*, a prime `ℓ`
and the three rank inputs and Čebotarev.  The `ℚ`-algebra structure on `K₁'` is derived from
`[NumberField K₁] [Algebra K₁ K₁'] [IsSepClosure K₁ K₁']`. -/
theorem exists_sigma_of_localCorrespondence_shimizu
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (b : NK.Reconstruct.FrobeniusCorrespondencePlace ϕ he a)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hH : HausRankInputDerived K₁ K₁' ℓ)
    (hM : RankStrictMonoLevelInputGenDerived K₁ K₁' ℓ)
    (hR : ResRankInputGenDerived K₁ K₁' ℓ)
    (hc : ChebotarevInputDerived K₁ K₁')
    : ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ
 := by
  letI : Algebra ℚ K₁' := ratAlgebra K₁ K₁'
  haveI : IsSepClosure ℚ K₁' := isSepClosure_rat_of_numberField K₁ K₁'
  haveI : IsGalois ℚ K₁' := isGalois_rat_of_numberField K₁ K₁'
  exact exists_sigma_of_localCorrespondence_shimizu_inst ϕ he a b ℓ hH hM hR hc

/-- **Neukirch–Uchida from a place correspondence and the Shimizu inputs**, in the `∃!` form: the
existence half is `exists_sigma_of_localCorrespondence_shimizu`, the uniqueness half the *proved*
`Submission.NeukirchUchida.unique_sigma`.  The `ℚ`-algebra structure on `K₁'` is derived from
`[NumberField K₁] [Algebra K₁ K₁'] [IsSepClosure K₁ K₁']`. -/
theorem neukirch_uchida_of_localCorrespondence_shimizu
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (b : NK.Reconstruct.FrobeniusCorrespondencePlace ϕ he a)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hH : HausRankInputDerived K₁ K₁' ℓ)
    (hM : RankStrictMonoLevelInputGenDerived K₁ K₁' ℓ)
    (hR : ResRankInputGenDerived K₁ K₁' ℓ)
    (hc : ChebotarevInputDerived K₁ K₁')
    : ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm)
 := by
  letI : Algebra ℚ K₁' := ratAlgebra K₁ K₁'
  haveI : IsSepClosure ℚ K₁' := isSepClosure_rat_of_numberField K₁ K₁'
  haveI : IsGalois ℚ K₁' := isGalois_rat_of_numberField K₁ K₁'
  exact neukirch_uchida_of_localCorrespondence_shimizu_inst ϕ he a b ℓ hH hM hR hc

/-- **The existence half of Neukirch–Uchida from the group-theoretic input (a), block (ii) in the
`LocalGaloisInputsTop` form, and the Shimizu inputs.**

`h` is `Submission.NeukirchUchida.PreservesDecompositionGroups ϕ` (CoNF (12.1.9) "if"), and the
per-prime inputs are the local structure bundles `NK.PTorsionTop.LocalGaloisInputsTop` with the
residue characteristic pinned by `CharP` (the shape of `NK.Mine.neukirch_uchida_of_topData`).
The two arithmetic fields of the place correspondence are *derived* from them by
`NK.Mine.residueChar_preserved_of_topInputs` and `NK.Mine.localDegree_preserved_of_topInputs`,
and the σ-free correspondence is assembled by
`Submission.NeukirchUchida.localCorrespondenceOf`.  The `ℚ`-algebra structure on `K₁'` is derived from
`[NumberField K₁] [Algebra K₁ K₁'] [IsSepClosure K₁ K₁']`. -/
theorem exists_sigma_of_preserves_shimizu
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
    (hH : HausRankInputDerived K₁ K₁' ℓ)
    (hM : RankStrictMonoLevelInputGenDerived K₁ K₁' ℓ)
    (hR : ResRankInputGenDerived K₁ K₁' ℓ)
    (hc : ChebotarevInputDerived K₁ K₁')
    : ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ
 := by
  letI : Algebra ℚ K₁' := ratAlgebra K₁ K₁'
  haveI : IsSepClosure ℚ K₁' := isSepClosure_rat_of_numberField K₁ K₁'
  haveI : IsGalois ℚ K₁' := isGalois_rat_of_numberField K₁ K₁'
  exact exists_sigma_of_preserves_shimizu_inst ϕ he h k₁ k₂ hb ℓ hH hM hR hc

/-- **Neukirch–Uchida (CoNF XII Thm 12.2.1) from the group-theoretic input (a), block (ii) in the
`LocalGaloisInputsTop` form, and the Shimizu inputs.**  This is the variant in which
`PreservesDecompositionGroups ϕ` is taken *directly*: a caller who already has block (i) need not
redo the per-prime bookkeeping.  The `ℚ`-algebra structure on `K₁'` is derived from
`[NumberField K₁] [Algebra K₁ K₁'] [IsSepClosure K₁ K₁']`. -/
theorem neukirch_uchida_of_preserves_shimizu
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
    (hH : HausRankInputDerived K₁ K₁' ℓ)
    (hM : RankStrictMonoLevelInputGenDerived K₁ K₁' ℓ)
    (hR : ResRankInputGenDerived K₁ K₁' ℓ)
    (hc : ChebotarevInputDerived K₁ K₁')
    : ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm)
 := by
  letI : Algebra ℚ K₁' := ratAlgebra K₁ K₁'
  haveI : IsSepClosure ℚ K₁' := isSepClosure_rat_of_numberField K₁ K₁'
  haveI : IsGalois ℚ K₁' := isGalois_rat_of_numberField K₁ K₁'
  exact neukirch_uchida_of_preserves_shimizu_inst ϕ he h k₁ k₂ hb ℓ hH hM hR hc

/-- **Neukirch–Uchida (CoNF XII Thm 12.2.1) from block (i) in the `HasseTwist`/`Indecomposed` form,
block (ii) *already reduced* to the `LocalGaloisInputsTop` form (with the residue characteristic
pinned by `CharP`, as in `NK.Mine.neukirch_uchida_of_topData`), and the Shimizu inputs.**

Block (i) is converted into `PreservesDecompositionGroups ϕ` by
`NK.Indecomposed.preservesDecompositionGroups_of_hasseAt`
(`NK.BrauerTwist.preservesDecompositionGroups_of_localGalois` + the per-prime rank data).  The `ℚ`-algebra structure on `K₁'` is derived from
`[NumberField K₁] [Algebra K₁ K₁'] [IsSepClosure K₁ K₁']`. -/
theorem neukirch_uchida_of_shimizu
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
    (hH : HausRankInputDerived K₁ K₁' ℓ)
    (hM : RankStrictMonoLevelInputGenDerived K₁ K₁' ℓ)
    (hR : ResRankInputGenDerived K₁ K₁' ℓ)
    (hc : ChebotarevInputDerived K₁ K₁')
    : ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm)
 := by
  letI : Algebra ℚ K₁' := ratAlgebra K₁ K₁'
  haveI : IsSepClosure ℚ K₁' := isSepClosure_rat_of_numberField K₁ K₁'
  haveI : IsGalois ℚ K₁' := isGalois_rat_of_numberField K₁ K₁'
  exact neukirch_uchida_of_shimizu_inst ϕ he hB₁ hB₂ k₁ k₂ hb ℓ hH hM hR hc

/-- **Neukirch–Uchida (CoNF XII Thm 12.2.1) from block (i) in the `NK.BrauerTwist` form, block (ii)
in the core `TowerRankCore`/`ArtinReciprocity` form, and the Shimizu inputs.**

This is the same endgame with the alternative leaf shape of block (i) used by
`NK.Mine.neukirch_uchida_of_topData`: per finite prime the triple `LocalH2Input`,
`Sha2Vanishing`, `LocalDecompositionCriterion`, converted into `PreservesDecompositionGroups ϕ` by
`NK.BrauerTwist.preservesDecompositionGroups_of_localGalois`.  The `ℚ`-algebra structure on `K₁'` is derived from
`[NumberField K₁] [Algebra K₁ K₁'] [IsSepClosure K₁ K₁']`. -/
theorem neukirch_uchida_of_brauerTwistLeaves
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (hB₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ, p.Prime ∧
        NK.BrauerTwist.LocalH2Input p K₂ K₂' (𝔭.adicCompletion K₁)
          (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        NK.BrauerTwist.Sha2Vanishing p K₂ K₂' (𝔭.adicCompletion K₁)
          (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        NK.BrauerTwist.LocalDecompositionCriterion p K₂ K₂' (𝔭.adicCompletion K₁)
          (SeparableClosure (𝔭.adicCompletion K₁)))
    (hB₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ p : ℕ, p.Prime ∧
        NK.BrauerTwist.LocalH2Input p K₁ K₁' (𝔮.adicCompletion K₂)
          (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        NK.BrauerTwist.Sha2Vanishing p K₁ K₁' (𝔮.adicCompletion K₂)
          (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        NK.BrauerTwist.LocalDecompositionCriterion p K₁ K₁' (𝔮.adicCompletion K₂)
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
    (hb : ∀ a : NK.Reconstruct.LocalCorrespondence ϕ,
      NK.Reconstruct.FrobeniusCorrespondencePlace ϕ he a)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hH : HausRankInputDerived K₁ K₁' ℓ)
    (hM : RankStrictMonoLevelInputGenDerived K₁ K₁' ℓ)
    (hR : ResRankInputGenDerived K₁ K₁' ℓ)
    (hc : ChebotarevInputDerived K₁ K₁')
    : ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm)
 := by
  letI : Algebra ℚ K₁' := ratAlgebra K₁ K₁'
  haveI : IsSepClosure ℚ K₁' := isSepClosure_rat_of_numberField K₁ K₁'
  haveI : IsGalois ℚ K₁' := isGalois_rat_of_numberField K₁ K₁'
  exact neukirch_uchida_of_brauerTwistLeaves_inst ϕ he hB₁ hB₂ k₁ k₂ hb ℓ hH hM hR hc

/-- **Neukirch–Uchida (CoNF XII Thm 12.2.1), the endgame of the Shimizu route.**

Inputs:

* **block (i)**, per finite prime of `K₁` and of `K₂`: the `HasseTwist`/`Indecomposed` triple
  `∃ p, Sha2Input p · ∧ RankData p · ∧ LocalReconstruction p ·` (converted into
  `PreservesDecompositionGroups ϕ` by `NK.Indecomposed.preservesDecompositionGroups_of_hasseAt`);
* **block (ii)**, per finite prime: the local class field theory pair
  `NK.LocalStructure.TowerRankCore k 𝔭 (SeparableClosure (𝔭.adicCompletion k)) (ringChar ...)` and
  `Nonempty (NK.LocalCFT.ArtinReciprocity (𝔭.adicCompletion k) (SeparableClosure ...))`
  (converted into `LocalGaloisInputsTop` by `exists_localGaloisInputsTop_of_coreData`);
* **the Shimizu inputs**: a Frobenius correspondence `hb` (σ-free), a prime `ℓ` with
  `[Fact ℓ.Prime]`, the three rank inputs of Shimizu's §4 and Čebotarev;
* the `ℚ`-algebra structure on `K₁'`, its `IsSepClosure` and `IsGalois` are **derived** from
  `[NumberField K₁] [Algebra K₁ K₁'] [IsSepClosure K₁ K₁']` by
  `NK.ReconstructEndgame.ratAlgebra`, `NK.ReconstructEndgame.isSepClosure_rat_of_numberField`
  and `NK.ReconstructEndgame.isGalois_rat_of_numberField`, and the Shimizu hypotheses are stated
  in the `ℚ`-algebra forms of `Submission/Work/ReconstructEndgame/Basic.lean`.

Existence comes from `NK.Reconstruct.exists_sigma_of_localCorrespondence` (block (iii) is exactly
its remaining leaf list), uniqueness from the *proved* `Submission.NeukirchUchida.unique_sigma`.  The `ℚ`-algebra structure on `K₁'` is derived from
`[NumberField K₁] [Algebra K₁ K₁'] [IsSepClosure K₁ K₁']`. -/
theorem neukirch_uchida_of_reconstructLeaves
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
    (hb : ∀ a : NK.Reconstruct.LocalCorrespondence ϕ,
      NK.Reconstruct.FrobeniusCorrespondencePlace ϕ he a)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hH : HausRankInputDerived K₁ K₁' ℓ)
    (hM : RankStrictMonoLevelInputGenDerived K₁ K₁' ℓ)
    (hR : ResRankInputGenDerived K₁ K₁' ℓ)
    (hc : ChebotarevInputDerived K₁ K₁')
    : ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm)
 := by
  letI : Algebra ℚ K₁' := ratAlgebra K₁ K₁'
  haveI : IsSepClosure ℚ K₁' := isSepClosure_rat_of_numberField K₁ K₁'
  haveI : IsGalois ℚ K₁' := isGalois_rat_of_numberField K₁ K₁'
  exact neukirch_uchida_of_reconstructLeaves_inst ϕ he hB₁ hB₂ k₁ k₂ hb ℓ hH hM hR hc

/-- **The existence half of Neukirch–Uchida from the leaves of the Shimizu route**: block (i) in the
`HasseTwist`/`Indecomposed` form, block (ii) in the core `TowerRankCore`/`ArtinReciprocity` form, and
the Shimizu inputs, producing `∃ σ, Conjugates σ ϕ` (no uniqueness).  The `ℚ`-algebra structure on `K₁'` is derived from
`[NumberField K₁] [Algebra K₁ K₁'] [IsSepClosure K₁ K₁']`. -/
theorem exists_sigma_of_reconstructLeaves
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
    (hb : ∀ a : NK.Reconstruct.LocalCorrespondence ϕ,
      NK.Reconstruct.FrobeniusCorrespondencePlace ϕ he a)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hH : HausRankInputDerived K₁ K₁' ℓ)
    (hM : RankStrictMonoLevelInputGenDerived K₁ K₁' ℓ)
    (hR : ResRankInputGenDerived K₁ K₁' ℓ)
    (hc : ChebotarevInputDerived K₁ K₁')
    : ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ
 := by
  letI : Algebra ℚ K₁' := ratAlgebra K₁ K₁'
  haveI : IsSepClosure ℚ K₁' := isSepClosure_rat_of_numberField K₁ K₁'
  haveI : IsGalois ℚ K₁' := isGalois_rat_of_numberField K₁ K₁'
  exact exists_sigma_of_reconstructLeaves_inst ϕ he hB₁ hB₂ k₁ k₂ hb ℓ hH hM hR hc

/-- **Neukirch–Uchida (CoNF XII Thm 12.2.1) from `PreservesDecompositionGroups ϕ` together
with the two arithmetic fields of the place correspondence (the residue characteristic and
the local degree) and the Shimizu inputs.**

This mirrors `NK.Mine.neukirch_uchida_of_decompositionGroups`, with its level-wise input
replaced by the Shimizu inputs and the `σ` produced by
`NK.Reconstruct.exists_sigma_of_localCorrespondence`.  The `ℚ`-algebra structure on `K₁'`
is derived from `[NumberField K₁] [Algebra K₁ K₁'] [IsSepClosure K₁ K₁']`. -/
theorem neukirch_uchida_of_decompositionGroups_shimizu
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (h : Submission.NeukirchUchida.PreservesDecompositionGroups ϕ)
    (residueChar : ∀ (A : NK.Reconstruct.FinitePlaceOf K₁ K₁') (ℓ : ℕ),
      CharP (NumberField.RingOfIntegers K₁ ⧸
          (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal) ℓ →
        CharP (NumberField.RingOfIntegers K₂ ⧸
          (Submission.NeukirchUchida.primeOf
            (Submission.NeukirchUchida.placeMap ϕ h A).1
            (Submission.NeukirchUchida.placeMap ϕ h A).2).asIdeal) ℓ)
    (localDegree : ∀ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
      (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal.inertiaDeg ℤ *
          (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal.ramificationIdx ℤ =
        (Submission.NeukirchUchida.primeOf
            (Submission.NeukirchUchida.placeMap ϕ h A).1
            (Submission.NeukirchUchida.placeMap ϕ h A).2).asIdeal.inertiaDeg ℤ *
          (Submission.NeukirchUchida.primeOf
            (Submission.NeukirchUchida.placeMap ϕ h A).1
            (Submission.NeukirchUchida.placeMap ϕ h A).2).asIdeal.ramificationIdx ℤ)
    (hb : ∀ a : NK.Reconstruct.LocalCorrespondence ϕ,
      NK.Reconstruct.FrobeniusCorrespondencePlace ϕ he a)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hH : HausRankInputDerived K₁ K₁' ℓ)
    (hM : RankStrictMonoLevelInputGenDerived K₁ K₁' ℓ)
    (hR : ResRankInputGenDerived K₁ K₁' ℓ)
    (hc : ChebotarevInputDerived K₁ K₁')
    : ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm)
 := by
  letI : Algebra ℚ K₁' := ratAlgebra K₁ K₁'
  haveI : IsSepClosure ℚ K₁' := isSepClosure_rat_of_numberField K₁ K₁'
  haveI : IsGalois ℚ K₁' := isGalois_rat_of_numberField K₁ K₁'
  exact neukirch_uchida_of_decompositionGroups_shimizu_inst ϕ he h residueChar
    localDegree hb ℓ hH hM hR hc

end Derived

end NK.ReconstructEndgame
