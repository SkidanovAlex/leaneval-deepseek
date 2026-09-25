import Submission.NK.HasseTwist.All
import Submission.NK.Mine.NeukirchUchidaOfTopData

/-!
# The endgame with the Hasse principle discharged

*SUPERSEDED* (session 27, later): the sharpest current capstone is
`NK.Mine.neukirch_uchida_of_finalLeaves` in `Submission/Work/Mine/FinalLeaves.lean`, which
additionally removes the `LocalH2Input` and `LocalDecompositionCriterion` hypotheses (deriving them
from `NK.Indecomposed.RankData` + `LocalReconstruction`).  This file is kept as the co-import
witness for the repaired commons (see below) and as a shorter historical form.

`NK.Mine.neukirch_uchida_of_topData` proves the `∃!` form of CoNF XII Thm 12.2.1 from
`NK.BrauerTwist.Sha2Vanishing`, i.e. the μ_p-twisted Hasse–Brauer–Noether principle.  That
principle is *proved* in `Submission/Work/HasseTwist/`
(`NK.HasseTwist.sha2Vanishing : Sha2Input p K K' κ κ' → NK.BrauerTwist.Sha2Vanishing p K K' κ κ'`,
from the audited catalogue `NK.HasseTwist.Sha2Input`).  This file composes the two, so that the
Hasse principle no longer occurs as a hypothesis of the endgame.

It is also the `import`-level check that the two chapters
`Submission.NK.HasseTwist.All` and `Submission.NK.PTorsionTop.All` can be co-imported: they
could not be, before the duplicate commons declaration
`Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois_coe`
of `Submission/Commons/NumberTheory/NumberField/Completion/exists_inertiaSubgroup_adicCompletion_card_eq_ramificationIdx.lean`
was renamed (to `..._coe_adicCompletion`); see `ROADMAP.md`, session 26 blocker section.
-/

namespace NK.Mine

open scoped Pointwise
open IsDedekindDomain.HeightOneSpectrum

universe u

variable {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **Neukirch–Uchida from the corrected local inputs and the Hasse principle's *inputs*.**

The three per-prime groups are

* the μ_p-twisted local Brauer computation `NK.BrauerTwist.LocalH2Input`;
* the audited catalogue `NK.HasseTwist.Sha2Input` of the Hasse principle (Hasse norm theorem,
  labelled level-wise Hasse–Brauer–Noether, exhaustion of the kernel of localisation) — the
  *result* `NK.BrauerTwist.Sha2Vanishing` is produced from it by
  `NK.HasseTwist.sha2Vanishing`;
* Neukirch's local finishing step `NK.BrauerTwist.LocalDecompositionCriterion`;

together with the corrected local structure bundle `NK.PTorsionTop.LocalGaloisInputsTop`
(with the residue characteristic) at every finite prime, and the level-wise weak Neukirch–Uchida
input `NK.ReconstructField.LevelIsoInput`.

Everything else — the local correspondence's arithmetic fields, the homeomorphy of the local
correspondence, and the uniqueness half — is a theorem of this workspace. -/
theorem neukirch_uchida_of_coreInputs
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (hB₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ, p.Prime ∧
        NK.BrauerTwist.LocalH2Input p K₂ K₂'
          (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        NK.HasseTwist.Sha2Input p K₂ K₂'
          (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        NK.BrauerTwist.LocalDecompositionCriterion p K₂ K₂'
          (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)))
    (hB₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ p : ℕ, p.Prime ∧
        NK.BrauerTwist.LocalH2Input p K₁ K₁'
          (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        NK.HasseTwist.Sha2Input p K₁ K₁'
          (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        NK.BrauerTwist.LocalDecompositionCriterion p K₁ K₁'
          (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)))
    (k₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ, p.Prime ∧
        CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K₁)) p ∧
        NK.PTorsionTop.LocalGaloisInputsTop K₁ 𝔭
          (SeparableClosure (𝔭.adicCompletion K₁)) p)
    (k₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ q : ℕ, q.Prime ∧
        CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K₂)) q ∧
        NK.PTorsionTop.LocalGaloisInputsTop K₂ 𝔮
          (SeparableClosure (𝔮.adicCompletion K₂)) q)
    (hlev : NK.ReconstructField.LevelIsoInput ϕ he) :
    ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) := by
  have hB₁' : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ, p.Prime ∧
        NK.BrauerTwist.LocalH2Input p K₂ K₂'
          (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        NK.BrauerTwist.Sha2Vanishing p K₂ K₂'
          (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        NK.BrauerTwist.LocalDecompositionCriterion p K₂ K₂'
          (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)) := by
    intro 𝔭
    obtain ⟨p, hp, h1, h2, h3⟩ := hB₁ 𝔭
    exact ⟨p, hp, h1, NK.HasseTwist.sha2Vanishing p h2, h3⟩
  have hB₂' : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ p : ℕ, p.Prime ∧
        NK.BrauerTwist.LocalH2Input p K₁ K₁'
          (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        NK.BrauerTwist.Sha2Vanishing p K₁ K₁'
          (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        NK.BrauerTwist.LocalDecompositionCriterion p K₁ K₁'
          (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)) := by
    intro 𝔮
    obtain ⟨p, hp, h1, h2, h3⟩ := hB₂ 𝔮
    exact ⟨p, hp, h1, NK.HasseTwist.sha2Vanishing p h2, h3⟩
  exact neukirch_uchida_of_topData ϕ he hB₁' hB₂' k₁ k₂ hlev

end NK.Mine
