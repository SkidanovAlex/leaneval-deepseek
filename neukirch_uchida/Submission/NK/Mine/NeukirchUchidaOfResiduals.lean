
/-
## WARNING (session 28): this file's rank hypothesis is REFUTED; use the repaired version

`NK.RankTheoryDeep` (delivered in session 28) proves, for the workspace's definitions, that
`NK.ShimizuRank.GammaTFRankFinite Ω ℓ` is **false** for every prime `ℓ`
(`NK.RankTheoryDeep.not_gammaTFRankFinite_prime`), hence `NK.ShimizuRank.Residuals Ω ℓ` is
unsatisfiable, hence **`NK.Mine.ResidualsDerived K K' ℓ` is false**
(`NK.RankTheoryDeep.not_residualsDerived`, `Submission/Work/RankTheoryDeep/ResidualsDerived.lean`).
The theorems below are therefore **vacuous** as stated: their hypothesis has no instances.

The cause is a formalisation defect (the workspace's `Gamma`/`GammaTF` are not the classically
relevant objects; `rankGamma` is `Module.finrank`, hence `0` whenever the rank is infinite, and for
`K = ℚ` the torsion-free quotient in question has infinite `ℤ_ℓ`-rank), see `ROADMAP.md` §8.

The repair — same endgame with `NK.RankTheoryDeep.CorrectedResidualsDeep` in place of
`Residuals` — is being built in **`Submission/Work/EndgameRepair/`**; use
`NK.EndgameRepair.exists_sigma_of_correctedResiduals` (resp. the repaired wall
`NK.EndgameRepair.ClassicalChaptersRepaired`) instead of the declarations of this file.
-/

import Submission.NK.ReconstructEndgame.FrobeniusInput
import Submission.NK.ShimizuRank.All

/-!
# The Shimizu endgame with the whole rank theory reduced to `NK.ShimizuRank.Residuals`

`Submission/Work/ShimizuRank/` reduces the three Iwasawa-theoretic rank inputs of the Shimizu route
(`HausRankInput`, `RankStrictMonoLevelInputGen`, `ResRankInputGen`) to the single structure
`NK.ShimizuRank.Residuals`.  This file composes that reduction with the endgame
`NK.ReconstructEndgame.neukirch_uchida_of_localStructureData`, so that the capstone below has
**one** rank hypothesis instead of three.

The rank inputs are predicates on `K₁'` as a `ℚ`-algebra; the challenge's fields only carry
`[NumberField K₁] [Algebra K₁ K₁'] [IsSepClosure K₁ K₁']`.  `ResidualsDerived` is the `letI`-form of
`NK.ShimizuRank.Residuals` with the `ℚ`-structure (and the derived `IsSepClosure`/`IsGalois`)
supplied by `Submission/Work/ReconstructEndgame/Basic.lean`, so the capstone can be *stated* without
a `ℚ`-algebra hypothesis.

## Contents

* `NK.Mine.ResidualsDerived` — `NK.ShimizuRank.Residuals` in the derived `ℚ`-algebra form;
* `NK.Mine.neukirch_uchida_of_localStructureData_residuals` — the `∃!` form of CoNF XII
  Thm 12.2.1 from blocks (i), (ii), the local structure data at every place, the single residual
  rank structure and Čebotarev;
* `NK.Mine.neukirch_uchida_of_reconstructLeaves_residuals` — the same with the Frobenius
  correspondence `hb` as an input instead of the local structure data.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open IsDedekindDomain.HeightOneSpectrum

universe u

namespace NK.Mine

/-- **Shimizu's residual rank structure in the derived `ℚ`-algebra form.**

This is *definitionally* `NK.ShimizuRank.Residuals K' ℓ` with the `ℚ`-algebra structure on `K'`
(and the instances `IsSepClosure ℚ K'`, `IsGalois ℚ K'`) derived from `[NumberField K] [Algebra K
K'] [IsSepClosure K K']`, so a caller who has no `ℚ`-structure in scope can still state the rank
hypothesis. -/
def ResidualsDerived (K : Type u) (K' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  letI : Algebra ℚ K' := NK.ReconstructEndgame.ratAlgebra K K'
  letI : IsSepClosure ℚ K' := NK.ReconstructEndgame.isSepClosure_rat_of_numberField K K'
  letI : IsGalois ℚ K' := NK.ReconstructEndgame.isGalois_rat_of_numberField K K'
  NK.ShimizuRank.Residuals K' ℓ

section Endgame

variable {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The `∃!` form of Neukirch–Uchida (CoNF XII Thm 12.2.1)** from the leaves of the Shimizu
route with the rank theory reduced to `NK.ShimizuRank.Residuals`.

The hypotheses are exactly: block (i) at the finite primes of `K₁` and of `K₂`
(`hB₁`, `hB₂`), block (ii) at the finite primes of the two fields (`k₁`, `k₂`), the local structure
data at every finite place (`h₁`, `h₂`), a prime `ℓ`, the residual rank structure, and Čebotarev. -/
theorem neukirch_uchida_of_localStructureData_residuals
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
    (hres : ResidualsDerived K₁ K₁' ℓ)
    (hc : NK.ReconstructEndgame.ChebotarevInputDerived K₁ K₁')
    : ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) := by
  letI : Algebra ℚ K₁' := NK.ReconstructEndgame.ratAlgebra K₁ K₁'
  haveI : IsSepClosure ℚ K₁' := NK.ReconstructEndgame.isSepClosure_rat_of_numberField K₁ K₁'
  haveI : IsGalois ℚ K₁' := NK.ReconstructEndgame.isGalois_rat_of_numberField K₁ K₁'
  obtain ⟨hH, hM, hR⟩ :=
    NK.ShimizuRank.rankInputs (show NK.ShimizuRank.Residuals K₁' ℓ from hres)
  exact NK.ReconstructEndgame.neukirch_uchida_of_localStructureData ϕ he hB₁ hB₂ k₁ k₂ h₁ h₂ ℓ
    hH hM hR hc

/-- The same capstone with the Frobenius correspondence `hb` as an explicit input (instead of the
local structure data at every place). -/
theorem neukirch_uchida_of_reconstructLeaves_residuals
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
    (hres : ResidualsDerived K₁ K₁' ℓ)
    (hc : NK.ReconstructEndgame.ChebotarevInputDerived K₁ K₁')
    : ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) := by
  letI : Algebra ℚ K₁' := NK.ReconstructEndgame.ratAlgebra K₁ K₁'
  haveI : IsSepClosure ℚ K₁' := NK.ReconstructEndgame.isSepClosure_rat_of_numberField K₁ K₁'
  haveI : IsGalois ℚ K₁' := NK.ReconstructEndgame.isGalois_rat_of_numberField K₁ K₁'
  obtain ⟨hH, hM, hR⟩ :=
    NK.ShimizuRank.rankInputs (show NK.ShimizuRank.Residuals K₁' ℓ from hres)
  exact NK.ReconstructEndgame.neukirch_uchida_of_reconstructLeaves ϕ he hB₁ hB₂ k₁ k₂ hb ℓ
    hH hM hR hc

end Endgame

end NK.Mine
