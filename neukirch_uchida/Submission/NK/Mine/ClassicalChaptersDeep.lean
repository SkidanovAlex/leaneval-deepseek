
/-
## WARNING (session 28): the rank field of this wall is REFUTED

`NK.RankTheoryDeep` proves `¬ NK.Mine.ResidualsDerived K K' ℓ` for every prime `ℓ` (see
`Submission/Work/RankTheoryDeep/ResidualsDerived.lean` and `ROADMAP.md` §8), so the structure
`NK.Mine.ClassicalChaptersDeep` and the walls `NK.Mine.ClassicalChapters` have **no instances**
and the capstones below are vacuous.  The repaired wall, with the rank field
`∀ ℓ [Fact ℓ.Prime], NK.RankTheoryDeep.CorrectedResidualsDerived K₁ K₁' ℓ`, is being built in
`Submission/Work/EndgameRepair/` (`NK.EndgameRepair.ClassicalChaptersRepaired`).
-/

import Submission.NK.Mine.ClassicalChapters
import Submission.NK.IndecomposedDeep.All

/-!
# The classical-input wall, with block (i) supplied by `Submission/Work/IndecomposedDeep/`

`Submission/Work/IndecomposedDeep/` has *instantiated* the two structures of block (i) of the
Neukirch–Uchida endgame — `NK.Indecomposed.RankData` and `NK.Indecomposed.LocalReconstruction`
— from the bundled classical catalogue `NK.IndecomposedDeep.DeepInputs`, and has proved the
per-prime form `NK.IndecomposedDeep.perPrime_residuals` consumed by
`NK.Mine.neukirch_uchida_of_localStructureData_residuals`.

This file re-states the wall `NK.Mine.ClassicalChapters` of
`Submission/Work/Mine/ClassicalChapters.lean` with that reduction folded in: block (i) is now the
per-prime pair (`NK.HasseTwist.Sha2Input`, `DeepInputs`) instead of the raw triple
(`Sha2Input`, `RankData`, `LocalReconstruction`), and the capstone
`NK.Mine.neukirch_uchida_of_deepChapters` is the `∃!` form of CoNF XII Thm 12.2.1 from it.

The remaining hypotheses are therefore, per finite prime:

* `NK.HasseTwist.Sha2Input p ·` — the μ_p-twisted Hasse catalogue (global class field theory);
* `NK.IndecomposedDeep.DeepInputs p ·` — local class field theory (`LocalFieldBrauerCyclic`),
  the two labelling inputs (`GlobalBrauerTransport`, `LocalSubgroupClosed`), the local-group
  Brauer computation (`LocalGroupBrauer`), Neukirch's surjectivity NSW (9.2.1)
  (`NeukirchH2modifiedsurj`), Ivanov's `lm:locfinindex` (`LocalInjectionFiniteIndex`) and
  Neukirch's Theorem 1 (`IndexOneOfSelfNormalizing`);

together with block (ii) (`NK.LocalStructure.TowerRankCore` + `Nonempty
(NK.LocalCFT.ArtinReciprocity)` at every finite prime), the local structure data
`NK.ResidueFrob.LocalStructureData` at every finite place, Shimizu's rank structure
`NK.Mine.ResidualsDerived` at one prime `ℓ`, and Čebotarev
(`NK.ReconstructEndgame.ChebotarevInputDerived`).  See `ROADMAP.md` §12 and the READMEs of the
areas for the current status of each.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open IsDedekindDomain.HeightOneSpectrum

universe u

namespace NK.Mine

/-- **The classical-input wall of Neukirch–Uchida, with block (i) reduced by
`Submission/Work/IndecomposedDeep/`.**  See the module docstring for the reading of the fields. -/
structure ClassicalChaptersDeep (K₁ K₂ K₁' K₂' : Type u) [Field K₁] [Field K₂] [Field K₁']
    [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] : Prop where
  /-- **block (i) at the primes of `K₁`**: the μ_p-twisted Hasse catalogue and the classical
  catalogue `DeepInputs`, at the completion `K₁_𝔭` and the global field `K₂`. -/
  hasse₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
    ∃ p : ℕ,
      NK.HasseTwist.Sha2Input p K₂ K₂' (𝔭.adicCompletion K₁)
        (SeparableClosure (𝔭.adicCompletion K₁)) ∧
      NK.IndecomposedDeep.DeepInputs p K₂ K₂' (𝔭.adicCompletion K₁)
        (SeparableClosure (𝔭.adicCompletion K₁))
  /-- **block (i) at the primes of `K₂`**. -/
  hasse₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
    ∃ p : ℕ,
      NK.HasseTwist.Sha2Input p K₁ K₁' (𝔮.adicCompletion K₂)
        (SeparableClosure (𝔮.adicCompletion K₂)) ∧
      NK.IndecomposedDeep.DeepInputs p K₁ K₁' (𝔮.adicCompletion K₂)
        (SeparableClosure (𝔮.adicCompletion K₂))
  /-- **block (ii) at the primes of `K₁`**: the tower ranks and local class field theory. -/
  localCft₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
    NK.LocalStructure.TowerRankCore K₁ 𝔭 (SeparableClosure (𝔭.adicCompletion K₁))
      (ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K₁))) ∧
    Nonempty (NK.LocalCFT.ArtinReciprocity (𝔭.adicCompletion K₁)
      (SeparableClosure (𝔭.adicCompletion K₁)))
  /-- **block (ii) at the primes of `K₂`**. -/
  localCft₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
    NK.LocalStructure.TowerRankCore K₂ 𝔮 (SeparableClosure (𝔮.adicCompletion K₂))
      (ringChar (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K₂))) ∧
    Nonempty (NK.LocalCFT.ArtinReciprocity (𝔮.adicCompletion K₂)
      (SeparableClosure (𝔮.adicCompletion K₂)))
  /-- **input (iii) at the places of `K₁`**: the tame structure of `G_κ`. -/
  localStructure₁ : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K₁ K₁',
    NK.ResidueFrob.LocalStructureData K₁ K₁' A
  /-- **input (iii) at the places of `K₂`**. -/
  localStructure₂ : ∀ B : NK.FrobeniusBridge.FinitePlaceOf K₂ K₂',
    NK.ResidueFrob.LocalStructureData K₂ K₂' B
  /-- **input (iv)**: Shimizu's rank theory, at every prime `ℓ`. -/
  residuals : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ResidualsDerived K₁ K₁' ℓ
  /-- **input (v)**: Čebotarev's density theorem. -/
  chebotarev : NK.ReconstructEndgame.ChebotarevInputDerived K₁ K₁'

section Endgame

variable {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **Neukirch–Uchida (CoNF XII Thm 12.2.1) from the wall with block (i) reduced.** -/
theorem neukirch_uchida_of_deepChapters (h : ClassicalChaptersDeep K₁ K₂ K₁' K₂')
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    : ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) := by
  classical
  exact NK.IndecomposedDeep.neukirch_uchida_of_classical ϕ he h.hasse₁ h.hasse₂
    h.localCft₁ h.localCft₂ h.localStructure₁ h.localStructure₂ 2 (h.residuals 2) h.chebotarev

/-- **The challenge theorem's statement, verbatim.** -/
theorem challenge_of_deepChapters (h : ClassicalChaptersDeep K₁ K₂ K₁' K₂')
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    : ∃! σ : K₂' ≃+* K₁',
      (algebraMap K₂ K₂').range.map σ.toRingHom = (algebraMap K₁ K₁').range ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) := by
  simpa only [Submission.NeukirchUchida.MapsBase] using
    neukirch_uchida_of_deepChapters h ϕ he

end Endgame

end NK.Mine
