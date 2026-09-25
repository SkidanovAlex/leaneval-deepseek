import Submission.NK.EndgameRepair.Endgame
import Submission.NK.IndecomposedDeep.All

/-!
# The repaired classical-input wall and its `∃!` capstone

`Submission/Work/Mine/ClassicalChapters.lean` and
`Submission/Work/Mine/ClassicalChaptersDeep.lean` name the whole remaining wall of the
Neukirch–Uchida development in a single structure, and prove the challenge theorem from it.  Their
rank field, however, is the **refuted** rank structure of the Shimizu route (unsatisfiable at every
prime `ℓ`; see `README.md` and `NK.RankTheoryDeep.not_residualsDerived`), so those walls have no
instances and their capstones are vacuous.

This module re-states the wall with the rank field replaced by the **satisfiable** corrected
residual `NK.RankTheoryDeep.CorrectedResidualsDerived K₁ K₁' ℓ`, and re-proves the capstone.

## Contents

* `NK.EndgameRepair.ClassicalChaptersRepaired` — the wall of
  `NK.Mine.ClassicalChaptersDeep` (block (i) in the `Sha2Input` × `DeepInputs` form, block (ii),
  the local structure data at every finite place, the rank chapter, Čebotarev), with the rank field
  `∀ (ℓ : ℕ) [Fact ℓ.Prime], NK.RankTheoryDeep.CorrectedResidualsDerived K₁ K₁' ℓ`.
* `NK.EndgameRepair.ClassicalChaptersRepairedBasic` — the same with block (i) in the raw
  `Sha2Input × RankData × LocalReconstruction` form (the shape of
  `NK.Mine.ClassicalChapters`), so that a caller who has not gone through
  `Submission/Work/IndecomposedDeep/` can use it too.
* `NK.EndgameRepair.neukirch_uchida_of_repairedChapters` and
  `NK.EndgameRepair.neukirch_uchida_of_repairedChaptersBasic` — the `∃!` form of CoNF XII
  Thm 12.2.1 from the walls (the existence half from
  `NK.EndgameRepair.neukirch_uchida_of_localStructureData_correctedResiduals`, uniqueness from the
  *proved* `Submission.NeukirchUchida.unique_sigma`).
* `NK.EndgameRepair.challenge_of_repairedChapters` (and `...Basic`) — the **verbatim**
  challenge statement (`Submission.neukirch_uchida`'s statement, with `MapsBase` unfolded to the
  range equality) from the walls.
* `NK.EndgameRepair.exists_sigma_of_repairedChapters` (and `...Basic`) — the existence halves.

The rank field of every structure and every theorem below is the corrected residual; the refuted
rank hypotheses of the on-disk route occur nowhere in this module.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace NK.EndgameRepair

universe u

/-- **The repaired classical-input wall of Neukirch–Uchida**, in the `DeepInputs`-reduced form of
`NK.Mine.ClassicalChaptersDeep`.

Eight fields, each one of the five classical chapters of `ROADMAP.md` §12 evaluated at the two
fields:

| field | classical content |
|---|---|
| `hasse₁`, `hasse₂` | block (i): the μ_p-twisted Hasse catalogue and the classical catalogue `NK.IndecomposedDeep.DeepInputs` (local class field theory, the two labelling inputs, the local-group Brauer computation, Neukirch's surjectivity NSW (9.2.1), Ivanov's `lm:locfinindex` and Neukirch's Theorem 1) |
| `localCft₁`, `localCft₂` | block (ii): the tower ranks and local class field theory |
| `localStructure₁`, `localStructure₂` | input (iii): the tame structure of `G_κ` at every finite place |
| `residuals` | input (iv): **Shimizu's rank theory, as the corrected residual** — CoNF (10.3.7)/(10.3.20) for the Hausdorff quotient `Γ_K ⧸ invisible`, ℓ-adic Artin reciprocity, the local unit theorem, and Shimizu's kernel-rank input |
| `chebotarev` | input (v): Čebotarev's density theorem |

The single difference from `NK.Mine.ClassicalChaptersDeep` is the type of `residuals`: the
corrected residual replaces the refuted one. -/
structure ClassicalChaptersRepaired (K₁ K₂ K₁' K₂' : Type u) [Field K₁] [Field K₂] [Field K₁']
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
  /-- **input (iv)**: the **corrected** rank theory of the Shimizu route, at every prime `ℓ`. -/
  residuals : ∀ (ℓ : ℕ) [Fact ℓ.Prime], NK.RankTheoryDeep.CorrectedResidualsDerived K₁ K₁' ℓ
  /-- **input (v)**: Čebotarev's density theorem. -/
  chebotarev : NK.ReconstructEndgame.ChebotarevInputDerived K₁ K₁'

/-- **The repaired classical-input wall of Neukirch–Uchida**, in the raw per-prime form of
`NK.Mine.ClassicalChapters` (block (i) *not* reduced through the `DeepInputs` catalogue), with the
same corrected rank field. -/
structure ClassicalChaptersRepairedBasic (K₁ K₂ K₁' K₂' : Type u) [Field K₁] [Field K₂]
    [Field K₁'] [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] : Prop where
  /-- **block (i) at the primes of `K₁`**. -/
  hasse₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
    ∃ p : ℕ,
      NK.HasseTwist.Sha2Input p K₂ K₂' (𝔭.adicCompletion K₁)
        (SeparableClosure (𝔭.adicCompletion K₁)) ∧
      NK.Indecomposed.RankData p K₂ K₂' (𝔭.adicCompletion K₁)
        (SeparableClosure (𝔭.adicCompletion K₁)) ∧
      NK.Indecomposed.LocalReconstruction p K₂ K₂' (𝔭.adicCompletion K₁)
        (SeparableClosure (𝔭.adicCompletion K₁))
  /-- **block (i) at the primes of `K₂`**. -/
  hasse₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
    ∃ p : ℕ,
      NK.HasseTwist.Sha2Input p K₁ K₁' (𝔮.adicCompletion K₂)
        (SeparableClosure (𝔮.adicCompletion K₂)) ∧
      NK.Indecomposed.RankData p K₁ K₁' (𝔮.adicCompletion K₂)
        (SeparableClosure (𝔮.adicCompletion K₂)) ∧
      NK.Indecomposed.LocalReconstruction p K₁ K₁' (𝔮.adicCompletion K₂)
        (SeparableClosure (𝔮.adicCompletion K₂))
  /-- **block (ii) at the primes of `K₁`**. -/
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
  /-- **input (iii) at the places of `K₁`**. -/
  localStructure₁ : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K₁ K₁',
    NK.ResidueFrob.LocalStructureData K₁ K₁' A
  /-- **input (iii) at the places of `K₂`**. -/
  localStructure₂ : ∀ B : NK.FrobeniusBridge.FinitePlaceOf K₂ K₂',
    NK.ResidueFrob.LocalStructureData K₂ K₂' B
  /-- **input (iv)**: the corrected rank theory, at every prime `ℓ`. -/
  residuals : ∀ (ℓ : ℕ) [Fact ℓ.Prime], NK.RankTheoryDeep.CorrectedResidualsDerived K₁ K₁' ℓ
  /-- **input (v)**: Čebotarev's density theorem. -/
  chebotarev : NK.ReconstructEndgame.ChebotarevInputDerived K₁ K₁'

section Endgame

variable {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **Neukirch–Uchida (CoNF XII Thm 12.2.1), the `∃!` capstone, from the repaired wall.**

The rank chapter enters only through `h.residuals 2`: the structure supplies the corrected residual
at *every* prime, and the endgame needs one. -/
theorem neukirch_uchida_of_repairedChapters (h : ClassicalChaptersRepaired K₁ K₂ K₁' K₂')
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    : ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) :=
  neukirch_uchida_of_localStructureData_correctedResiduals ϕ he
    (NK.IndecomposedDeep.perPrime_residuals (K₁ := K₁) (K₂ := K₂) (K₂' := K₂') h.hasse₁)
    (NK.IndecomposedDeep.perPrime_residuals (K₁ := K₂) (K₂ := K₁) (K₂' := K₁') h.hasse₂)
    h.localCft₁ h.localCft₂ h.localStructure₁ h.localStructure₂ 2 (h.residuals 2) h.chebotarev

/-- The existence half of `neukirch_uchida_of_repairedChapters`. -/
theorem exists_sigma_of_repairedChapters (h : ClassicalChaptersRepaired K₁ K₂ K₁' K₂')
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    : ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ := by
  obtain ⟨σ, hσ, _⟩ := neukirch_uchida_of_repairedChapters h ϕ he
  exact ⟨σ, hσ⟩

/-- **`Submission.neukirch_uchida`, verbatim, from the repaired wall.**

This is the *exact* statement of `Challenge.lean` (with `Submission.NeukirchUchida.MapsBase`
unfolded to the range equality `(algebraMap K₂ K₂').range.map σ.toRingHom = (algebraMap K₁ K₁').range`),
so it is the last line of the development modulo the wall. -/
theorem challenge_of_repairedChapters (h : ClassicalChaptersRepaired K₁ K₂ K₁' K₂')
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    : ∃! σ : K₂' ≃+* K₁',
      (algebraMap K₂ K₂').range.map σ.toRingHom = (algebraMap K₁ K₁').range ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) := by
  simpa only [Submission.NeukirchUchida.MapsBase] using
    neukirch_uchida_of_repairedChapters h ϕ he

/-- **Neukirch–Uchida (CoNF XII Thm 12.2.1), the `∃!` capstone, from the repaired wall in the raw
per-prime form.** -/
theorem neukirch_uchida_of_repairedChaptersBasic (h : ClassicalChaptersRepairedBasic K₁ K₂ K₁' K₂')
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    : ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) :=
  neukirch_uchida_of_localStructureData_correctedResiduals ϕ he h.hasse₁ h.hasse₂
    h.localCft₁ h.localCft₂ h.localStructure₁ h.localStructure₂ 2 (h.residuals 2) h.chebotarev

/-- The existence half of `neukirch_uchida_of_repairedChaptersBasic`. -/
theorem exists_sigma_of_repairedChaptersBasic (h : ClassicalChaptersRepairedBasic K₁ K₂ K₁' K₂')
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    : ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ := by
  obtain ⟨σ, hσ, _⟩ := neukirch_uchida_of_repairedChaptersBasic h ϕ he
  exact ⟨σ, hσ⟩

/-- **`Submission.neukirch_uchida`, verbatim, from the repaired wall in the raw per-prime form.** -/
theorem challenge_of_repairedChaptersBasic (h : ClassicalChaptersRepairedBasic K₁ K₂ K₁' K₂')
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    : ∃! σ : K₂' ≃+* K₁',
      (algebraMap K₂ K₂').range.map σ.toRingHom = (algebraMap K₁ K₁').range ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) := by
  simpa only [Submission.NeukirchUchida.MapsBase] using
    neukirch_uchida_of_repairedChaptersBasic h ϕ he

/-- **The repaired wall from the reduced one**: every instance of
`NK.Mine.ClassicalChaptersDeep` with its rank field replaced by the corrected residual, in the
`DeepInputs` form, is an instance of `ClassicalChaptersRepaired`.  (Recorded so that the *shape* of
the old wall can be reused field by field.) -/
theorem classicalChaptersRepaired_of_deepInputs
    (h₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ,
        NK.HasseTwist.Sha2Input p K₂ K₂' (𝔭.adicCompletion K₁)
          (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        NK.IndecomposedDeep.DeepInputs p K₂ K₂' (𝔭.adicCompletion K₁)
          (SeparableClosure (𝔭.adicCompletion K₁)))
    (h₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ p : ℕ,
        NK.HasseTwist.Sha2Input p K₁ K₁' (𝔮.adicCompletion K₂)
          (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        NK.IndecomposedDeep.DeepInputs p K₁ K₁' (𝔮.adicCompletion K₂)
          (SeparableClosure (𝔮.adicCompletion K₂)))
    (hl₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      NK.LocalStructure.TowerRankCore K₁ 𝔭 (SeparableClosure (𝔭.adicCompletion K₁))
        (ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K₁))) ∧
      Nonempty (NK.LocalCFT.ArtinReciprocity (𝔭.adicCompletion K₁)
        (SeparableClosure (𝔭.adicCompletion K₁))))
    (hl₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      NK.LocalStructure.TowerRankCore K₂ 𝔮 (SeparableClosure (𝔮.adicCompletion K₂))
        (ringChar (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K₂))) ∧
      Nonempty (NK.LocalCFT.ArtinReciprocity (𝔮.adicCompletion K₂)
        (SeparableClosure (𝔮.adicCompletion K₂))))
    (hs₁ : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K₁ K₁',
      NK.ResidueFrob.LocalStructureData K₁ K₁' A)
    (hs₂ : ∀ B : NK.FrobeniusBridge.FinitePlaceOf K₂ K₂',
      NK.ResidueFrob.LocalStructureData K₂ K₂' B)
    (hr : ∀ (ℓ : ℕ) [Fact ℓ.Prime], NK.RankTheoryDeep.CorrectedResidualsDerived K₁ K₁' ℓ)
    (hc : NK.ReconstructEndgame.ChebotarevInputDerived K₁ K₁') :
    ClassicalChaptersRepaired K₁ K₂ K₁' K₂' :=
  ⟨h₁, h₂, hl₁, hl₂, hs₁, hs₂, hr, hc⟩

end Endgame

end NK.EndgameRepair
