import Submission.NK.Mine.NeukirchUchidaOfResiduals
import Submission.NK.ResidueFrob.LocalStructureInputs

/-!
# The complete classical-input wall of Neukirch–Uchida

This module collects **every** remaining classical input of the Neukirch–Uchida development into a
single structure `NK.Mine.ClassicalChapters`, and proves the challenge theorem
(CoNF XII Thm 12.2.1, the `∃!` form) from it:

```lean
NK.Mine.neukirch_uchida_of_classicalChapters (h : ClassicalChapters K₁ K₂ K₁' K₂') ϕ he
  : ∃! σ : K₂' ≃+* K₁', MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
      ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm)
```

The structure has exactly **seven** fields, each one of the five classical chapters of ROADMAP.md
§12, at the *two* fields `K₁` and `K₂`:

| field | classical content |
|---|---|
| `hasse₁`, `hasse₂` | block (i): per finite prime of `K₁` resp. `K₂`, the μ_p-twisted Hasse catalogue `NK.HasseTwist.Sha2Input` (Hasse norm theorem + labelled level-wise Hasse–Brauer–Noether + exhaustion of the localisation kernel, global class field theory), Neukirch's rank data `NK.Indecomposed.RankData` (the μ_p-twisted local Brauer `Br(κ)[p] ≅ ℤ/p` and Neukirch's surjectivity NSW (9.2.1)) and Neukirch's local *Kennzeichnung* `NK.Indecomposed.LocalReconstruction` (Korollar 1 + the maximality of decomposition groups) |
| `localCft₁`, `localCft₂` | block (ii): per finite prime, the tower ranks `NK.LocalStructure.TowerRankCore` and local class field theory `Nonempty (NK.LocalCFT.ArtinReciprocity κ κ̄)` |
| `localStructure₁`, `localStructure₂` | input (iii): per finite place, the tame structure of `G_κ` (`NK.ResidueFrob.LocalStructureData`) |
| `residuals` | input (iv): Shimizu's rank theory, as the single structure `NK.ShimizuRank.Residuals` at every prime `ℓ` |
| `chebotarev` | input (v): Čebotarev's density theorem (`NK.Reconstruct.ChebotarevInput ℚ K₁'`) |

**Reading of the structure.** The five chapters are *not* independent: the areas of this workspace
are proving them, and the sharpest reductions currently on disk replace several fields by single
named classical theorems.  The point of this module is to give **one name** to the whole remaining
wall, so that (a) the endgame is a single call once the chapters land, and (b) an audit of "what is
left" is a `#print` of the seven fields.

## Satisfiability

Each field is a classical theorem of the literature; the *formal* statements have been audited for
satisfiability at concrete instances in the areas that own them (see `ROADMAP.md` §2, §10, §12 and
the READMEs of `Submission/Work/{HasseTwist,Indecomposed,LocalStructure,TameData,ShimizuRank}`).
In particular: the Hasse catalogue is stated in the *labelled* form (the unlabelled form is false),
the rank data are stated with `μ_p`-coefficients (the trivial-coefficient form is false for odd
`p`), and the local reconstruction carries no hypothesis on `κ₀ = ⊤` (which would make it false).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open IsDedekindDomain.HeightOneSpectrum

universe u

namespace NK.Mine

/-- **The complete classical-input wall of Neukirch–Uchida.**

Its seven constituents are the five classical chapters of the proof, evaluated at the two fields
`K₁` and `K₂`: the Hasse catalogue with Neukirch's rank data and local reconstruction (block (i)),
local class field theory with the tower ranks (block (ii)), the local structure of `G_κ` (input
(iii)), Shimizu's rank theory (input (iv)) and Čebotarev (input (v)).  See the module docstring for
the reading of the fields and for the references. -/
structure ClassicalChapters (K₁ K₂ K₁' K₂' : Type u) [Field K₁] [Field K₂] [Field K₁']
    [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] : Prop where
  /-- **block (i) at the primes of `K₁`**: the μ_p-twisted Hasse catalogue, Neukirch's rank data
  and Neukirch's local reconstruction, at the completion `K₁_𝔭` and the global field `K₂`. -/
  hasse₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
    ∃ p : ℕ,
      NK.HasseTwist.Sha2Input p K₂ K₂' (𝔭.adicCompletion K₁)
        (SeparableClosure (𝔭.adicCompletion K₁)) ∧
      NK.Indecomposed.RankData p K₂ K₂' (𝔭.adicCompletion K₁)
        (SeparableClosure (𝔭.adicCompletion K₁)) ∧
      NK.Indecomposed.LocalReconstruction p K₂ K₂' (𝔭.adicCompletion K₁)
        (SeparableClosure (𝔭.adicCompletion K₁))
  /-- **block (i) at the primes of `K₂`** (the same catalogue in the other direction). -/
  hasse₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
    ∃ p : ℕ,
      NK.HasseTwist.Sha2Input p K₁ K₁' (𝔮.adicCompletion K₂)
        (SeparableClosure (𝔮.adicCompletion K₂)) ∧
      NK.Indecomposed.RankData p K₁ K₁' (𝔮.adicCompletion K₂)
        (SeparableClosure (𝔮.adicCompletion K₂)) ∧
      NK.Indecomposed.LocalReconstruction p K₁ K₁' (𝔮.adicCompletion K₂)
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
  /-- **input (iii) at the places of `K₁`**: the tame structure of `G_κ` at every finite place. -/
  localStructure₁ : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K₁ K₁',
    NK.ResidueFrob.LocalStructureData K₁ K₁' A
  /-- **input (iii) at the places of `K₂`**. -/
  localStructure₂ : ∀ B : NK.FrobeniusBridge.FinitePlaceOf K₂ K₂',
    NK.ResidueFrob.LocalStructureData K₂ K₂' B
  /-- **input (iv)**: Shimizu's rank theory, as the single structure `NK.ShimizuRank.Residuals`,
  at *every* prime `ℓ`. -/
  residuals : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ResidualsDerived K₁ K₁' ℓ
  /-- **input (v)**: Čebotarev's density theorem for the absolute Galois group of `K₁`. -/
  chebotarev : NK.ReconstructEndgame.ChebotarevInputDerived K₁ K₁'

section Endgame

variable {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **Neukirch–Uchida (CoNF XII Thm 12.2.1) from the complete classical-input wall.**

This is the single call that closes the challenge theorem once the five classical chapters of
`ROADMAP.md` §12 have been proved: the existence half is the Shimizu endgame
(`NK.Mine.neukirch_uchida_of_localStructureData_residuals`), the uniqueness half is the *proved*
`Submission.NeukirchUchida.unique_sigma` (inside the endgame). -/
theorem neukirch_uchida_of_classicalChapters (h : ClassicalChapters K₁ K₂ K₁' K₂')
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    : ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) := by
  classical
  exact neukirch_uchida_of_localStructureData_residuals ϕ he h.hasse₁ h.hasse₂
    h.localCft₁ h.localCft₂ h.localStructure₁ h.localStructure₂ 2
    (h.residuals 2) h.chebotarev

/-- **The challenge theorem `Submission.neukirch_uchida`, verbatim, from the classical-input
wall.**

This is the *exact* statement of `Challenge.lean` (the `MapsBase` condition unfolded to
`(algebraMap K₂ K₂').range.map σ.toRingHom = (algebraMap K₁ K₁').range`), so it records the last
line of the development: once the fields of `ClassicalChapters` are instantiated by proved
theorems, `Submission.neukirch_uchida` is `simpa [Submission.NeukirchUchida.MapsBase]` away. -/
theorem challenge_of_classicalChapters (h : ClassicalChapters K₁ K₂ K₁' K₂')
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    : ∃! σ : K₂' ≃+* K₁',
      (algebraMap K₂ K₂').range.map σ.toRingHom = (algebraMap K₁ K₁').range ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) := by
  simpa only [Submission.NeukirchUchida.MapsBase] using
    neukirch_uchida_of_classicalChapters h ϕ he

end Endgame

end NK.Mine
