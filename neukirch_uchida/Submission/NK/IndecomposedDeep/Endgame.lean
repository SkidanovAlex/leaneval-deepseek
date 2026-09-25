/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The endgame: `preservesDecompositionGroups_of_classical`, and the per-prime form

This module composes the two structures of `Submission/Work/Indecomposed/` — instantiated in
`RankData.lean` and `Reconstruction.lean` — into

* the endgame input (a) `Submission.NeukirchUchida.PreservesDecompositionGroups ϕ` of the
  Neukirch–Uchida development (the replacement of the sibling's
  `NK.Indecomposed.preservesDecompositionGroups_of_hasseAt` with the classical input catalogue of
  this chapter);

  `NK.IndecomposedDeep.preservesDecompositionGroups_of_classical`

* the per-prime *residual* form

  `∀ 𝔭, ∃ p, NK.HasseTwist.Sha2Input p · ∧ NK.Indecomposed.RankData p · ∧
  NK.Indecomposed.LocalReconstruction p ·`

  (`NK.IndecomposedDeep.perPrime_residuals`) consumed verbatim by
  `NK.Mine.neukirch_uchida_of_localStructureData_residuals`
  (`Submission/Work/Mine/NeukirchUchidaOfResiduals.lean`), together with the *composition* of the
  two,

  `NK.IndecomposedDeep.neukirch_uchida_of_classical`,

  which is the `∃!` form of CoNF XII Thm 12.2.1 with block (i) supplied by this chapter and the
  remaining blocks named as in the workspace endgame.

## The catalogue at a pair of local fields

`NK.IndecomposedDeep.DeepInputs p K K' κ κ'` bundles the classical input catalogue of `Defs.lean`
at one pair: the number field `K` with separable closure `K'` on the "target" side of the
homeomorphism, and the `p`-adic field `κ` with separable closure `κ'` (the completion of the other
number field at the prime being processed).  The two structures are *proved* from it
(`rankData_of_deepInputs`, `localReconstruction_of_deepInputs`), and hence so is
`PreservesDecompositionGroups ϕ`.
-/

import Submission.NK.IndecomposedDeep.RankData
import Submission.NK.IndecomposedDeep.Reconstruction
import Submission.NK.Indecomposed.Preserves
import Submission.NK.Mine.NeukirchUchidaOfResiduals

open IsDedekindDomain.HeightOneSpectrum

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

namespace NK.IndecomposedDeep

open NK.BrauerTwist NK.HasseTwist

variable {p : ℕ} {K K' κ κ' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K']
  [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-! ## The bundled catalogue -/

/-- **The classical input catalogue of block (i) at one pair `(K, K')`, `(κ, κ')`.**

This bundles, for a number field `K` with separable closure `K'` (the "target" side of the
homeomorphism `ϕ`) and a `p`-adic field `κ = K₁_𝔭` with separable closure `κ'` (the completion of
the other number field at the prime being processed):

| field | classical content | reference |
|---|---|---|
| `brauer` | `H²(G_κ, μ_p) ≅ ℤ/p` | Kummer sequence + `Br(κ)[p] ≅ ℤ/p` (NSW (7.1.7), (7.2.6)); reduced on disk in `Submission/Work/LocalCFT/Brauer/` |
| `transport` | the labelling transport: a closed `U ≤ G_K` with `U ≅ G_κ` has `H²(U, μ_p) ≅ H²(G_κ, μ_p)` | NSW (7.1.7)–(7.1.8) at the labelled subgroups, plus the cyclotomic compatibility of the labelling; **not formalised in the workspace** — see `README.md` §3 |
| `localGroup` | `p ≤ |H²(H ⊓ D_A, μ_p)|` at the non-trivial local groups | NSW (7.1.8)(i),(ii) |
| `surj` | Neukirch's modified surjectivity of the localisation at a prime | NSW (9.2.1); global class field theory.  On disk: `NK.HasseTwist.NeukirchH2modifiedsurj` (unconditional form) |
| `closed` | a subgroup isomorphic to a `p`-adic absolute Galois group is closed | Serre; see `README.md` §5 |
| `finiteness` | Neukirch's Korollar 1, finiteness form | Ivanov, `lm:locfinindex`; on disk: `NK.LocalDecomposition.LocalInjectionFiniteIndex` |
| `indexOne` | Neukirch's Theorem 1, maximality of decomposition groups | on disk: `NK.LocalDecomposition.IndexOneOfSelfNormalizing`; see the warning in `Reconstruction.lean` and `README.md` §6 |
-/
structure DeepInputs (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop where
  /-- the case of interest: `p` is a prime -/
  hp : p.Prime
  /-- the local Brauer computation at the local field: `H²(G_κ, μ_p) ≅ ℤ/p` -/
  brauer : NK.BrauerTwist.LocalFieldBrauerCyclic (κ := κ) (κ' := κ') p
  /-- the labelling transport for the twisted cohomology -/
  transport : GlobalBrauerTransport p K K' κ κ'
  /-- the local Brauer computation at the non-trivial local groups -/
  localGroup : LocalGroupBrauer p K K' κ κ'
  /-- Neukirch's modified surjectivity (NSW (9.2.1)) -/
  surj : NeukirchH2modifiedsurj p K K' κ κ'
  /-- closedness of subgroups isomorphic to a `p`-adic absolute Galois group -/
  closed : LocalSubgroupClosed.{u} κ κ'
  /-- Neukirch's Korollar 1, finiteness form (Ivanov's `lm:locfinindex`) -/
  finiteness : NK.LocalDecomposition.LocalInjectionFiniteIndex.{u} κ κ'
  /-- Neukirch's Theorem 1: the maximality of decomposition groups -/
  indexOne : NK.LocalDecomposition.IndexOneOfSelfNormalizing p K K' κ κ'

/-- **The rank data of Neukirch's argument from the bundled catalogue.** -/
theorem rankData_of_deepInputs (h : DeepInputs p K K' κ κ') :
    NK.Indecomposed.RankData p K K' κ κ' :=
  rankData_of_inputs (K := K) (K' := K') (κ := κ) (κ' := κ') h.hp h.brauer h.transport
    h.localGroup h.surj

/-- **Neukirch's local reconstruction from the bundled catalogue.** -/
theorem localReconstruction_of_deepInputs (h : DeepInputs p K K' κ κ') :
    NK.Indecomposed.LocalReconstruction p K K' κ κ' :=
  localReconstruction_of_inputs (K := K) (K' := K') (κ := κ) (κ' := κ') h.closed h.finiteness
    h.indexOne

/-! ## The per-prime local data, and the endgame input (a) -/

/-- **The per-prime twisted local data at a finite prime, from the catalogue and the Hasse input.**

This is `NK.Indecomposed.exists_localData_of_rankData` with the rank data and the local
reconstruction *proved* from the catalogue: at a finite prime `𝔭` of `K₁` (whose completion is `κ`),
the Hasse input `Sha2Input` together with the catalogue at that prime produce the triple
(`LocalH2Input`, `Sha2Vanishing`, `LocalDecompositionCriterion`) consumed by
`NK.BrauerTwist.preservesDecompositionGroups_of_localGalois`. -/
theorem exists_localData_of_deepInputs {K₁ K₂ K₂' : Type u} [Field K₁] [NumberField K₁]
    [Field K₂] [NumberField K₂] [Field K₂'] [Algebra K₂ K₂'] [IsSepClosure K₂ K₂']
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)) (p : ℕ)
    (hHasse : Sha2Input p K₂ K₂' (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)))
    (h : DeepInputs p K₂ K₂' (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁))) :
    ∃ q : ℕ, q.Prime ∧
      NK.BrauerTwist.LocalH2Input q K₂ K₂'
        (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)) ∧
      NK.BrauerTwist.Sha2Vanishing q K₂ K₂'
        (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)) ∧
      NK.BrauerTwist.LocalDecompositionCriterion q K₂ K₂'
        (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)) :=
  NK.Indecomposed.exists_localData_of_rankData (K₁ := K₁) (K₂ := K₂) (K₂' := K₂') 𝔭 p hHasse
    (rankData_of_deepInputs h) (localReconstruction_of_deepInputs h)

/-- **The endgame input (a) from the classical catalogue.**

Let `K₁, K₂` be number fields with separable closures `K₁', K₂'` and `ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)`
a homeomorphism.  Suppose that

* at every finite prime `𝔭` of `K₁` there are a prime `p`, the Hasse input
  `NK.HasseTwist.Sha2Input p K₂ K₂' (K₁_𝔭) (K₁_𝔭')` and the catalogue `DeepInputs p K₂ K₂' (K₁_𝔭) ·`,
* and symmetrically at every finite prime `𝔮` of `K₂`.

Then `ϕ` preserves the decomposition groups of the finite places:
`Submission.NeukirchUchida.PreservesDecompositionGroups ϕ` — the input (a) of
`Submission/NeukirchUchida/Endgame.lean`.

This is `NK.Indecomposed.preservesDecompositionGroups_of_hasseAt` with its rank data and local
reconstruction *proved* from the classical catalogue, i.e. the linchpin block (i) in the form in
which the endgame consumes it. -/
theorem preservesDecompositionGroups_of_classical
    {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (h₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ,
        NK.HasseTwist.Sha2Input p K₂ K₂'
          (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        DeepInputs p K₂ K₂'
          (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)))
    (h₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ p : ℕ,
        NK.HasseTwist.Sha2Input p K₁ K₁'
          (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        DeepInputs p K₁ K₁'
          (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂))) :
    Submission.NeukirchUchida.PreservesDecompositionGroups ϕ :=
  NK.Indecomposed.preservesDecompositionGroups_of_hasseAt (K₁ := K₁) (K₂ := K₂) (K₁' := K₁')
    (K₂' := K₂') ϕ he
    (fun 𝔭 => by
      obtain ⟨p, hHasse, h⟩ := h₁ 𝔭
      exact ⟨p, hHasse, rankData_of_deepInputs h, localReconstruction_of_deepInputs h⟩)
    (fun 𝔮 => by
      obtain ⟨p, hHasse, h⟩ := h₂ 𝔮
      exact ⟨p, hHasse, rankData_of_deepInputs h, localReconstruction_of_deepInputs h⟩)

/-- **Neukirch's criterion from the catalogue and the Hasse input.**

At a pair `(K, K')`, `(κ, κ')`, the catalogue together with the Hasse input
`NK.HasseTwist.Sha2Input` produces Neukirch's criterion
`NK.BrauerTwist.LocalDecompositionCriterion p K K' κ κ'` in the `μ_p`-twisted form.  This is
`NK.Indecomposed.localDecompositionCriterion_of_twistedHasse` with its rank data and its local
reconstruction *proved* from the catalogue — i.e. the criterion (CoNF (12.1.9) "if") with only the
Hasse principle left as a hypothesis. -/
theorem localDecompositionCriterion_of_deepInputs
    (hH : Sha2Input p K K' κ κ') (h : DeepInputs p K K' κ κ') :
    NK.BrauerTwist.LocalDecompositionCriterion p K K' κ κ' :=
  NK.Indecomposed.localDecompositionCriterion_of_twistedHasse (K := K) (K' := K') (κ := κ)
    (κ' := κ') hH (neukirchH2modifiedsurjAt_of_input h.surj)
    (fun U hU hκ => (rankData_of_deepInputs h).card_global U hU hκ)
    (fun H hHcl hκ 𝔭 V hV hne => (rankData_of_deepInputs h).card_local H hHcl hκ 𝔭 V hV hne)
    (localReconstruction_of_deepInputs h)

/-! ## The per-prime residual form consumed by the endgame -/

/-- **The per-prime residual form**: at every finite prime of `K₁` there are a prime `p`, the Hasse
input `Sha2Input` and the two structures `RankData`, `LocalReconstruction` — with the structures
*proved* from the catalogue `DeepInputs`.

This is exactly the shape of the hypothesis `hB₁` of
`NK.Mine.neukirch_uchida_of_localStructureData_residuals`
(`Submission/Work/Mine/NeukirchUchidaOfResiduals.lean`), so the endgame consumes it verbatim. -/
theorem perPrime_residuals
    {K₁ K₂ K₂' : Type u} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂] [Field K₂']
    [Algebra K₂ K₂'] [IsSepClosure K₂ K₂']
    (h : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ,
        NK.HasseTwist.Sha2Input p K₂ K₂'
          (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        DeepInputs p K₂ K₂'
          (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁))) :
    ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ,
        NK.HasseTwist.Sha2Input p K₂ K₂'
          (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        NK.Indecomposed.RankData p K₂ K₂'
          (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        NK.Indecomposed.LocalReconstruction p K₂ K₂'
          (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)) := by
  intro 𝔭
  obtain ⟨p, hHasse, hdeep⟩ := h 𝔭
  exact ⟨p, hHasse, rankData_of_deepInputs hdeep, localReconstruction_of_deepInputs hdeep⟩

/-! ## The composed capstone -/

/-- **The `∃!` form of Neukirch–Uchida (CoNF XII Thm 12.2.1), with block (i) supplied by this
chapter.**

This is `NK.Mine.neukirch_uchida_of_localStructureData_residuals` with its block (i)
(`hB₁`, `hB₂`) *derived* from the catalogue: the remaining hypotheses are block (ii) (`k₁`, `k₂`: the
tower ranks and local class field theory), the local structure data at every finite place (`h₁`,
`h₂`), the rank residual `NK.ShimizuRank.Residuals` at a prime `ℓ` and Čebotarev. -/
theorem neukirch_uchida_of_classical
    {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (hB₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ,
        NK.HasseTwist.Sha2Input p K₂ K₂'
          (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        DeepInputs p K₂ K₂'
          (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)))
    (hB₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ p : ℕ,
        NK.HasseTwist.Sha2Input p K₁ K₁'
          (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        DeepInputs p K₁ K₁'
          (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)))
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
    (hres : NK.Mine.ResidualsDerived K₁ K₁' ℓ)
    (hc : NK.ReconstructEndgame.ChebotarevInputDerived K₁ K₁') :
    ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) :=
  NK.Mine.neukirch_uchida_of_localStructureData_residuals (K₁ := K₁) (K₂ := K₂) (K₁' := K₁')
    (K₂' := K₂') ϕ he (perPrime_residuals (K₁ := K₁) (K₂ := K₂) (K₂' := K₂') hB₁)
    (perPrime_residuals (K₁ := K₂) (K₂ := K₁) (K₂' := K₁') hB₂) k₁ k₂ h₁ h₂ ℓ hres hc

end NK.IndecomposedDeep
