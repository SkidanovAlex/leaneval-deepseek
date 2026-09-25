/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The criterion, its tightness, the `p = 2` instance, and the use in the `(a)`-chain

This file collects the end-points of the chapter `Submission/Work/LocalDecomposition/`:

* `NK.LocalDecomposition.indexOne_of_localDecompositionCriterion` — **the reduction is tight**:
  conversely to `localDecompositionCriterion`, Neukirch's criterion (together with the local Brauer
  nonvanishing input `NK.BrauerHasse.LocalH2Input`, i.e. `Br(κ)[p] ≅ Z/p`) implies the
  index-one/maximality input `IndexOneOfSelfNormalizing`.  Hence, modulo the local Brauer input,
  `IndexOneOfSelfNormalizing` is *exactly* the content of the "if" direction of CoNF (12.1.9).

* `NK.LocalDecomposition.localDecompositionCriterion_two` — the criterion at the prime `p = 2`,
  where the trivial coefficient module `Z/2` agrees with the cyclotomic twist `μ_2` (see the
  module documentation of `Defs.lean`).

* `NK.LocalDecomposition.preservesDecompositionGroups_of_localData_two` — **the use**: at `p = 2`,
  the four inputs of the reduction, evaluated at the completion `𝔭.adicCompletion K₁` of every
  finite prime, together with the local Brauer input `LocalH2Input 2` and the Hasse principle
  `Sha2Vanishing 2`, yield `Submission.NeukirchUchida.PreservesDecompositionGroups ϕ` — the
  input `(a)` of the Neukirch–Uchida endgame.
-/
import Submission.NK.LocalDecomposition.Reduction
import Submission.NK.LocalDecomposition.Localisation
import Submission.NK.Mine.LocalGaloisInputsOfArtin

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false


open scoped Classical Pointwise
open IsDedekindDomain.HeightOneSpectrum

universe u

namespace NK.LocalDecomposition

noncomputable section

open NK.BrauerHasse

variable {p : ℕ} {K K' κ κ' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K']
  [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-- **The reduction is tight.**  Neukirch's criterion, together with the local Brauer nonvanishing
(`NK.BrauerHasse.LocalH2Input`, i.e. `H²(G_κ, Z/p) ≠ 0` for `H ≅ Gal(κ'/κ)`), implies the
index-one/maximality input: for `H ≤ D_A` closed, self-normalising, isomorphic to `Gal(κ'/κ)` and
of finite relative index, one has `D_A = H`.

Proof.  Choose `0 ≠ x ∈ H²(H, Z/p)`.  Since `H ≤ D_A` is an *inert* place, the localisation of `x`
at `A` is non-zero (`NK.HassePrinciple.loc_ne_zero_of_le_stabSubgroup`), so the criterion produces
`A'` with `D_{A'} = H`; as `H ≤ D_A`, this gives `D_{A'} ≤ D_A`, and since the decomposition groups
of distinct places intersect trivially (`stabSubgroup_inf_eq_bot_of_ne`) while a decomposition group
is non-trivial, necessarily `A' = A` and `D_A = H`. -/
theorem indexOne_of_localDecompositionCriterion
    (hC : NK.BrauerHasse.LocalDecompositionCriterion p K K' κ κ')
    (h2 : NK.BrauerHasse.LocalH2Input p K K' κ κ') :
    IndexOneOfSelfNormalizing p K K' κ κ' := by
  intro H hHclosed hN hκ A hA hHle hrel
  obtain ⟨x, hx⟩ := h2 H hHclosed hκ
  have hloc : H2Profinite.loc p H x ⟨A, hA⟩ ≠ 0 :=
    NK.HassePrinciple.loc_ne_zero_of_le_stabSubgroup p ⟨A, hA⟩ hHle hx
  obtain ⟨A', hA', hstab⟩ := hC H hHclosed hN hκ ⟨A, hA⟩ x hloc
  by_cases hAA' : A' = A
  · subst hAA'; exact hstab
  · exfalso
    have hbot : MulAction.stabilizer Gal(K'/K) A ⊓ MulAction.stabilizer Gal(K'/K) A' = ⊥ :=
      stabSubgroup_inf_eq_bot_of_ne (A := A) (A' := A') (Ne.symm hAA') hA hA'
    have h1 : MulAction.stabilizer Gal(K'/K) A' ≤ ⊥ := by
      rw [hstab, ← hbot]
      exact le_inf hHle (le_of_eq hstab.symm)
    obtain ⟨σ, hσne, hσA⟩ :=
      Commons.NumberTheory.NumberField.Valuation.exists_ne_one_comap_eq_of_comap_ne_top
        (K := K) (K' := K') A' hA'
    have hmem : σ ∈ MulAction.stabilizer Gal(K'/K) A' :=
      (Commons.NumberTheory.NumberField.Valuation.comap_eq_iff_mem_stabilizer
        (K := K) (K' := K') A' σ).mp hσA
    rw [le_bot_iff.mp h1] at hmem
    exact hσne (Subgroup.mem_bot.mp hmem)

/-- **The "only if" half of Neukirch's criterion** (CoNF (12.1.9) "only if"; CoNF (12.1.4)): the
decomposition group of a place over a finite prime is closed and self-normalising.  (The third
ingredient of the criterion's hypothesis, that `D_A` is isomorphic to the absolute Galois group of
the local field `K_𝔭`, is `NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois`.) -/
theorem stabSubgroup_isClosed_and_normalizer {K : Type u} [Field K] [NumberField K]
    {K' : Type u} [Field K'] [Algebra K K'] [IsSepClosure K K'] (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') ≠ ⊤) :
    IsClosed ((MulAction.stabilizer Gal(K'/K) A : Set Gal(K'/K))) ∧
      Subgroup.normalizer (MulAction.stabilizer Gal(K'/K) A) =
        MulAction.stabilizer Gal(K'/K) A :=
  ⟨isClosed_stabSubgroup A, normalizer_stabSubgroup_eq A hA⟩

/-- **The criterion at the prime `p = 2`.**  At `p = 2` the trivial coefficient module `Z/2` used by
the `NK.BrauerHasse` development agrees with the cyclotomic twist `μ_2` (`μ_2 = {±1} ⊆ κ` for
every field of characteristic `≠ 2`), so the four inputs of the reduction are the classical
statements with the correct coefficients (see `Submission/Work/LocalDecomposition/README.md`). -/
theorem localDecompositionCriterion_two
    (hInd : IndecomposedPrime 2 K K' κ κ') (hFin : InjectionFiniteIndex 2 K K' κ κ')
    (hInf : LocalGaloisInfinite κ κ') (hIdx : IndexOneOfSelfNormalizing 2 K K' κ κ') :
    NK.BrauerHasse.LocalDecompositionCriterion 2 K K' κ κ' :=
  localDecompositionCriterion hInd hFin hInf hIdx

variable {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
  [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂'] [IsSepClosure K₁ K₁']
  [IsSepClosure K₂ K₂']

/-- **The `(a)`-chain from the four inputs, at `p = 2`.**

For every finite prime `𝔭` of `K₁` (resp. `𝔮` of `K₂`), the local Brauer input
`NK.BrauerHasse.LocalH2Input 2`, the Hasse principle `NK.BrauerHasse.Sha2Vanishing 2` and the
four inputs of this chapter — `IndecomposedPrime`, `InjectionFiniteIndex`, `LocalGaloisInfinite`,
`IndexOneOfSelfNormalizing` — for the completion `𝔭.adicCompletion K₁` yield
`NK.BrauerHasse.LocalDecompositionCriterion 2`, hence
`Submission.NeukirchUchida.PreservesDecompositionGroups ϕ`: (a homeomorphic) isomorphism of absolute
Galois groups of number fields preserves the dependence structure of the decomposition subgroups. -/
theorem preservesDecompositionGroups_of_localData_two
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (hLoc₁ : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁),
      NK.BrauerHasse.LocalH2Input 2 K₂ K₂'
        (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)))
    (hHasse₁ : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁),
      NK.BrauerHasse.Sha2Vanishing 2 K₂ K₂'
        (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)))
    (hInd₁ : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁),
      IndecomposedPrime 2 K₂ K₂' (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)))
    (hFin₁ : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁),
      InjectionFiniteIndex 2 K₂ K₂' (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)))
    (hInf₁ : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁),
      LocalGaloisInfinite (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)))
    (hIdx₁ : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁),
      IndexOneOfSelfNormalizing 2 K₂ K₂'
        (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)))
    (hLoc₂ : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂),
      NK.BrauerHasse.LocalH2Input 2 K₁ K₁'
        (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)))
    (hHasse₂ : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂),
      NK.BrauerHasse.Sha2Vanishing 2 K₁ K₁'
        (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)))
    (hInd₂ : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂),
      IndecomposedPrime 2 K₁ K₁' (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)))
    (hFin₂ : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂),
      InjectionFiniteIndex 2 K₁ K₁' (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)))
    (hInf₂ : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂),
      LocalGaloisInfinite (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)))
    (hIdx₂ : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂),
      IndexOneOfSelfNormalizing 2 K₁ K₁'
        (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂))) :
    Submission.NeukirchUchida.PreservesDecompositionGroups ϕ :=
  NK.Mine.preservesDecompositionGroups_of_localData_two ϕ he
    (fun 𝔭 => ⟨hLoc₁ 𝔭, hHasse₁ 𝔭,
      localDecompositionCriterion (hInd₁ 𝔭) (hFin₁ 𝔭) (hInf₁ 𝔭) (hIdx₁ 𝔭)⟩)
    (fun 𝔮 => ⟨hLoc₂ 𝔮, hHasse₂ 𝔮,
      localDecompositionCriterion (hInd₂ 𝔮) (hFin₂ 𝔮) (hInf₂ 𝔮) (hIdx₂ 𝔮)⟩)

end

end NK.LocalDecomposition
