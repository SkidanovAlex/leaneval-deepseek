/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The reduction of Neukirch's criterion to its four inputs

This file contains the main theorem of the chapter:

```lean
NK.LocalDecomposition.localDecompositionCriterion
    (hInd : IndecomposedPrime p K K' κ κ') (hInf : LocalGaloisInfinite κ κ')
    (hIdx : IndexOneOfSelfNormalizing p K K' κ κ') :
    NK.BrauerHasse.LocalDecompositionCriterion p K K' κ κ'
```

i.e. Neukirch's characterisation of decomposition groups (the "if" direction of CoNF (12.1.9),
Theorem 1 of Neukirch, Invent. Math. **6** (1969)) from the three named classical inputs
`IndecomposedPrime`, `LocalGaloisInfinite` and `IndexOneOfSelfNormalizing` — see
`Submission/Work/LocalDecomposition/Defs.lean` for their statements and references.

The two halves of `NK.BrauerHasse.LocalDecompositionCriterion` are the ones isolated by
`Submission/Work/LocalStructure/Defs.lean`:

* `NK.LocalStructure.LocalBrauerLocalisation` — a non-zero local component of `x` at `A` forces
  `H ⊆ D_A` with finite index.  It is derived here from `IndecomposedPrime` (which produces an open
  subgroup `H₀ ≤ H` inside some decomposition group) and `LocalGaloisInfinite`, using
  `NK.LocalDecomposition.le_stabSubgroup_of_openSubgroup_le` (Ivanov's `lm:finindexlm`, proved in
  `Basic.lean`).
* `NK.LocalStructure.LocalFinishingStep` — a closed self-normalising `H ≤ D_A` isomorphic to the
  absolute Galois group of a `p`-adic field is *equal* to `D_A`.  It is derived here from
  `IndexOneOfSelfNormalizing`, and it is shown to be *equivalent* to it
  (`localFinishingStep_iff_indexOne`): the existence of a place `A'` with `D_{A'} = H` is not extra
  information, because two distinct places have trivially intersecting decomposition groups
  (`stabSubgroup_inf_eq_bot_of_ne`).
-/
import Submission.NK.LocalDecomposition.Basic
import Submission.NK.LocalStructure.Brauer.localDecompositionCriterion_of_brauer_and_finishing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

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

/-- **The local Brauer/localisation half from the indecomposed-prime input.**

If `IndecomposedPrime` produces, for a class with non-zero local component at `A`, an open
subgroup `H₀ ≤ H` inside the decomposition group of a place `A'` over a finite prime, and if `H` is
infinite (because `H ≅ Gal(κ'/κ)` and `Gal(κ'/κ)` is, `LocalGaloisInfinite`), then Ivanov's
`lm:finindexlm` (`le_stabSubgroup_of_openSubgroup_le`) upgrades this to `H ≤ D_{A'}`, and the
relative index is finite since it is bounded by `[D_{A'} : H₀]`. -/
theorem localBrauerLocalisation_of_inputs (hInd : IndecomposedPrime p K K' κ κ')
    (hFin : InjectionFiniteIndex p K K' κ κ') (hInf : LocalGaloisInfinite κ κ') :
    NK.LocalStructure.LocalBrauerLocalisation p K K' κ κ' := by
  refine ⟨fun H _hHclosed hκ A x hx => ?_⟩
  obtain ⟨H₀, A', hH₀le, hH₀fin, hA', hH₀le_stab⟩ := hInd H _hHclosed hκ A x hx
  -- Neukirch's Korollar 1: `H₀` is open in `D_{A'}` as well
  have hH₀fin_stab := hFin H H₀ A' hH₀le hH₀fin hκ hA' hH₀le_stab
  -- `H` is infinite because it is isomorphic to the absolute Galois group of the `p`-adic field `κ`
  obtain ⟨e⟩ := hκ
  haveI : Infinite (Gal(κ'/κ)) := hInf
  have hHinf : Nat.card ↥H = 0 := by
    rw [Nat.card_congr e.toEquiv]
    exact Nat.card_eq_zero_of_infinite
  -- Ivanov's `lm:finindexlm`: the open subgroup pulls `H` into the decomposition group
  have hHle : H ≤ MulAction.stabilizer Gal(K'/K) A' :=
    le_stabSubgroup_of_openSubgroup_le A' hA' H H₀ hH₀le hH₀fin hHinf hH₀le_stab
  -- the relative index is finite
  have hmul : H₀.relIndex H * H.relIndex (MulAction.stabilizer Gal(K'/K) A') =
      H₀.relIndex (MulAction.stabilizer Gal(K'/K) A') :=
    Subgroup.relIndex_mul_relIndex (H := H₀) (K := H)
      (L := MulAction.stabilizer Gal(K'/K) A') hH₀le hHle
  have hpos : 0 < H.relIndex (MulAction.stabilizer Gal(K'/K) A') := by
    rcases Nat.eq_zero_or_pos (H.relIndex (MulAction.stabilizer Gal(K'/K) A')) with h0 | h
    · rw [h0, mul_zero] at hmul
      exact absurd (hmul ▸ hH₀fin_stab) (lt_irrefl _)
    · exact h
  exact ⟨A', hA', hHle, hpos⟩

/-- **The strong form of the indecomposed-prime conclusion.**  The three inputs
`IndecomposedPrime`, `InjectionFiniteIndex` and `LocalGaloisInfinite` upgrade the *open subgroup*
`H₀ ⊆ D_{A'}` produced by the localisation argument to the containment `H ⊆ D_{A'}` of the whole
closed subgroup, with finite relative index.  This is the statement that Neukirch's argument in fact
produces (CoNF (12.1.9): "the prime is indecomposed"), and it is the form recorded in the
sub-project's `README` as the intended discharge of `IndecomposedPrime`.

The proof is Ivanov's `lm:finindexlm` (`le_stabSubgroup_of_openSubgroup_le`, proved in
`Basic.lean`), which needs only that `H` be infinite — supplied by `LocalGaloisInfinite` and the
isomorphism `H ≅ Gal(κ'/κ)`. -/
theorem le_stabSubgroup_of_indecomposedPrime (hInd : IndecomposedPrime p K K' κ κ')
    (hFin : InjectionFiniteIndex p K K' κ κ') (hInf : LocalGaloisInfinite κ κ') :
    ∀ (H : Subgroup Gal(K'/K)), IsClosed (H : Set Gal(K'/K)) →
      Nonempty (H ≃* Gal(κ'/κ)) →
      ∀ (A : OverFinitePrime K K') (x : H2Profinite p H), H2Profinite.loc p H x A ≠ 0 →
        ∃ A' : ValuationSubring K', A'.comap (algebraMap K K') ≠ ⊤ ∧
          H ≤ MulAction.stabilizer Gal(K'/K) A' := by
  intro H hHclosed hκ A x hx
  obtain ⟨H₀, A', hH₀le, hH₀fin, hA', hH₀le_stab⟩ := hInd H hHclosed hκ A x hx
  have hH₀fin_stab := hFin H H₀ A' hH₀le hH₀fin hκ hA' hH₀le_stab
  obtain ⟨e⟩ := hκ
  haveI : Infinite (Gal(κ'/κ)) := hInf
  have hHinf : Nat.card ↥H = 0 := by
    rw [Nat.card_congr e.toEquiv]
    exact Nat.card_eq_zero_of_infinite
  exact ⟨A', hA', le_stabSubgroup_of_openSubgroup_le A' hA' H H₀ hH₀le hH₀fin hHinf hH₀le_stab⟩

/-- **The finishing step from the index-one (maximality) input.**

If `H ≤ D_A` is closed, self-normalising, isomorphic to the absolute Galois group of a `p`-adic
field and of finite relative index in `D_A`, then `IndexOneOfSelfNormalizing` says `D_A = H`, so one
may take `A' = A`. -/
theorem localFinishingStep_of_indexOne (hIdx : IndexOneOfSelfNormalizing p K K' κ κ') :
    NK.LocalStructure.LocalFinishingStep p K K' κ κ' := by
  intro H hHclosed hN hκ A hA hHle hrel
  exact ⟨A, hA, hIdx H hHclosed hN hκ A hA hHle hrel⟩

/-- **The index-one (maximality) input from the finishing step.**

Conversely, if `LocalFinishingStep` holds, then for `H ≤ D_A` closed, self-normalising, isomorphic
to a local Galois group and of finite relative index, the finishing step produces a place `A'` with
`D_{A'} = H`; since `H ≤ D_A`, one has `D_{A'} ≤ D_A`, so `D_{A'}` is contained in
`D_A ⊓ D_{A'} = ⊥` whenever `A' ≠ A`, contradicting the non-triviality of a decomposition group.
Hence `A' = A` and `D_A = H`. -/
theorem indexOne_of_localFinishingStep (hFin : NK.LocalStructure.LocalFinishingStep p K K' κ κ') :
    IndexOneOfSelfNormalizing p K K' κ κ' := by
  intro H hHclosed hN hκ A hA hHle hrel
  obtain ⟨A', hA', hstab⟩ := hFin H hHclosed hN hκ A hA hHle hrel
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

/-- **The finishing step and the index-one statement are equivalent**: the existential over places
of `NK.LocalStructure.LocalFinishingStep` carries no extra information, because the decomposition
groups of distinct places have trivial intersection. -/
theorem localFinishingStep_iff_indexOne :
    NK.LocalStructure.LocalFinishingStep p K K' κ κ' ↔
      IndexOneOfSelfNormalizing p K K' κ κ' :=
  ⟨indexOne_of_localFinishingStep, localFinishingStep_of_indexOne⟩

/-- **A partial case of the index-one input `IndexOneOfSelfNormalizing`.**

If `H ≤ D_A` is *normal* in `D_A` and self-normalising in `Gal(K'/K)`, then `D_A ≤ N(H) = H`, so
`D_A = H`.  (The normality hypothesis holds when the finite extension of the local field `K_𝔭`
corresponding to `H` is Galois; the content of `IndexOneOfSelfNormalizing` is therefore exactly the
*non-Galois* case, where `H` is a non-normal finite-index subgroup of `D_A`.) -/
theorem stabSubgroup_eq_of_normal (A : ValuationSubring K') (H : Subgroup Gal(K'/K))
    (hHle : H ≤ MulAction.stabilizer Gal(K'/K) A)
    (hHnorm : (H.subgroupOf (MulAction.stabilizer Gal(K'/K) A)).Normal)
    (hN : Subgroup.normalizer H = H) :
    MulAction.stabilizer Gal(K'/K) A = H := by
  have hconj : ∀ x ∈ MulAction.stabilizer Gal(K'/K) A, ∀ h ∈ H, x * h * x⁻¹ ∈ H := by
    intro x hx h hh
    have hconjmem := hHnorm.conj_mem (⟨h, hHle hh⟩ : ↥(MulAction.stabilizer Gal(K'/K) A)) hh
      (⟨x, hx⟩ : ↥(MulAction.stabilizer Gal(K'/K) A))
    exact Subgroup.mem_subgroupOf.mp hconjmem
  refine le_antisymm (fun g hg => ?_) hHle
  rw [← hN, Subgroup.mem_normalizer_iff]
  intro h
  exact ⟨fun hh => hconj g hg h hh, fun hh => by
    have h1 : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ ∈ H := hconj g⁻¹ (inv_mem hg) (g * h * g⁻¹) hh
    have h2 : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rwa [h2] at h1⟩

/-- **Neukirch's criterion for decomposition groups** (Neukirch, Invent. Math. **6** (1969),
Theorem 1; CoNF (12.1.9) "if"): from the indecomposed-prime step, the infinitude of the local
Galois group and the maximality of decomposition groups, every closed self-normalising subgroup
`H ≤ Gal(K'/K)` isomorphic to the absolute Galois group of a `p`-adic field is the decomposition
group of a place of `K'` over a finite prime of `K`, as soon as some class in `H²(H, Z/p)` has a
non-zero local component. -/
theorem localDecompositionCriterion (hInd : IndecomposedPrime p K K' κ κ')
    (hFin : InjectionFiniteIndex p K K' κ κ') (hInf : LocalGaloisInfinite κ κ')
    (hIdx : IndexOneOfSelfNormalizing p K K' κ κ') :
    NK.BrauerHasse.LocalDecompositionCriterion p K K' κ κ' := by
  intro H hHclosed hN hκ A x hx
  obtain ⟨A₀, hA₀, hHle, hrel⟩ :=
    (localBrauerLocalisation_of_inputs hInd hFin hInf).exists_stabilizer H hHclosed hκ A x hx
  exact ⟨A₀, hA₀, hIdx H hHclosed hN hκ A₀ hA₀ hHle hrel⟩

/-- **The four inputs produce the two inputs of `Submission/Work/LocalStructure/`.**  This is the
form in which the reduction can be plugged into
`NK.LocalStructure.Brauer.localDecompositionCriterion_of_brauer_and_finishing` (and hence into
`NK.BrauerHasse.exists_decompositionGroup_of_localGalois`, resp.
`NK.Mine.preservesDecompositionGroups_of_localGalois`). -/
theorem localStructureInputs_of_inputs (hInd : IndecomposedPrime p K K' κ κ')
    (hFin : InjectionFiniteIndex p K K' κ κ') (hInf : LocalGaloisInfinite κ κ')
    (hIdx : IndexOneOfSelfNormalizing p K K' κ κ') :
    NK.LocalStructure.LocalBrauerLocalisation p K K' κ κ' ∧
      NK.LocalStructure.LocalFinishingStep p K K' κ κ' :=
  ⟨localBrauerLocalisation_of_inputs hInd hFin hInf, localFinishingStep_of_indexOne hIdx⟩


end

end NK.LocalDecomposition
