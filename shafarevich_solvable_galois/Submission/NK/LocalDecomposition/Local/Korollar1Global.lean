/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Korollar 1: from the local form to the finiteness of the index in a decomposition group

`NK.LocalDecomposition.InjectionFiniteIndex` (input (B) of the reduction) asserts that a subgroup
`H₀ ≤ D_A` of a decomposition group which is open in a closed subgroup `H ≅ Gal(κ'/κ)` has finite
relative index in `D_A`.  This file proves the *group-theoretic* core of that implication from the
local form

`NK.LocalDecomposition.LocalInjectionFiniteIndexSubgroup κ κ'`

of Neukirch's Korollar 1 (an arbitrary subgroup of the absolute Galois group of a `p`-adic field
isomorphic to `Gal(κ'/κ₀)` has finite index — no closedness needed).

The proof is the transport of the index along the local correspondence
`NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois`
(`D_A ≅ Gal(L'/L)` for `L = 𝔭.adicCompletion K`), which is valid for *arbitrary* subgroups and hence
does not need the correspondence to be a homeomorphism:

* `NK.LocalDecomposition.relIndex_pos_of_localInjection` — if `H₀ ≤ D_A` is isomorphic to
  `Gal(κ'/κ₀)`, then `0 < H₀.relIndex D_A`;
* `NK.LocalDecomposition.injectionFiniteIndex_of_localInjection` — consequently, the local form of
  Korollar 1 implies the global input `InjectionFiniteIndex` **for subgroups that come with their
  presentation** as `Gal(κ'/κ₀)`.

The remaining gap between the two — producing the presentation `H₀ ≅ Gal(κ'/κ₀)` for the open
subgroup `H₀` of `H ≅ Gal(κ'/κ)` — is discussed in `README.md` §5: it is a *formalisation* gap
(the disk local correspondence is an abstract `MulEquiv`, so that the image of `H₀` need not be
closed), not a mathematical one.
-/
import Submission.NK.LocalDecomposition.Reduction
import Submission.NK.LocalDecomposition.exists_intermediateField_of_finiteIndex_finrank
import Submission.NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical Pointwise
open IsDedekindDomain.HeightOneSpectrum

universe u

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace NK.LocalDecomposition

noncomputable section

open NK.BrauerHasse

variable {p : ℕ} {K K' κ κ' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K']
  [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-- **The index of a subgroup is invariant under an isomorphism of groups**: for `e : A ≃* B` and
`H ≤ A`, the index of `H` in `A` equals that of `H.map e` in `B`. -/
theorem relIndex_map_eq_of_mulEquiv {A B : Type u} [Group A] [Group B] (e : A ≃* B)
    (H : Subgroup A) :
    (H.map (e : A →* B)).relIndex ⊤ = H.relIndex ⊤ := by
  have h := Subgroup.relIndex_map_map_of_injective (f := (e : A →* B)) H ⊤ e.injective
  rwa [Subgroup.map_top_of_surjective _ e.surjective] at h

/-- **The finiteness of the index from the local form of Korollar 1.**

Let `A` be a place of `K'` over a finite prime of `K`, `H₀ ≤ D_A` a subgroup which is isomorphic to
the absolute Galois group `Gal(κ'/κ₀)` of a finite extension `κ₀` of the `p`-adic field `κ`.  Then
`H₀` has finite relative index in `D_A`.

The hypothesis is exactly what Neukirch's localisation argument produces for the open subgroup `H₀`
of the reduction; the isomorphism is transported to the local field of `A` by
`NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois`, and the index is computed
through it. -/
theorem relIndex_pos_of_localInjection (hD : LocalInjectionFiniteIndexSubgroup κ κ')
    (A : ValuationSubring K') (hA : A.comap (algebraMap K K') ≠ ⊤)
    (H₀ : Subgroup Gal(K'/K)) (hH₀le : H₀ ≤ MulAction.stabilizer Gal(K'/K) A)
    (κ₀ : IntermediateField κ κ') (h₀ : Nonempty (H₀ ≃* Gal(κ'/↥κ₀))) :
    0 < H₀.relIndex (MulAction.stabilizer Gal(K'/K) A) := by
  classical
  obtain ⟨𝔭, h𝔭⟩ := exists_heightOneSpectrum_eq_comap A hA
  obtain ⟨e⟩ :=
    NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois 𝔭 A h𝔭
  show 0 < H₀.relIndex (NK.Mine.decompositionGroupOf K K' A)
  have hD' : H₀ ≤ NK.Mine.decompositionGroupOf K K' A := hH₀le
  -- the image of `H₀` under the local correspondence
  have hmap : Nonempty
      (((H₀.subgroupOf (NK.Mine.decompositionGroupOf K K' A)).map
        (e : ↥(NK.Mine.decompositionGroupOf K K' A) →*
          Gal(SeparableClosure (𝔭.adicCompletion K)/𝔭.adicCompletion K))) ≃*
        Gal(κ'/↥κ₀)) := by
    obtain ⟨h₀e⟩ := h₀
    exact ⟨(Subgroup.equivMapOfInjective (H₀.subgroupOf (NK.Mine.decompositionGroupOf K K' A))
        (e : ↥(NK.Mine.decompositionGroupOf K K' A) →*
          Gal(SeparableClosure (𝔭.adicCompletion K)/𝔭.adicCompletion K)) e.injective).symm.trans
      ((Subgroup.subgroupOfEquivOfLe hD').trans h₀e)⟩
  have hloc := hD κ₀ K 𝔭 (SeparableClosure (𝔭.adicCompletion K)) _ hmap
  -- transport the finiteness back along the local correspondence
  have h1 : (H₀.subgroupOf (NK.Mine.decompositionGroupOf K K' A)).relIndex ⊤ =
      H₀.relIndex (NK.Mine.decompositionGroupOf K K' A) := by
    rw [← Subgroup.subgroupOf_self (NK.Mine.decompositionGroupOf K K' A)]
    exact Subgroup.relIndex_subgroupOf (H := H₀) (K := NK.Mine.decompositionGroupOf K K' A)
      (L := NK.Mine.decompositionGroupOf K K' A) le_rfl
  rw [← h1, ← relIndex_map_eq_of_mulEquiv e (H₀.subgroupOf (NK.Mine.decompositionGroupOf K K' A))]
  exact hloc

/-- **The global input `InjectionFiniteIndex`, from the local form of Korollar 1 and
Nikolov–Segal.**

The presentation `H₀ ≅ Gal(κ'/κ₀)` of the open subgroup, which was assumed in
`injectionFiniteIndex_of_localInjection`, is *derived* here: since `H₀` has finite index in
`H ≅ Gal(κ'/κ)`, its transporting image is a finite-index subgroup of the local absolute Galois group
`Gal(κ'/κ)`, hence closed by Nikolov–Segal (`hNS`, the input
`NK.LocalInputs.LocalGaloisInputsOfUnits.open_of_index_prime` /
`NK.LocalStructure.TowerRankCore.finiteIndex_isClosed`), hence by the Galois correspondence the
fixing subgroup of a finite extension `κ₀/κ` — this is
`NK.LocalDecomposition.exists_intermediateField_of_finiteIndex_finrank`.  Feeding that
presentation to `relIndex_pos_of_localInjection` gives the finiteness of the relative index in `D_A`.

The hypothesis `hNS` is Nikolov–Segal's theorem that a finite-index subgroup of the absolute Galois
group of a `p`-adic field is open (equivalently closed), a named classical input of the local
structure theory. -/
theorem injectionFiniteIndex_of_localInjection_unconditional
    (hD : LocalInjectionFiniteIndexSubgroup κ κ')
    (hNS : ∀ U : Subgroup Gal(κ'/κ), U.FiniteIndex → IsClosed (U : Set Gal(κ'/κ))) :
    InjectionFiniteIndex p K K' κ κ' := by
  intro H H₀ A hH₀le hH₀fin hκ hA hH₀le_stab
  obtain ⟨e⟩ := hκ
  obtain ⟨N, -, hpres⟩ := exists_intermediateField_of_finiteIndex_finrank (K := H) e H₀ hH₀le
    hH₀fin hNS
  exact relIndex_pos_of_localInjection hD A hA H₀ hH₀le_stab N hpres

/-- **The global input `InjectionFiniteIndex`, given the presentation of the open subgroup.**

This is the conditional form of `NK.LocalDecomposition.InjectionFiniteIndex` in which the open
subgroup `H₀ ≤ H` comes with the presentation `H₀ ≅ Gal(κ'/κ₀)` (equivalently: is the fixing
subgroup of a finite extension of `κ`).  It is derived here from the local form of Neukirch's
Korollar 1; the unconditional input `InjectionFiniteIndex` differs only by this presentation
hypothesis on the open subgroup. -/
theorem injectionFiniteIndex_of_localInjection
    (hD : LocalInjectionFiniteIndexSubgroup κ κ')
    (hpres : ∀ (H H₀ : Subgroup Gal(K'/K)) (A : ValuationSubring K'),
      H₀ ≤ H → 0 < H₀.relIndex H → Nonempty (H ≃* Gal(κ'/κ)) →
      A.comap (algebraMap K K') ≠ ⊤ → H₀ ≤ MulAction.stabilizer Gal(K'/K) A →
      ∃ κ₀ : IntermediateField κ κ', Nonempty (H₀ ≃* Gal(κ'/↥κ₀))) :
    InjectionFiniteIndex p K K' κ κ' := by
  intro H H₀ A hH₀le hH₀fin hκ hA hH₀le_stab
  obtain ⟨κ₀, h₀⟩ := hpres H H₀ A hH₀le hH₀fin hκ hA hH₀le_stab
  exact relIndex_pos_of_localInjection hD A hA H₀ hH₀le_stab κ₀ h₀

/-- **`IndecomposedPrime` from its presented form** (the additional clause is simply dropped). -/
theorem indecomposedPrime_of_presented (h : IndecomposedPrimePresented p K K' κ κ') :
    IndecomposedPrime p K K' κ κ' := by
  intro H hHclosed hκ A x hx
  obtain ⟨κ₀, H₀, A', hH₀le, hH₀fin, -, hA', hH₀le_stab⟩ := h H hHclosed hκ A x hx
  exact ⟨H₀, A', hH₀le, hH₀fin, hA', hH₀le_stab⟩

/-- **Route II of the reduction: the criterion from the presented indecomposed-prime input and the
*local* form of Neukirch's Korollar 1.**

This is the reduction in which the input `InjectionFiniteIndex` — the finiteness of the relative
index of the open subgroup — is *proved* (`relIndex_pos_of_localInjection`) from the local form
`LocalInjectionFiniteIndexSubgroup κ κ'` of Neukirch's Korollar 1 (Ivanov's `lm:locfinindex`) and
the presentation of the open subgroup supplied by `IndecomposedPrimePresented`. -/
theorem localDecompositionCriterion_of_presentedInputs
    (hInd : IndecomposedPrimePresented p K K' κ κ')
    (hD : LocalInjectionFiniteIndexSubgroup κ κ') (hInf : LocalGaloisInfinite κ κ')
    (hIdx : IndexOneOfSelfNormalizing p K K' κ κ') :
    NK.BrauerHasse.LocalDecompositionCriterion p K K' κ κ' := by
  intro H hHclosed hN hκ A x hx
  obtain ⟨κ₀, H₀, A', hH₀le, hH₀fin, hH₀pres, hA', hH₀le_stab⟩ := hInd H hHclosed hκ A x hx
  -- Neukirch's Korollar 1 (local form): `H₀` is open in `D_{A'}`
  have hH₀fin_stab := relIndex_pos_of_localInjection hD A' hA' H₀ hH₀le_stab κ₀ hH₀pres
  -- `H` is infinite, so Ivanov's `lm:finindexlm` pulls it into `D_{A'}`
  have hκne := hκ
  obtain ⟨e⟩ := hκne
  haveI : Infinite (Gal(κ'/κ)) := hInf
  have hHinf : Nat.card ↥H = 0 := by
    rw [Nat.card_congr e.toEquiv]
    exact Nat.card_eq_zero_of_infinite
  have hHle : H ≤ MulAction.stabilizer Gal(K'/K) A' :=
    le_stabSubgroup_of_openSubgroup_le A' hA' H H₀ hH₀le hH₀fin hHinf hH₀le_stab
  have hmul : H₀.relIndex H * H.relIndex (MulAction.stabilizer Gal(K'/K) A') =
      H₀.relIndex (MulAction.stabilizer Gal(K'/K) A') :=
    Subgroup.relIndex_mul_relIndex (H := H₀) (K := H)
      (L := MulAction.stabilizer Gal(K'/K) A') hH₀le hHle
  have hpos : 0 < H.relIndex (MulAction.stabilizer Gal(K'/K) A') := by
    have hprod : 0 < H₀.relIndex H * H.relIndex (MulAction.stabilizer Gal(K'/K) A') := by
      rw [hmul]
      exact hH₀fin_stab
    exact Nat.pos_of_mul_pos_left hprod
  exact ⟨A', hA', hIdx H hHclosed hN hκ A' hA' hHle hpos⟩

/-- **Route III of the reduction: the criterion from the indecomposed-prime input, the local form of
Neukirch's Korollar 1, Nikolov–Segal, and the index-one input.**

Here the global input `InjectionFiniteIndex` of Route I is *proved*
(`injectionFiniteIndex_of_localInjection_unconditional`) from `LocalInjectionFiniteIndexSubgroup`
(the local form of Korollar 1 as quoted by Ivanov — no closedness hypothesis) and Nikolov–Segal
(finite-index subgroups of the absolute Galois group of a `p`-adic field are closed). -/
theorem localDecompositionCriterion_of_localKorollar1 (hInd : IndecomposedPrime p K K' κ κ')
    (hD : LocalInjectionFiniteIndexSubgroup κ κ')
    (hNS : ∀ U : Subgroup Gal(κ'/κ), U.FiniteIndex → IsClosed (U : Set Gal(κ'/κ)))
    (hInf : LocalGaloisInfinite κ κ') (hIdx : IndexOneOfSelfNormalizing p K K' κ κ') :
    NK.BrauerHasse.LocalDecompositionCriterion p K K' κ κ' :=
  localDecompositionCriterion hInd
    (injectionFiniteIndex_of_localInjection_unconditional hD hNS) hInf hIdx

end

end NK.LocalDecomposition
