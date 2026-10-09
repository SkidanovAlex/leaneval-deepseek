/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The per-finite-prime form, and the `(a)`-chain

`Submission/Work/BrauerTwist/Preserves.lean` reduces the endgame input (a) of the Neukirch–Uchida
development,

`Submission.NeukirchUchida.PreservesDecompositionGroups ϕ`,

to the availability, at every finite prime `𝔭` of `K₁`, of the *twisted local data* at
`κ = 𝔭.adicCompletion K₁`:

`∃ p, p.Prime ∧ LocalH2Input p K₂ K₂' κ κ' ∧ Sha2Vanishing p K₂ K₂' κ κ' ∧
      LocalDecompositionCriterion p K₂ K₂' κ κ'`.

This file supplies that data from the inputs of `Submission/Work/Indecomposed/`: the per-prime Hasse
input `NK.HasseTwist.Sha2Input`, the rank data `NK.Indecomposed.RankData` and the local
reconstruction `NK.Indecomposed.LocalReconstruction` at the completion.  Two of the three
components are *derived*:

* `Sha2Vanishing` is `NK.HasseTwist.sha2Vanishing` (the Hasse chapter);
* `LocalDecompositionCriterion` is `NK.Indecomposed.localDecompositionCriterion_of_twistedHasse`;
* `LocalH2Input` (the existence of a non-zero class in `H²(H, μ_p)`) is *not* an extra input: it
  follows from the rank data, since `Nat.card (H2Twist p H) = p ≥ 2`
  (`NK.Indecomposed.localH2Input_of_rankData`).

The resulting theorem `NK.Indecomposed.preservesDecompositionGroups_of_hasseAt` is the `(a)`-chain
with the per-prime rank data and local reconstruction as its only inputs.
-/

import Submission.NK.Indecomposed.Main
import Submission.NK.BrauerTwist.Preserves
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open IsDedekindDomain.HeightOneSpectrum

universe u

namespace NK.Indecomposed

/-- **The local data at a finite prime, in the shape consumed by the `(a)`-chain.**  At a finite
prime `𝔭` of `K`, the Hasse input `Sha2Input` for the completion `κ = 𝔭.adicCompletion K`, the rank
data `RankData` and the local reconstruction `LocalReconstruction` at `κ` produce the triple
(`LocalH2Input`, `Sha2Vanishing`, `LocalDecompositionCriterion`) which
`NK.BrauerTwist.preservesDecompositionGroups_of_localGalois` consumes.

The `LocalH2Input` component is derived from the rank data (`localH2Input_of_rankData`), the
`Sha2Vanishing` component is the Hasse chapter's `NK.HasseTwist.sha2Vanishing`, and the
`LocalDecompositionCriterion` component is Neukirch's criterion assembled in
`NK.Indecomposed.localDecompositionCriterion_of_twistedHasse`. -/
theorem exists_localData_of_rankData {K₁ K₂ K₂' : Type u} [Field K₁] [NumberField K₁]
    [Field K₂] [NumberField K₂] [Field K₂'] [Algebra K₂ K₂'] [IsSepClosure K₂ K₂']
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)) (p : ℕ)
    (hHasse : NK.HasseTwist.Sha2Input p K₂ K₂'
      (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)))
    (hrank : RankData p K₂ K₂' (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)))
    (hrec : LocalReconstruction p K₂ K₂' (𝔭.adicCompletion K₁)
      (SeparableClosure (𝔭.adicCompletion K₁))) :
    ∃ q : ℕ, q.Prime ∧
      NK.BrauerTwist.LocalH2Input q K₂ K₂'
        (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)) ∧
      NK.BrauerTwist.Sha2Vanishing q K₂ K₂'
        (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)) ∧
      NK.BrauerTwist.LocalDecompositionCriterion q K₂ K₂'
        (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)) :=
  ⟨p, hHasse.hp, localH2Input_of_rankData hrank,
    NK.HasseTwist.sha2Vanishing p hHasse,
    localDecompositionCriterion_of_twistedHasse (K := K₂) (K' := K₂')
      hHasse hrank.surj hrank.card_global hrank.card_local hrec⟩

/-- **The endgame input (a) from the per-prime Hasse input, the rank data and the local
reconstruction.**

Let `K₁, K₂` be number fields with separable closures `K₁', K₂'` and `ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)`
a homeomorphism.  Suppose that for every finite prime `𝔭` of `K₁` (and, in the other direction,
every finite prime `𝔮` of `K₂`) there are a prime `p`, the Hasse input `Sha2Input` at the completion
`K₁,𝔭` (with the number field `K₂`), the rank data `RankData` and the local reconstruction
`LocalReconstruction`.  Then `ϕ` preserves the decomposition groups.

This is Neukirch–Uchida's input (a) with the criterion, the Hasse principle and the local Brauer
input all supplied by the present chapter and its siblings
(`NK.BrauerTwist.preservesDecompositionGroups_of_localGalois` does the remaining local work). -/
theorem preservesDecompositionGroups_of_hasseAt
    {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (h₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ,
        NK.HasseTwist.Sha2Input p K₂ K₂'
          (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        RankData p K₂ K₂'
          (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        LocalReconstruction p K₂ K₂'
          (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)))
    (h₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ p : ℕ,
        NK.HasseTwist.Sha2Input p K₁ K₁'
          (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        RankData p K₁ K₁'
          (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        LocalReconstruction p K₁ K₁'
          (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂))) :
    Submission.NeukirchUchida.PreservesDecompositionGroups ϕ :=
  NK.BrauerTwist.preservesDecompositionGroups_of_localGalois (K₁ := K₁) (K₂ := K₂)
    (K₁' := K₁') (K₂' := K₂') ϕ he
    (fun 𝔭 => by
      obtain ⟨p, hHasse, hrank, hrec⟩ := h₁ 𝔭
      exact exists_localData_of_rankData (K₁ := K₁) (K₂ := K₂) (K₂' := K₂') 𝔭 p hHasse hrank hrec)
    (fun 𝔮 => by
      obtain ⟨p, hHasse, hrank, hrec⟩ := h₂ 𝔮
      exact exists_localData_of_rankData (K₁ := K₂) (K₂ := K₁) (K₂' := K₁') 𝔮 p hHasse hrank hrec)

end NK.Indecomposed
