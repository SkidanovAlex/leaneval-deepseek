/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The global corollary: corresponding places have the same residue characteristic and local degree

This is the form in which the local input of the Neukirch–Uchida theorem is consumed by the
global endgame (CoNF XII (12.1.9)/(12.1.10); Ivanov, arXiv:1309.3046, §3):

  for number fields `K₁`, `K₂` with separable closures `K₁'`, `K₂'`, an isomorphism
  `ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)` of absolute Galois groups, places `A` of `K₁'` and `B` of `K₂'`
  over finite primes `𝔭`, `𝔮`, and the hypothesis `ϕ(D_A) = D_B` (the local correspondence),

* `primeBelow K₁ 𝔭 = primeBelow K₂ 𝔮`: the rational primes below `𝔭` and `𝔮` coincide; and
* `localDegree K₁ 𝔭 = localDegree K₂ 𝔮`, i.e. `[K₁,𝔭 : ℚ_p] = [K₂,𝔮 : ℚ_p]`.

Here `localDegree K 𝔭` is by definition the `ℚ_p`-dimension of `K_𝔭`
(`Module.finrank ((primeBelow K 𝔭).adicCompletion ℚ) (𝔭.adicCompletion K)`; see
`NK.LocalInputs.Defs.localDegree`), so the second conclusion is exactly the usual
`[K₁,𝔭 : ℚ_p] = [K₂,𝔮 : ℚ_p]`.

The proof is an application of `NK.LocalAnabelian.residueChar_and_degree_eq_of_padicGaloisInputs`
to the instantiated local inputs (`NK.LocalInputs.Instantiation`), where the isomorphism of the
local absolute Galois groups is obtained from `ϕ(D_A) = D_B` and

  `D_A ≅ Gal(κ̄/κ)`,  `κ = 𝔭.adicCompletion K₁`

(`NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois`).

Together with the local-degree bookkeeping `∑_{𝔮|p} [K_𝔮 : ℚ_p] = [K : ℚ]`
(`NK.Mine.sumFinrank_adicCompletion_eq_finrank`) this gives `[K₁ : ℚ] = [K₂ : ℚ]` for a
Neukirch–Uchida isomorphism, which is the input of the Čebotarev reconstruction.

**Vocabulary.**  The place hypotheses are stated with `NK.Mine.decompositionGroupOf`, which is
*definitionally* `Submission.NeukirchUchida.decompositionGroup`
(and `decompositionGroup₂` for the second field), so a caller holding the hypothesis
`(decompositionGroup A).map ϕ = decompositionGroup₂ B` of
`Submission/NeukirchUchida/Reduction.lean` can pass it here unchanged.
-/
import Submission.NK.Mine.CompletionAPI
import Submission.NK.LocalInputs.Instantiation
import Submission.NK.LocalInputs.ResidueChar.primesEquiv_primeBelow
import Submission.NK.LocalInputs.Global.nonempty_mulEquiv_sepClosure_of_decompositionGroup_map
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical Pointwise
open IsDedekindDomain.HeightOneSpectrum

namespace NK.LocalInputs

noncomputable section

universe u

/-- **The global corollary (main form).**  Corresponding places have the same residue
characteristic and the same absolute local degree.

The hypotheses on the local inputs are `LocalFieldInputs` and `LocalGaloisInputs` for both
completions; they are the classical structure theory of the `p`-adic field `K_𝔭` (see
`NK.LocalInputs.Inputs`), stated for `p` and `q` the respective residue characteristics. -/
theorem residueChar_and_localDegree_eq_of_decompositionGroup
    {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁))
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂))
    (A : ValuationSubring K₁') (B : ValuationSubring K₂')
    (hA : A.comap (algebraMap K₁ K₁') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₁ 𝔭)
    (hB : B.comap (algebraMap K₂ K₂') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₂ 𝔮)
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hAB : (NK.Mine.decompositionGroupOf K₁ K₁' A).map (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) =
      NK.Mine.decompositionGroupOf K₂ K₂' B)
    {p q : ℕ} (hF₁ : LocalFieldInputs K₁ 𝔭 p)
    (hG₁ : LocalGaloisInputs K₁ 𝔭 (SeparableClosure (𝔭.adicCompletion K₁)) p)
    (hF₂ : LocalFieldInputs K₂ 𝔮 q)
    (hG₂ : LocalGaloisInputs K₂ 𝔮 (SeparableClosure (𝔮.adicCompletion K₂)) q) :
    p = q ∧ localDegree K₁ 𝔭 = localDegree K₂ 𝔮 := by
  obtain ⟨ψ⟩ :=
    NK.LocalInputs.Global.nonempty_mulEquiv_sepClosure_of_decompositionGroup_map
      𝔭 𝔮 A B hA hB ϕ hAB
  have h₁ := padicGaloisInputs_of_localInputs_sepClosure 𝔭 hF₁ hG₁
  have h₂ := padicGaloisInputs_of_localInputs_sepClosure 𝔮 hF₂ hG₂
  obtain ⟨hpq, -, hd⟩ :=
    NK.LocalAnabelian.residueChar_and_degree_eq_of_padicGaloisInputs h₁ h₂ ψ
  exact ⟨hpq, hd⟩

/-- **The global corollary, in the form in which the places are described by the primes of the
number fields**: the rational primes below `𝔭` and `𝔮` coincide, i.e.
`primeBelow K₁ 𝔭 = primeBelow K₂ 𝔮` as primes of `𝓞 ℚ`.

This refines `residueChar_and_localDegree_eq_of_decompositionGroup` (whose `p = q` is the
statement that the residue fields have the same characteristic) to the statement about the
rational primes themselves. -/
theorem primeBelow_eq_of_decompositionGroup
    {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁))
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂))
    (A : ValuationSubring K₁') (B : ValuationSubring K₂')
    (hA : A.comap (algebraMap K₁ K₁') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₁ 𝔭)
    (hB : B.comap (algebraMap K₂ K₂') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₂ 𝔮)
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hAB : (NK.Mine.decompositionGroupOf K₁ K₁' A).map (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) =
      NK.Mine.decompositionGroupOf K₂ K₂' B)
    {p q : ℕ} (hF₁ : LocalFieldInputs K₁ 𝔭 p)
    (hG₁ : LocalGaloisInputs K₁ 𝔭 (SeparableClosure (𝔭.adicCompletion K₁)) p)
    (hF₂ : LocalFieldInputs K₂ 𝔮 q)
    (hG₂ : LocalGaloisInputs K₂ 𝔮 (SeparableClosure (𝔮.adicCompletion K₂)) q) :
    primeBelow K₁ 𝔭 = primeBelow K₂ 𝔮 := by
  have hpq : p = q :=
    (residueChar_and_localDegree_eq_of_decompositionGroup 𝔭 𝔮 A B hA hB ϕ hAB hF₁ hG₁ hF₂ hG₂).1
  have h₁ : (Rat.HeightOneSpectrum.primesEquiv (primeBelow K₁ 𝔭)).1 = p :=
    NK.LocalInputs.ResidueChar.primesEquiv_primeBelow 𝔭 hF₁.hp hF₁.residue_char
  have h₂ : (Rat.HeightOneSpectrum.primesEquiv (primeBelow K₂ 𝔮)).1 = q :=
    NK.LocalInputs.ResidueChar.primesEquiv_primeBelow 𝔮 hF₂.hp hF₂.residue_char
  refine Rat.HeightOneSpectrum.primesEquiv.injective ?_
  exact Subtype.ext (by rw [h₁, h₂, hpq])

/-- **The global corollary, combined statement**: corresponding places have the same rational
prime below and the same absolute local degree. -/
theorem primeBelow_and_localDegree_eq_of_decompositionGroup
    {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁))
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂))
    (A : ValuationSubring K₁') (B : ValuationSubring K₂')
    (hA : A.comap (algebraMap K₁ K₁') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₁ 𝔭)
    (hB : B.comap (algebraMap K₂ K₂') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₂ 𝔮)
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hAB : (NK.Mine.decompositionGroupOf K₁ K₁' A).map (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) =
      NK.Mine.decompositionGroupOf K₂ K₂' B)
    {p q : ℕ} (hF₁ : LocalFieldInputs K₁ 𝔭 p)
    (hG₁ : LocalGaloisInputs K₁ 𝔭 (SeparableClosure (𝔭.adicCompletion K₁)) p)
    (hF₂ : LocalFieldInputs K₂ 𝔮 q)
    (hG₂ : LocalGaloisInputs K₂ 𝔮 (SeparableClosure (𝔮.adicCompletion K₂)) q) :
    primeBelow K₁ 𝔭 = primeBelow K₂ 𝔮 ∧ localDegree K₁ 𝔭 = localDegree K₂ 𝔮 :=
  ⟨primeBelow_eq_of_decompositionGroup 𝔭 𝔮 A B hA hB ϕ hAB hF₁ hG₁ hF₂ hG₂,
    (residueChar_and_localDegree_eq_of_decompositionGroup 𝔭 𝔮 A B hA hB ϕ hAB
      hF₁ hG₁ hF₂ hG₂).2⟩

end

end NK.LocalInputs
