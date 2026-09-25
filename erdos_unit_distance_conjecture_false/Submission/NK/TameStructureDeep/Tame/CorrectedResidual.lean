/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The corrected tamely ramified structure theorem, assembled

For `κ = K_𝔭` and the *corrected* wild inertia `V_κ = Gal(K'/κ^{tr})`
(`NK.TameStructureDeep.Tame.correctedWildInertia`, i.e. the fixing subgroup of the maximal tamely
ramified extension `Tame.tameClosure`), this file assembles everything the local structure theorem
needs about the tame inertia.  Every field below is a **theorem** of this chapter:

* `correctedWildInertia_le_inertia` — `V_κ ≤ I_κ` (`Tame/TameClosure.lean`);
* `correctedWildInertia_normal` — `V_κ ◁ G_κ` (`Tame/CorrectedInterface.lean`);
* `isProCyclic_correctedWildInertia` — `I_κ/V_κ` is pro-cyclic;
* `isProPrimeToP_correctedWildInertia` — `I_κ/V_κ` is pro-prime-to-`p`;
* `commutator_mem_correctedWildInertia` — `[I_κ, I_κ] ≤ V_κ` (`Tame/inertiaQuotient.lean`);
* `exists_frobenius_adicCompletion` — the normalised Frobenius exists (`Core.lean`);
* `isFrobeniusFor_iff_isTameFrobeniusLift` — **the Frobenius normalisation**: a normalised
  Frobenius is exactly a tame Frobenius lift, i.e. `frobenius_iff` for the corrected `V_κ`,
  assembled from `Tame/kummer_tateTwist_of_pow_eq.lean`
  (`IsFrobeniusFor ⟹ IsTameFrobeniusLift`) and
  `Tame/actsAsFrobenius_of_isTameFrobeniusLift.lean` (the converse, via the Kummer pairing);
* `unramifiedQuotient_adicCompletion` — `G_κ ⧸ I_κ ≅ Ẑ` (`Unramified.lean`).

What is *not* here: the maximality clause of `NK.LocalTame.IsMaxNormalProCyclicInQuotient`,
i.e. that every normal pro-cyclic subgroup `J/V_κ ≤ G_κ/V_κ` lies in `I_κ/V_κ`.  Per README §7.2
(corrected four times) this clause is **TRUE** — the cyclotomic character on the tame inertia is
faithful, `ker χ = ⋂_{ℓ≠p,n} ord_{ℓ^n}(q) Ẑ = 0`, which is the formalised `κ^ur = κ(μ_{p'})` — but it
is not yet *proved* in the workspace's vocabulary; see
`NK.TameStructureDeep.Tame.isMaximal_correctedWildInertia`.  Also not here: Shimizu's lemma
(local class field theory) for the abelianisation.
-/
import Mathlib
import Submission.NK.TameStructureDeep.Tame.CorrectedInterface
import Submission.NK.TameStructureDeep.Tame.isProCyclic_correctedWildInertia
import Submission.NK.TameStructureDeep.Tame.isProPrimeToP_correctedWildInertia
import Submission.NK.TameStructureDeep.Tame.isTameFrobeniusLift_correctedWildInertia
import Submission.NK.TameStructureDeep.Tame.actsAsFrobenius_of_isTameFrobeniusLift
import Submission.NK.TameStructureDeep.Tame.inertiaQuotient
import Submission.NK.TameStructureDeep.Tame.UnramifiedNoPow
import Submission.NK.TameStructureDeep.Unramified
import Submission.NK.TameStructureDeep.Core
import Submission.NK.TameStructureDeep.Support.quotientImage_normal_iff

open scoped Classical

namespace NK.TameStructureDeep.Tame

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
  [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']

/-- **The Frobenius normalisation for the corrected wild inertia** (NSW (12.1.8); Iwasawa): for a
uniformiser `π` of `κ = K_𝔭`, an element of `G_κ` is a normalised Frobenius (lies outside `I_κ` and
acts on the prime-to-`p` roots of unity by `ζ ↦ ζ^q`) **iff** it is a tame Frobenius lift: it lies
outside `I_κ` and conjugates the tame inertia `I_κ/V_κ = Gal(κ^{tr}/κ^{ur})` by the `q`-th power
map.

Both directions are theorems of this chapter:
`Tame.isTameFrobeniusLift_correctedWildInertia` (`⟹`, via the Tate twist on the Kummer layers) and
`Tame.actsAsFrobenius_of_isTameFrobeniusLift` (`⟸`, via the surjectivity of the Kummer pairing). -/
theorem isFrobeniusFor_iff_isTameFrobeniusLift {π : 𝔭.adicCompletionIntegers K}
    (hπ : IsUniformizerAt 𝔭 π) {q : ℕ} {F : Gal(K'/𝔭.adicCompletion K)} :
    NK.LocalAnabelian.IsFrobeniusFor (κ := 𝔭.adicCompletion K) (K' := K') (resCharAt 𝔭) q F ↔
      NK.LocalTame.IsTameFrobeniusLift q
        (correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K') (resCharAt 𝔭) π)
        (NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K')
          (resCharAt 𝔭)) F := by
  have hp : (resCharAt 𝔭).Prime := NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  have hπ0 : (π : 𝔭.adicCompletion K) ≠ 0 := by
    intro h
    have hz : π = 0 := Subtype.ext h
    exact IsDiscreteValuationRing.not_a_field (𝔭.adicCompletionIntegers K)
      (by rw [hπ, hz, Ideal.span_singleton_eq_bot])
  constructor
  · intro hF
    exact isTameFrobeniusLift_correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K')
      (π := (π : 𝔭.adicCompletion K)) hp.ne_one hπ0 hF
  · intro h
    exact ⟨h.1, actsAsFrobenius_of_isTameFrobeniusLift 𝔭 hπ h⟩

/-- **The corrected tamely ramified structure theorem, assembled.**  For a uniformiser `π` of
`κ = K_𝔭`, the tame inertia `I_κ/V_κ` for `V_κ = Gal(K'/κ^{tr})` is pro-cyclic, pro-prime-to-`p`,
abelian, contained in `I_κ` as a normal subgroup, `G_κ ⧸ I_κ ≅ Ẑ`, a normalised Frobenius exists,
and it is characterised by the `q`-power action on the tame inertia.  Every conjunct is a theorem
of this chapter (`Tame/`); see `Tame/CorrectedResidual.lean`'s header for the references. -/
theorem correctedTameStructure_proved {π : 𝔭.adicCompletionIntegers K}
    (hπ : IsUniformizerAt 𝔭 π) [hV : (correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K')
      (resCharAt 𝔭) (π : 𝔭.adicCompletion K)).Normal] :
    correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K') (resCharAt 𝔭)
          (π : 𝔭.adicCompletion K) ≤
        NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K') (resCharAt 𝔭) ∧
      NK.LocalTame.IsProCyclic
        ↥(NK.LocalTame.quotientImage
          (correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K') (resCharAt 𝔭)
            (π : 𝔭.adicCompletion K))
          (NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K')
            (resCharAt 𝔭))) ∧
      NK.LocalTame.IsProPrimeToP (resCharAt 𝔭)
        ↥(NK.LocalTame.quotientImage
          (correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K') (resCharAt 𝔭)
            (π : 𝔭.adicCompletion K))
          (NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K')
            (resCharAt 𝔭))) ∧
      (∀ σ ∈ (NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
          (resCharAt 𝔭)).fixingSubgroup,
        ∀ τ ∈ (NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
          (resCharAt 𝔭)).fixingSubgroup,
          σ * τ * σ⁻¹ * τ⁻¹ ∈
            correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K') (resCharAt 𝔭)
              (π : 𝔭.adicCompletion K)) ∧
      Nonempty (Gal(K'/𝔭.adicCompletion K) ⧸
        NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K')
          (resCharAt 𝔭) ≃* NK.LocalAnabelian.Zhat) ∧
      ∃ F : Gal(K'/𝔭.adicCompletion K),
        NK.LocalAnabelian.IsFrobeniusFor (κ := 𝔭.adicCompletion K) (K' := K')
          (resCharAt 𝔭) (NK.LocalStructure.residueCard K 𝔭) F := by
  refine ⟨correctedWildInertia_le_inertia (K' := K') (resCharAt 𝔭) (π : 𝔭.adicCompletion K),
    ?_, ?_, ?_, ?_, ?_⟩
  · exact isProCyclic_correctedWildInertia 𝔭 hπ
  · exact isProPrimeToP_correctedWildInertia 𝔭 hπ
  · intro σ hσ τ hτ
    exact commutator_mem_correctedWildInertia (p := resCharAt 𝔭)
      (NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭).ne_one σ τ hσ hτ
  · exact NK.TameStructureDeep.unramifiedQuotient_adicCompletion (K := K) 𝔭
  · exact NK.TameStructureDeep.exists_frobenius_adicCompletion (K := K) 𝔭

end

end NK.TameStructureDeep.Tame
