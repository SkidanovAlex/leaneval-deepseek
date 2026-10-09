import Mathlib
import Submission.Work.SSGRoute.ZConstruction.levelK_canonicalPairing
import Submission.Work.SSGRoute.ZConstruction.levelK_canonicalTransport
import Submission.Commons.NumberTheory.NumberField.Valuation.centralizer_stabilizer_valuationSubring_sepClosure
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The completion at places with the same level-`K` local group

For the place-transport of the canonical level-`K` pairing (`levelK_canonicalTransportStep.lean`)
one has to show that two finite places `A`, `A'` of `Ω` over `k` whose *level-`K` local groups*
`H_A = decomp k A ⊓ K.fixingSubgroup` agree give isomorphic completions
`κ_A ≅ κ_{A'}` of `↥K`.

The mathematical input is **rigidity of places of the separable closure** (CoNF XII
(12.1.3)/(12.1.4),
`Commons.NumberTheory.NumberField.Valuation.stabilizer_inf_stabilizer_eq_bot_of_ne`): distinct
places of `Ω` over finite primes of `↥K` have decomposition groups meeting in `⊥`, while the
decomposition group of a finite place is non-trivial.  Hence equal decomposition groups force the
places *themselves* to be equal (there is no normalizer ambiguity after all), so the two completions
are literally the same field and the ring equivalence is the identity.

The level-`K` local group already determines the decomposition group over `↥K`
(`decomp_levelK_eq_of_localGroup_eq`, `levelK_canonicalTransport.lean`), which is where the
hypothesis is used.
-/

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

set_option linter.unusedSectionVars false

/-- **Two finite places of `Ω` with the same decomposition group over a number field `K` are
equal** (rigidity of places): the decomposition groups of two *distinct* places over finite primes
meet in `⊥`, and the decomposition group of a finite place is non-trivial. -/
theorem eq_of_decomp_eq_of_finite {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] (K : IntermediateField k Ω) [NumberField ↥K] [IsSepClosure ↥K Ω]
    {A A' : ValuationSubring Ω}
    (hA : A.comap (algebraMap ↥K Ω) ≠ ⊤) (hA' : A'.comap (algebraMap ↥K Ω) ≠ ⊤)
    (hD : SSGRoute.decomp (k := ↥K) A = SSGRoute.decomp (k := ↥K) A') : A = A' := by
  by_contra hne
  have hbot := Commons.NumberTheory.NumberField.Valuation.stabilizer_inf_stabilizer_eq_bot_of_ne
    (K := ↥K) (K' := Ω) hne hA hA'
  simp only [SSGRoute.decomp] at hD
  rw [← hD, inf_idem] at hbot
  obtain ⟨σ, hσne, hσA⟩ :=
    Commons.NumberTheory.NumberField.Valuation.exists_ne_one_comap_eq_of_comap_ne_top
      (K := ↥K) (K' := Ω) A hA
  have hσmem : σ ∈ SSGRoute.decomp (k := ↥K) A :=
    (Commons.NumberTheory.NumberField.Valuation.comap_eq_iff_mem_stabilizer A σ).mp hσA
  simp only [SSGRoute.decomp] at hσmem
  rw [hbot] at hσmem
  exact hσne (Subgroup.mem_bot.mp hσmem)

/-- **Places with the same level-`K` local group have isomorphic completions.**  The local group
`levelKLocalGroup k Ω K A` determines the decomposition group of `A` over `↥K`
(`decomp_levelK_eq_of_localGroup_eq`), hence, by rigidity of places of the separable closure, the
place `A` itself: there is no room for a normalizer (or conjugate-place) ambiguity, and the two
completions of `↥K` are literally the same. -/
theorem levelK_completion_iso_of_localGroup_eq (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (A A' : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (hA' : SSGRoute.IsFinPlace k A')
    (h : levelKLocalGroup k Ω K A = levelKLocalGroup k Ω K A') :
    Nonempty (Work.SSGRoute.ZDataMup.mupCompletion (K := K) A
        (isFinPlace_of_isFinPlace_below (K := K) (A := A) hA) ≃+*
      Work.SSGRoute.ZDataMup.mupCompletion (K := K) A'
        (isFinPlace_of_isFinPlace_below (K := K) (A := A') hA')) := by
  have hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤ :=
    isFinPlace_of_isFinPlace_below (K := K) (A := A) hA
  have hAK' : A'.comap (algebraMap ↥K Ω) ≠ ⊤ :=
    isFinPlace_of_isFinPlace_below (K := K) (A := A') hA'
  have hD : SSGRoute.decomp (k := ↥K) A = SSGRoute.decomp (k := ↥K) A' :=
    decomp_levelK_eq_of_localGroup_eq (K := K) A A' h
  have hAA' : A = A' := eq_of_decomp_eq_of_finite K hAK hAK' hD
  subst hAA'
  refine ⟨RingEquiv.cast ?_⟩
  exact congrArg
    (fun q => Submission.NeukirchUchida.primeOf (K₁ := ↥K) (K₁' := Ω) A q)
    (Subsingleton.elim _ _)

end Work.SSGRoute.ZConstruction
