import Mathlib
import Submission.NK.Reconstruct.denseChebotarev
import Submission.NK.Reconstruct.PlaceCorrespondence
import Submission.NK.Reconstruct.frobeniusCorrespondence_of_place
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The σ-based Frobenius correspondence within `R` from the place-based one

The *Frobenius correspondence* (input (b) of the reconstruction of Neukirch–Uchida) has two
presentations, compare `Submission/Work/Reconstruct/PlaceCorrespondence.lean` and
`Submission/Work/Reconstruct/denseChebotarev.lean`:

* the σ-free, place-based one, `NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a`, and
* the σ-based one, `NK.Reconstruct.FrobeniusCorrespondence ϕ σ`, consumed by the endgame of
`NK.Reconstruct.exists_sigma_of_frobeniusCorrespondence`;

in the restricted form used when Čebotarev only provides primes inside a set `R` of full Dirichlet
density, the σ-based statement is `NK.Reconstruct.FrobeniusCorrespondenceWithin ϕ σ R`
(`Submission/Work/Reconstruct/denseChebotarev.lean`): only the primes of `R` are considered.

This file proves the restricted passage
`NK.Reconstruct.frobeniusCorrespondenceWithin_of_place_within`, the analogue of
`NK.Reconstruct.frobeniusCorrespondence_of_place` in which the realization of the place
correspondence by `σ` is only assumed at the places `A` whose prime of `𝓞 K₁` lies in `R` — which is
exactly what is available from the local correspondence together with Čebotarev.

The argument is that of `NK.Reconstruct.frobeniusCorrespondence_of_place`:

* the level `L₁ ⊆ K₁'` of a pair identified by `σ` is `σ(L₂)` (`eq_sigmaLevel_of_ringEquiv`), so
  the level `levelMap ϕ L₁` of `ϕ` is `L₂` (`hlvl`);
* a place `A` of `K₁'` over a given prime `P` of the level `L₁` exists, whose trace on `K₁` is the
  valuation ring of the prime `p` below `P` (`exists_place_over_prime`); in particular the prime of
  `𝓞 K₁` below `A` is `p`, which lies in `R` by hypothesis, so that the *restricted* realization
  hypothesis applies at `A`;
* the level-prime of `A` is `P` (`primeOfLevel_eq_of_comap_eq`);
* the Frobenius statement produced by `b` at the level `L₁` is transported across the equality
  `levelMap ϕ L₁ = L₂` (`isFrobAt_primeOfLevel_of_eq`);
* the transported level-prime is `primeTransport τ P`, because `σ` realizes the place
  correspondence `a` at `A` and because the valuation subring of the transformed prime is the
  transform of the valuation subring (`valuationSubringAtPrime_primeTransport`).
-/

set_option linter.style.haveILetI false

namespace NK.Reconstruct

open IsDedekindDomain

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-! ## The realization of the place map at a single place -/

/-- **The trace of a place below a corresponding place of the two levels**, assuming the
realization `(a.placeMap A).comap σ.symm = A` only at the single place `A`.

If `σ` realizes the place correspondence `a` at `A` and `τ : ↥L₁ ≃+* ↥L₂` is the restriction of
`σ.symm`, then the trace on `𝓞 L₂` of the place `a.placeMap A` of `K₂'` is the transform, under
`τ`, of the trace on `𝓞 L₁` of the place `A` of `K₁'`. -/
lemma comap_placeMap_level_of_eq {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} (a : LocalCorrespondence ϕ)
    (σ : K₂' ≃+* K₁') {A : FinitePlaceOf K₁ K₁'}
    (hrealA : (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1)
    {L₁ : IntermediateField K₁ K₁'} {L₂ : IntermediateField K₂ K₂'}
    (τ : ↥L₁ ≃+* ↥L₂) (hτ : ∀ x : ↥L₁, (τ x : K₂') = σ.symm (x : K₁')) :
    (a.placeMap A).1.comap (algebraMap ↥L₂ K₂') =
      (A.1.comap (algebraMap ↥L₁ K₁')).comap (τ.symm : ↥L₂ →+* ↥L₁) := by
  ext y
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap, ValuationSubring.mem_comap,
    ← hrealA, ValuationSubring.mem_comap]
  have key : σ.symm (algebraMap ↥L₁ K₁' (τ.symm y)) = algebraMap ↥L₂ K₂' y := by
    have h1 := hτ (τ.symm y)
    rw [RingEquiv.apply_symm_apply] at h1
    exact h1.symm
  exact Iff.of_eq (congrArg (fun z => z ∈ (a.placeMap A).1) key.symm)

/-! ## The Frobenius correspondence in the σ-based form, restricted to `R` -/

theorem frobeniusCorrespondenceWithin_of_place_within {K₁ K₂ K₁' K₂' : Type*} [Field K₁]
    [Field K₂] [Field K₁'] [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁']
    [Algebra K₂ K₂'] [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ) (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    {R : Set (NK.Chebotarev.PrimeIdeal K₁)}
    (hlvl : NK.Reconstruct.AgreesOnLevels ϕ hϕ σ hσ)
    (hreal : ∀ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
      Submission.NeukirchUchida.primeOf A.1 A.2 ∈ R →
        (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1)
    (b : NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a) :
    NK.Reconstruct.FrobeniusCorrespondenceWithin ϕ σ R := by
  intro L₂ _ _ _ L₁ _ _ _ τ hτ p hp P hP _hunr g hg
  -- the level `L₁` is the image of `L₂` under `σ`
  have hL₁ : L₁ = sigmaLevel σ hσ L₂ := eq_sigmaLevel_of_ringEquiv σ hσ τ hτ
  subst hL₁
  -- hence the level of `ϕ` attached to it is `L₂`
  have hlevel : levelMap ϕ (sigmaLevel σ hσ L₂) = L₂ := hlvl L₂
  haveI hfdL : FiniteDimensional K₂ (levelMap ϕ (sigmaLevel σ hσ L₂)) :=
    finiteDimensional_levelMap hϕ (sigmaLevel σ hσ L₂)
  haveI hnL : Normal K₂ (levelMap ϕ (sigmaLevel σ hσ L₂)) :=
    normal_levelMap hϕ (sigmaLevel σ hσ L₂)
  haveI hnfL : NumberField ↥(levelMap ϕ (sigmaLevel σ hσ L₂)) :=
    numberField_levelMap hϕ (sigmaLevel σ hσ L₂)
  -- a place of `K₁'` over the prime `P` of the level, over the prime `p` of `K₁`
  obtain ⟨A, hAcomap, hAval⟩ := exists_place_over_prime (sigmaLevel σ hσ L₂) p P hP
  have hAne : A.comap (algebraMap K₁ K₁') ≠ ⊤ := by
    rw [hAval]; exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top p
  let A' : FinitePlaceOf K₁ K₁' := ⟨A, hAne⟩
  -- the prime below `A` is `p`, hence belongs to `R`, so `σ` realizes `a` at `A`
  have hprimeA : Submission.NeukirchUchida.primeOf A'.1 A'.2 = p := by
    apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := K₁)
    rw [← Submission.NeukirchUchida.primeOf_spec A'.1 A'.2]
    exact hAval
  have hrealA : (a.placeMap A').1.comap (σ.symm : K₁' →+* K₂') = A'.1 :=
    hreal A' (by rw [hprimeA]; exact hp)
  have hAL : (A'.1).comap (algebraMap ↥(sigmaLevel σ hσ L₂) K₁') ≠ ⊤ :=
    comap_level_ne_top A'.2 (sigmaLevel σ hσ L₂)
  have hprime : primeOfLevel A'.1 (sigmaLevel σ hσ L₂) hAL = P :=
    primeOfLevel_eq_of_comap_eq (sigmaLevel σ hσ L₂) hAcomap hAL
  -- the place-based Frobenius correspondence
  have hb : NK.Chebotarev.IsFrobAt
      (primeOfLevel (a.placeMap A').1 (levelMap ϕ (sigmaLevel σ hσ L₂))
        (comap_level_ne_top (a.placeMap A').2 (levelMap ϕ (sigmaLevel σ hσ L₂))))
      (AlgEquiv.restrictNormalHom (levelMap ϕ (sigmaLevel σ hσ L₂)) (ϕ g)) :=
    b (sigmaLevel σ hσ L₂) A' g (by rw [hprime]; exact hg)
  -- transported to the level `L₂`
  have hb₂ : NK.Chebotarev.IsFrobAt
      (primeOfLevel (a.placeMap A').1 L₂ (comap_level_ne_top (a.placeMap A').2 L₂))
      (AlgEquiv.restrictNormalHom L₂ (ϕ g)) :=
    (isFrobAt_primeOfLevel_of_eq hlevel (a.placeMap A').1 (a.placeMap A').2 (ϕ g)).mp hb
  -- the transported level-prime is the transport of `P` along `τ`
  have hQ : primeOfLevel (a.placeMap A').1 L₂ (comap_level_ne_top (a.placeMap A').2 L₂)
      = primeTransport τ P := by
    apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥L₂)
    rw [← primeOfLevel_spec (a.placeMap A').1 L₂ (comap_level_ne_top (a.placeMap A').2 L₂),
      comap_placeMap_level_of_eq a σ hrealA τ hτ, hAcomap,
      ← valuationSubringAtPrime_primeTransport τ P]
  rw [hQ] at hb₂
  exact hb₂

end NK.Reconstruct
