import Mathlib
import Submission.NK.Mine.PrimeCorrespondenceAPI

/-!
# The induced map on primes is a bijection

The local correspondence `primeMap ϕ h` of `Submission/NeukirchUchida/PrimeCorrespondence.lean`
sends a finite prime `𝔭` of `K₁` to the prime of `K₂` below the image under `placeMap ϕ h` of any
place of `K₁'` over `𝔭`.  Here we prove that it is a bijection.

Both directions are bookkeeping with the two structural facts already established in
`PlaceSystem.lean`/`PrimeCorrespondence.lean`:

* the `Gal(K'/K)`-action is transitive on the places over a fixed prime
  (`exists_smul_eq_of_comap_eq'`), and
* the place map of the local correspondence is a `Gal`-equivariant bijection
  (`placeMap_bijective`, `placeMap_smul`), while the prime below a place only depends on the trace.

Injectivity: if `primeMap ϕ h 𝔭₁ = primeMap ϕ h 𝔭₂` then the two image places are places over a
common prime, hence conjugate by some `σ ∈ Gal(K₂'/K₂)`; pulling `σ` back along the (bijective)
`ϕ` and applying equivariance of `placeMap` shows that the two chosen places over `𝔭₁` and `𝔭₂` are
conjugate, so the primes below them coincide.
Surjectivity: given `𝔮` of `K₂`, take a place over it, a preimage place under `placeMap`, and apply
the same argument.
-/

namespace NK.NeukirchUchida

open scoped Pointwise
open Submission.NeukirchUchida

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- The prime of `K₁` below the place `placeOver p` is `p`. -/
lemma primeOf_placeOver (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)) :
    primeOf (K₁ := K₁) (K₁' := K₁')
      (placeOver (K₁ := K₁) (K₁' := K₁') p).1
      (placeOver (K₁ := K₁) (K₁' := K₁') p).2 = p := by
  apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := K₁)
  rw [← primeOf_spec (placeOver (K₁ := K₁) (K₁' := K₁') p).1
      (placeOver (K₁ := K₁) (K₁' := K₁') p).2,
    placeOver_spec (K₁ := K₁) (K₁' := K₁') p]

theorem primeMap_bijective {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (h : Submission.NeukirchUchida.PreservesDecompositionGroups ϕ) :
    Function.Bijective (Submission.NeukirchUchida.primeMap ϕ h) := by
  constructor
  · intro p₁ p₂ hpq
    have hpq' : primeOf (K₁:=K₂) (K₁':=K₂')
          (placeMap ϕ h (placeOver (K₁:=K₁) (K₁':=K₁') p₁)).1
          (placeMap ϕ h (placeOver (K₁:=K₁) (K₁':=K₁') p₁)).2 =
        primeOf (K₁:=K₂) (K₁':=K₂')
          (placeMap ϕ h (placeOver (K₁:=K₁) (K₁':=K₁') p₂)).1
          (placeMap ϕ h (placeOver (K₁:=K₁) (K₁':=K₁') p₂)).2 := hpq
    have hcomap : (placeMap ϕ h (placeOver (K₁:=K₁) (K₁':=K₁') p₁)).1.comap (algebraMap K₂ K₂') =
        (placeMap ϕ h (placeOver (K₁:=K₁) (K₁':=K₁') p₂)).1.comap (algebraMap K₂ K₂') := by
      rw [primeOf_spec (placeMap ϕ h (placeOver (K₁:=K₁) (K₁':=K₁') p₁)).1
            (placeMap ϕ h (placeOver (K₁:=K₁) (K₁':=K₁') p₁)).2,
          primeOf_spec (placeMap ϕ h (placeOver (K₁:=K₁) (K₁':=K₁') p₂)).1
            (placeMap ϕ h (placeOver (K₁:=K₁) (K₁':=K₁') p₂)).2,
          hpq']
    obtain ⟨σ, hσ⟩ := exists_smul_eq_of_comap_eq' (K₁ := K₂) (K₁' := K₂')
      (A := (placeMap ϕ h (placeOver (K₁:=K₁) (K₁':=K₁') p₁)).1)
      (B := (placeMap ϕ h (placeOver (K₁:=K₁) (K₁':=K₁') p₂)).1)
      (placeMap ϕ h (placeOver (K₁:=K₁) (K₁':=K₁') p₁)).2 hcomap
    have h4 : (⟨σ • (placeMap ϕ h (placeOver (K₁:=K₁) (K₁':=K₁') p₁)).1,
        smul_comap_ne_top (K₁:=K₂) (K₁':=K₂') σ (placeMap ϕ h (placeOver (K₁:=K₁) (K₁':=K₁') p₁)).2⟩ : FinitePlace K₂ K₂') =
        placeMap ϕ h (placeOver (K₁:=K₁) (K₁':=K₁') p₂) := Subtype.ext hσ
    have h3 : (⟨(ϕ.symm σ) • (placeOver (K₁:=K₁) (K₁':=K₁') p₁).1,
        smul_comap_ne_top (K₁:=K₁) (K₁':=K₁') (ϕ.symm σ) (placeOver (K₁:=K₁) (K₁':=K₁') p₁).2⟩ : FinitePlace K₁ K₁') =
        placeOver (K₁:=K₁) (K₁':=K₁') p₂ := by
      apply placeMap_injective (K₁:=K₁) (K₁':=K₁') ϕ h
      rw [placeMap_smul (K₁:=K₁) (K₁':=K₁') ϕ h (ϕ.symm σ) (placeOver (K₁:=K₁) (K₁':=K₁') p₁)]
      simp only [MulEquiv.apply_symm_apply]
      exact h4
    have hval : (ϕ.symm σ) • (placeOver (K₁:=K₁) (K₁':=K₁') p₁).1 = (placeOver (K₁:=K₁) (K₁':=K₁') p₂).1 :=
      congrArg Subtype.val h3
    have hp : p₁ = p₂ := by
      calc p₁ = primeOf (K₁:=K₁) (K₁':=K₁') (placeOver (K₁:=K₁) (K₁':=K₁') p₁).1 (placeOver (K₁:=K₁) (K₁':=K₁') p₁).2 :=
            (primeOf_placeOver (K₁:=K₁) (K₁':=K₁') p₁).symm
        _ = primeOf (K₁:=K₁) (K₁':=K₁') ((ϕ.symm σ) • (placeOver (K₁:=K₁) (K₁':=K₁') p₁).1)
              (smul_comap_ne_top (K₁:=K₁) (K₁':=K₁') (ϕ.symm σ) (placeOver (K₁:=K₁) (K₁':=K₁') p₁).2) :=
            (primeOf_smul (K₁:=K₁) (K₁':=K₁') (ϕ.symm σ) (placeOver (K₁:=K₁) (K₁':=K₁') p₁).1 (placeOver (K₁:=K₁) (K₁':=K₁') p₁).2).symm
        _ = primeOf (K₁:=K₁) (K₁':=K₁') (placeOver (K₁:=K₁) (K₁':=K₁') p₂).1 (placeOver (K₁:=K₁) (K₁':=K₁') p₂).2 :=
            primeOf_eq_of_comap_eq (K₁:=K₁) (K₁':=K₁')
              (smul_comap_ne_top (K₁:=K₁) (K₁':=K₁') (ϕ.symm σ) (placeOver (K₁:=K₁) (K₁':=K₁') p₁).2)
              (placeOver (K₁:=K₁) (K₁':=K₁') p₂).2 (by rw [hval])
        _ = p₂ := primeOf_placeOver (K₁:=K₁) (K₁':=K₁') p₂
    exact hp
  · intro q
    obtain ⟨A, hA⟩ := placeMap_surjective (K₁:=K₁) (K₁':=K₁') ϕ h (placeOver (K₁:=K₂) (K₁':=K₂') q)
    refine ⟨primeOf (K₁:=K₁) (K₁':=K₁') A.1 A.2, ?_⟩
    have hcomap : (placeOver (K₁:=K₁) (K₁':=K₁') (primeOf (K₁:=K₁) (K₁':=K₁') A.1 A.2)).1.comap (algebraMap K₁ K₁') =
        A.1.comap (algebraMap K₁ K₁') := by
      rw [placeOver_spec, primeOf_spec A.1 A.2]
    obtain ⟨τ, hτ⟩ := exists_smul_eq_of_comap_eq' (K₁ := K₁) (K₁' := K₁')
      (A := (placeOver (K₁:=K₁) (K₁':=K₁') (primeOf (K₁:=K₁) (K₁':=K₁') A.1 A.2)).1)
      (B := A.1)
      (placeOver (K₁:=K₁) (K₁':=K₁') (primeOf (K₁:=K₁) (K₁':=K₁') A.1 A.2)).2 hcomap
    have h3 : (⟨τ • (placeOver (K₁:=K₁) (K₁':=K₁') (primeOf (K₁:=K₁) (K₁':=K₁') A.1 A.2)).1,
        smul_comap_ne_top (K₁:=K₁) (K₁':=K₁') τ (placeOver (K₁:=K₁) (K₁':=K₁') (primeOf (K₁:=K₁) (K₁':=K₁') A.1 A.2)).2⟩ : FinitePlace K₁ K₁') = A :=
      Subtype.ext hτ
    have hpm2 := placeMap_smul (K₁:=K₁) (K₁':=K₁') ϕ h τ (placeOver (K₁:=K₁) (K₁':=K₁') (primeOf (K₁:=K₁) (K₁':=K₁') A.1 A.2))
    have hval : ϕ τ • (placeMap ϕ h (placeOver (K₁:=K₁) (K₁':=K₁') (primeOf (K₁:=K₁) (K₁':=K₁') A.1 A.2))).1 =
        (placeMap ϕ h A).1 := by
      have h1 : placeMap ϕ h (⟨τ • (placeOver (K₁:=K₁) (K₁':=K₁') (primeOf (K₁:=K₁) (K₁':=K₁') A.1 A.2)).1,
          smul_comap_ne_top (K₁:=K₁) (K₁':=K₁') τ (placeOver (K₁:=K₁) (K₁':=K₁') (primeOf (K₁:=K₁) (K₁':=K₁') A.1 A.2)).2⟩ : FinitePlace K₁ K₁') =
          placeMap ϕ h A := by rw [h3]
      exact congrArg Subtype.val (hpm2.symm.trans h1)
    have hval2 : (placeMap ϕ h A).1 = (placeOver (K₁:=K₂) (K₁':=K₂') q).1 := congrArg Subtype.val hA
    calc primeMap ϕ h (primeOf (K₁:=K₁) (K₁':=K₁') A.1 A.2)
        = primeOf (K₁:=K₂) (K₁':=K₂') (placeMap ϕ h (placeOver (K₁:=K₁) (K₁':=K₁') (primeOf (K₁:=K₁) (K₁':=K₁') A.1 A.2))).1
            (placeMap ϕ h (placeOver (K₁:=K₁) (K₁':=K₁') (primeOf (K₁:=K₁) (K₁':=K₁') A.1 A.2))).2 := rfl
        _ = primeOf (K₁:=K₂) (K₁':=K₂') (ϕ τ • (placeMap ϕ h (placeOver (K₁:=K₁) (K₁':=K₁') (primeOf (K₁:=K₁) (K₁':=K₁') A.1 A.2))).1)
              (smul_comap_ne_top (K₁:=K₂) (K₁':=K₂') (ϕ τ) (placeMap ϕ h (placeOver (K₁:=K₁) (K₁':=K₁') (primeOf (K₁:=K₁) (K₁':=K₁') A.1 A.2))).2) :=
            (primeOf_smul (K₁:=K₂) (K₁':=K₂') (ϕ τ) (placeMap ϕ h (placeOver (K₁:=K₁) (K₁':=K₁') (primeOf (K₁:=K₁) (K₁':=K₁') A.1 A.2))).1 (placeMap ϕ h (placeOver (K₁:=K₁) (K₁':=K₁') (primeOf (K₁:=K₁) (K₁':=K₁') A.1 A.2))).2).symm
        _ = primeOf (K₁:=K₂) (K₁':=K₂') (placeMap ϕ h A).1 (placeMap ϕ h A).2 :=
            primeOf_eq_of_comap_eq (K₁:=K₂) (K₁':=K₂') _ _ (by rw [hval])
        _ = primeOf (K₁:=K₂) (K₁':=K₂') (placeOver (K₁:=K₂) (K₁':=K₂') q).1 (placeOver (K₁:=K₂) (K₁':=K₂') q).2 :=
            primeOf_eq_of_comap_eq (K₁:=K₂) (K₁':=K₂') _ _ (by rw [hval2])
        _ = q := primeOf_placeOver (K₁:=K₂) (K₁':=K₂') q

end NK.NeukirchUchida
