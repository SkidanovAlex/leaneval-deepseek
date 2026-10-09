import Submission.NeukirchUchida.PlaceSystem
import Submission.Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime
import Submission.Commons.NumberTheory.NumberField.ringOfIntegers_le_of_ne_top
import Submission.Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
import Submission.Commons.NumberTheory.NumberField.Valuation.centralizer_stabilizer_valuationSubring_sepClosure
import Submission.Commons.FieldTheory.Galois.exists_smul_eq_of_comap_eq
import Submission.Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local correspondence at the boundary: the induced map on primes

CoNF XII §12.2 starts from the *local correspondence*: an isomorphism `ϕ` of absolute Galois groups
which maps decomposition groups to decomposition groups induces a bijection of the primes of the two
number fields, and (with the local structure theory) this bijection respects the residue
characteristic and the absolute degree of the primes.

This file formalises the group-theoretic part, using only the input
`PreservesDecompositionGroups ϕ` of `Reduction.lean` together with rigidity of places:

* `primeOf A hA` — the prime of `K₁` below a place `A` of `K₁'`;
* `primeMap ϕ h` — the induced map `𝔭 ↦` the prime below `placeMap ϕ h A_𝔭`;
* `primeOf_placeMap` — **coherence**: for *any* place `A` over `𝔭`, the prime below
  `placeMap ϕ h A` is `primeMap ϕ h 𝔭` (here Galois-equivariance `placeMap_smul` and transitivity of
  the action on the places over a fixed prime are used).
-/

namespace Submission.NeukirchUchida

open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The prime of `K` below a place of `K'`.** -/
noncomputable def primeOf (A : ValuationSubring K₁')
    (hA : A.comap (algebraMap K₁ K₁') ≠ ⊤) :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁) :=
  (Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime
    (A.comap (algebraMap K₁ K₁')) hA
    (Commons.NumberTheory.NumberField.ringOfIntegers_le_of_ne_top _ hA)).choose

/-- The defining property of `primeOf`. -/
theorem primeOf_spec (A : ValuationSubring K₁')
    (hA : A.comap (algebraMap K₁ K₁') ≠ ⊤) :
    A.comap (algebraMap K₁ K₁') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₁ (primeOf A hA) :=
  (Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime
    (A.comap (algebraMap K₁ K₁')) hA
    (Commons.NumberTheory.NumberField.ringOfIntegers_le_of_ne_top _ hA)).choose_spec

/-- `primeOf` depends only on the trace of the place on `K₁`. -/
theorem primeOf_eq_of_comap_eq {A B : ValuationSubring K₁'}
    (hA : A.comap (algebraMap K₁ K₁') ≠ ⊤) (hB : B.comap (algebraMap K₁ K₁') ≠ ⊤)
    (h : A.comap (algebraMap K₁ K₁') = B.comap (algebraMap K₁ K₁')) :
    primeOf A hA = primeOf B hB :=
  Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
    (by rw [← primeOf_spec A hA, ← primeOf_spec B hB, h])

/-- Two places over the same prime differ by an element of the Galois group. -/
theorem exists_smul_eq_of_comap_eq' {A B : ValuationSubring K₁'}
    (hA : A.comap (algebraMap K₁ K₁') ≠ ⊤)
    (h : A.comap (algebraMap K₁ K₁') = B.comap (algebraMap K₁ K₁')) :
    ∃ σ : Gal(K₁'/K₁), σ • A = B :=
  Commons.FieldTheory.Galois.exists_smul_eq_of_comap_eq (F := K₁) (K' := K₁') A B hA h

/-- **A place over a given prime of `K₁`.** -/
noncomputable def placeOver (p : IsDedekindDomain.HeightOneSpectrum
    (NumberField.RingOfIntegers K₁)) : FinitePlace K₁ K₁' :=
  ⟨(Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime
      (K := K₁) (K' := K₁') p).choose,
    by
      rw [(Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime
        (K := K₁) (K' := K₁') p).choose_spec]
      exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top p⟩

/-- The defining property of `placeOver`. -/
theorem placeOver_spec (p : IsDedekindDomain.HeightOneSpectrum
    (NumberField.RingOfIntegers K₁)) :
    (placeOver (K₁ := K₁) (K₁' := K₁') p).1.comap (algebraMap K₁ K₁') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₁ p :=
  (Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime
    (K := K₁) (K' := K₁') p).choose_spec

variable {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}

/-- The prime below a place is invariant under the Galois action (it is the trace of the place on
the base field). -/
theorem primeOf_smul (σ : Gal(K₁'/K₁)) (A : ValuationSubring K₁')
    (hA : A.comap (algebraMap K₁ K₁') ≠ ⊤) :
    primeOf (σ • A) (smul_comap_ne_top σ hA) = primeOf A hA :=
  primeOf_eq_of_comap_eq (smul_comap_ne_top σ hA) hA
    (Commons.NumberTheory.NumberField.Valuation.comap_smul_algebraMap A σ)

/-- **The local correspondence at the boundary: the induced map on primes.** -/
noncomputable def primeMap (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (h : PreservesDecompositionGroups ϕ)
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)) :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂) :=
  primeOf (K₁ := K₂) (K₁' := K₂')
    (placeMap (K₁ := K₁) (K₁' := K₁') ϕ h (placeOver (K₁ := K₁) (K₁' := K₁') p)).1
    (placeMap (K₁ := K₁) (K₁' := K₁') ϕ h (placeOver (K₁ := K₁) (K₁' := K₁') p)).2

/-- **Coherence of the local correspondence**: the prime below the image of a place over `𝔭` is
`primeMap ϕ h 𝔭`, independently of the chosen place. -/
theorem primeOf_placeMap (h : PreservesDecompositionGroups ϕ) (A : FinitePlace K₁ K₁') :
    primeOf (K₁ := K₂) (K₁' := K₂') (placeMap (K₁ := K₁) (K₁' := K₁') ϕ h A).1
        (placeMap (K₁ := K₁) (K₁' := K₁') ϕ h A).2 =
      primeMap ϕ h (primeOf (K₁ := K₁) (K₁' := K₁') A.1 A.2) := by
  set p₀ := primeOf (K₁ := K₁) (K₁' := K₁') A.1 A.2 with hp₀
  -- the two places lie over the same prime, hence are conjugate
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_comap_eq'
    (K₁ := K₁) (K₁' := K₁')
    (A := (placeOver (K₁ := K₁) (K₁' := K₁') p₀).1) (B := A.1)
    (placeOver (K₁ := K₁) (K₁' := K₁') p₀).2
    (by rw [placeOver_spec p₀, primeOf_spec A.1 A.2])
  have hsub : (⟨σ • (placeOver (K₁ := K₁) (K₁' := K₁') p₀).1,
      smul_comap_ne_top (K₁ := K₁) (K₁' := K₁') σ
        (placeOver (K₁ := K₁) (K₁' := K₁') p₀).2⟩ : FinitePlace K₁ K₁') = A :=
    Subtype.ext hσ
  have hpm : placeMap (K₁ := K₁) (K₁' := K₁') ϕ h A =
      ⟨ϕ σ • (placeMap (K₁ := K₁) (K₁' := K₁') ϕ h
          (placeOver (K₁ := K₁) (K₁' := K₁') p₀)).1,
        smul_comap_ne_top (K₁ := K₂) (K₁' := K₂') (ϕ σ)
          (placeMap (K₁ := K₁) (K₁' := K₁') ϕ h
            (placeOver (K₁ := K₁) (K₁' := K₁') p₀)).2⟩ := by
    rw [← hsub, placeMap_smul]
  refine primeOf_eq_of_comap_eq (K₁ := K₂) (K₁' := K₂')
    (placeMap (K₁ := K₁) (K₁' := K₁') ϕ h A).2
    (placeMap (K₁ := K₁) (K₁' := K₁') ϕ h
      (placeOver (K₁ := K₁) (K₁' := K₁') p₀)).2 ?_
  rw [congrArg (fun x : FinitePlace K₂ K₂' => x.1.comap (algebraMap K₂ K₂')) hpm]
  exact Commons.NumberTheory.NumberField.Valuation.comap_smul_algebraMap
    (K := K₂) (K' := K₂') _ (ϕ σ)

-- The final statement that `primeMap` is a *bijection* is proved in
-- `Submission/Work/NeukirchUchida/primeMap_bijective.lean`
-- (`NK.NeukirchUchida.primeMap_bijective`); it is not imported here to avoid an import cycle
-- with the API module of the delegated lemma.

end Submission.NeukirchUchida
