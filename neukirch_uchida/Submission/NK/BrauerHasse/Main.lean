/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Neukirch's characterisation of decomposition groups: the "if" direction

This is the consequence that the Neukirch–Uchida development consumes: a closed subgroup
`H ≤ G_K` of the absolute Galois group of a number field `K` which

* is **self-normalising** (`Subgroup.normalizer H = H`), and
* is **isomorphic to the absolute Galois group of a `p`-adic field** `κ` (`H ≅ Gal(κ̄/κ)`),

is the decomposition group of a place of `K̄` over a finite prime of `K`
(Neukirch, *Kennzeichnung der p-adischen und der endlich algebraischen Zahlkörper*,
Invent. Math. **6** (1969), Theorem 1; Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*,
Theorem (12.1.9), "if" direction; Ivanov, arXiv:1309.2801, Theorem 4.2).

## The shape of the argument

Neukirch's argument, in the form implemented here, is:

1. `H ≅ Gal(κ̄/κ)` gives a non-zero class `x ∈ H²(H, Z/p)` — this is the local input
   `NK.BrauerHasse.LocalH2Input` (`Br(κ)[p] ≅ Z/p`).
2. The localisation map `H²(H, Z/p) → ∏_A H²(H ∩ D_A, Z/p)` (over the places `A` of `K̄` above the
   finite primes of `K`) has trivial kernel — the *vanishing of the limiting Sha²*
   `NK.BrauerHasse.Sha2Vanishing`, which is Hasse–Brauer–Noether in `Z/p`-coefficients plus its
   passage to the direct limit over the open subgroups containing `H`.  Hence `x` has a non-zero
   local component at some place `A`; this step is *proved* here as
   `NK.BrauerHasse.exists_loc_ne_zero`.
3. A non-zero local component at a place forces `H` to be that place's decomposition group — the
   local finishing step `NK.BrauerHasse.LocalDecompositionCriterion`.  In Neukirch's argument
   this is where the prime is shown to be "indecomposed" (so that `H` is contained in its
   decomposition group) and where Neukirch's Korollar 1 — an injection of the absolute Galois
   groups of two `p`-adic fields forces the fields to be isomorphic, so that the inclusion
   `H ⊆ D_A` is an isomorphism — is used, together with `N(H) = H`.

## What is assumed and what would discharge it

`LocalH2Input`, `Sha2Vanishing` and `LocalDecompositionCriterion` are the three named inputs (see
their docstrings).  `Sha2Vanishing` would be discharged by global class field theory: for a
number field `F`, `Br(F) → ∏_v Br(F_v)` is injective (Hasse–Brauer–Noether) in `Z/p`-coefficients,
and the localisation maps are compatible with inflation, so passing to the direct limit over the
finite levels inside `K̄^H` gives the stated vanishing (CoNF XII §12.1; the `Submission/Work/GlobalCFT/`
subproject is building the idèle class group that this would rest on).  `LocalH2Input` is local
class field theory (`Br(κ)[p] ≅ Z/p`); `LocalDecompositionCriterion` is the local half of
Neukirch's Theorem 1 (CoNF (12.1.9)).
-/

import Submission.NK.BrauerHasse.Hasse
import Submission.NK.BrauerHasse.exists_heightOneSpectrum_eq_comap
import Mathlib.NumberTheory.NumberField.Basic

set_option autoImplicit false

open CategoryTheory
open scoped Pointwise

universe u

namespace NK.BrauerHasse

variable {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
variable {κ κ' : Type u} [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-- **Neukirch's characterisation of decomposition groups, "if" direction (CoNF XII (12.1.9)).**

A closed subgroup `H ≤ G_K = Gal(K̄/K)` of the absolute Galois group of a number field `K` which is
self-normalising and isomorphic to the absolute Galois group `Gal(κ̄/κ)` of a `p`-adic field `κ` is
the decomposition group of a place of `K̄` over a finite prime of `K`.

The three inputs are `LocalH2Input` (the local Brauer group `H²(G_κ, Z/p) ≅ Z/p`),
`Sha2Vanishing` (Hasse–Brauer–Noether and its limit form) and `LocalDecompositionCriterion`
(the local finishing step of Neukirch's argument); see the module docstring. -/
theorem exists_decompositionGroup_of_localGalois
    (p : ℕ) (hp : p.Prime)
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hN : Subgroup.normalizer H = H)
    (hκ : Nonempty (H ≃* Gal(κ'/κ)))
    (hLoc : LocalH2Input p K K' κ κ')
    (hHasse : Sha2Vanishing p K K' κ κ')
    (hStep : LocalDecompositionCriterion p K K' κ κ') :
    ∃ A : ValuationSubring K', A.comap (algebraMap K K') ≠ ⊤ ∧
      MulAction.stabilizer Gal(K'/K) A = H := by
  obtain ⟨x, hx⟩ := hLoc H hH hκ
  obtain ⟨A, hA⟩ := exists_loc_ne_zero (K := K) (K' := K') p hHasse H hH hκ hx
  obtain ⟨A', hA'ne, hA'⟩ := hStep H hH hN hκ A x hA
  exact ⟨A', hA'ne, hA'⟩

/-- The same statement in the `FinitePlace` vocabulary of `Submission.NeukirchUchida.PlaceSystem`:
the subgroup is the decomposition group of a **finite place** of `K'`. -/
theorem exists_finitePlace_of_localGalois
    (p : ℕ) (hp : p.Prime)
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hN : Subgroup.normalizer H = H)
    (hκ : Nonempty (H ≃* Gal(κ'/κ)))
    (hLoc : LocalH2Input p K K' κ κ')
    (hHasse : Sha2Vanishing p K K' κ κ')
    (hStep : LocalDecompositionCriterion p K K' κ κ') :
    ∃ A : {A : ValuationSubring K' // A.comap (algebraMap K K') ≠ ⊤},
      MulAction.stabilizer Gal(K'/K) A.1 = H := by
  obtain ⟨A, hA, hstab⟩ :=
    exists_decompositionGroup_of_localGalois (K := K) (K' := K') (κ := κ) (κ' := κ')
      p hp H hH hN hκ hLoc hHasse hStep
  exact ⟨⟨A, hA⟩, hstab⟩

/-- **The same statement with the place parameterised by a finite prime of `K`.**  Any place of
`K'` over a finite prime of `K` restricts to `𝒪_𝔭` for a unique finite prime `𝔭` of `K`, so the
conclusion of `exists_decompositionGroup_of_localGalois` can be stated with `𝔭` explicit:
`H` is the decomposition group of a place over the finite prime `𝔭`. -/
theorem exists_prime_decompositionGroup_of_localGalois
    (p : ℕ) (hp : p.Prime)
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hN : Subgroup.normalizer H = H)
    (hκ : Nonempty (H ≃* Gal(κ'/κ)))
    (hLoc : LocalH2Input p K K' κ κ')
    (hHasse : Sha2Vanishing p K K' κ κ')
    (hStep : LocalDecompositionCriterion p K K' κ κ') :
    ∃ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
      (A : ValuationSubring K'),
      A.comap (algebraMap K K') =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭 ∧
      MulAction.stabilizer Gal(K'/K) A = H := by
  obtain ⟨A, hA, hstab⟩ :=
    exists_decompositionGroup_of_localGalois (K := K) (K' := K') (κ := κ) (κ' := κ')
      p hp H hH hN hκ hLoc hHasse hStep
  obtain ⟨𝔭, h𝔭⟩ := exists_heightOneSpectrum_eq_comap (K := K) (K' := K') A hA
  exact ⟨𝔭, A, h𝔭, hstab⟩

end NK.BrauerHasse
