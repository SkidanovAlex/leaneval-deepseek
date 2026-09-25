/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Neukirch's criterion with `μ_p`-coefficients: the "if" direction

This is the corrected form of `NK.BrauerHasse.exists_decompositionGroup_of_localGalois`: the same
criterion, but with the coefficient module `μ_p = Z/p(1)` (the `p`-th roots of unity) instead of
the trivial module `Z/p`.  The statement is

> a closed, self-normalising subgroup `H ≤ G_K` isomorphic to the absolute Galois group of a
> `p`-adic field `κ` is the decomposition group of a place of `K̄` over a finite prime of `K`

(Neukirch, *Kennzeichnung der `p`-adischen und der endlich algebraischen Zahlkörper*, Invent. Math.
**6** (1969), Theorem 1; Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, (12.1.9), "if"
direction.)

The difference with the sibling area is *only* the coefficient module: with trivial coefficients
the local input `H²(G_κ, Z/p) ≅ Z/p` is false whenever `μ_p ⊄ κ` (local Tate duality gives
`H²(G_κ, Z/p) ≅ Hom(μ_p(κ), Q/Z)`), so the (a)-chain of the endgame could not be instantiated; with
the cyclotomic twist the local input is the classical Kummer/Brauer computation
`H²(G_κ, μ_p) = Br(κ)[p] ≅ Z/p`, which holds unconditionally.  See the module docstring of
`Basic.lean`.

## The inputs

* `NK.BrauerTwist.LocalH2Input` — the local Brauer group (`Br(κ)[p] ≅ Z/p`);
* `NK.BrauerTwist.Sha2Vanishing` — Hasse–Brauer–Noether in `μ_p`-coefficients and its limit form;
* `NK.BrauerTwist.LocalDecompositionCriterion` — Neukirch's local finishing step.

The step from the first two to "some local component is non-zero" is *proved*
(`NK.BrauerTwist.exists_loc_ne_zero`).
-/

import Submission.NK.BrauerTwist.Hasse
import Submission.NK.BrauerHasse.exists_heightOneSpectrum_eq_comap
import Mathlib.NumberTheory.NumberField.Basic

set_option autoImplicit false

open CategoryTheory
open scoped Pointwise

universe u

namespace NK.BrauerTwist

variable {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
variable {κ κ' : Type u} [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-- **Neukirch's characterisation of decomposition groups, "if" direction, with `μ_p`-coefficients
(CoNF XII (12.1.9)).**

A closed subgroup `H ≤ G_K = Gal(K̄/K)` of the absolute Galois group of a number field `K` which is
self-normalising and isomorphic to the absolute Galois group `Gal(κ̄/κ)` of a `p`-adic field `κ` is
the decomposition group of a place of `K̄` over a finite prime of `K`.

This is the coefficient-correct form of `NK.BrauerHasse.exists_decompositionGroup_of_localGalois`:
the three inputs are the same three classical inputs, but with `μ_p`-coefficients, and they are the
ones that are true for every `p`-adic `κ`. -/
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
  obtain ⟨𝔭, h𝔭⟩ := NK.BrauerHasse.exists_heightOneSpectrum_eq_comap (K := K) (K' := K') A hA
  exact ⟨𝔭, A, h𝔭, hstab⟩

end NK.BrauerTwist
