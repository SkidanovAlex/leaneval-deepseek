/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `HasKummerMachinery` from `μ_ℓ ⊆ K`, and the differentiation lemma from `μ_ℓ ⊆ K`

The Kummer machinery of §5 (`NK.UchidaKummer.HasKummerMachinery`) bundles four inputs over every
finite intermediate field `E` of `K'/K`:

1. `μ_ℓ ⊆ E`;
2. the local Kummer surjection `IsKummerSurjective E ℓ S` for every finite `S` — §5 Prop.
   `K^x/K^ell local surjection`, proved here from weak approximation
   (`Approximation/isWeakApproximation`, Neukirch II.5.7) and the openness of the `ℓ`-th power
   subgroups (`Approximation/isOpenEllPowSubgroup`);
3. a local unit at each prime of `E` which is not an `ℓ`-th power
   (`Approximation/exists_not_ellPow_unit_adicCompletion`);
4. the local Kummer dichotomy (`Kummer/localDeg_kummerField_eq_one_iff`).

Components 2–4 are now **unconditional**, so the machinery reduces to `μ_ℓ ⊆ K`: every finite
intermediate field `E` of `K'/K` contains `μ_ℓ` as soon as `K` does.  Composing with
`NK.UchidaKummer.Differentiation.isDifferentiable_of_kummerMachinery` gives the differentiation
lemma of §5 from `μ_ℓ ⊆ K` alone.
-/
import Submission.NK.UchidaKummer.Defs
import Submission.NK.UchidaKummer.Approximation.isWeakApproximation
import Submission.NK.UchidaKummer.Approximation.isOpenEllPowSubgroup
import Submission.NK.UchidaKummer.Approximation.isKummerSurjective_of_weakApproximation
import Submission.NK.UchidaKummer.Approximation.exists_not_ellPow_unit_adicCompletion
import Submission.NK.UchidaKummer.Kummer.isKummerLocalDichotomy_of_exists_isPrimitiveRoot
import Submission.NK.UchidaKummer.Differentiation.isDifferentiable_of_kummerMachinery

namespace NK.UchidaKummer

open IsDedekindDomain

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K']
  [IsSepClosure K K']

/-- **The Kummer machinery of §5 from `μ_ℓ ⊆ K`.** -/
theorem hasKummerMachinery_of_exists_isPrimitiveRoot (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hμ : ∃ ζ : K, IsPrimitiveRoot ζ ℓ) : HasKummerMachinery K K' ℓ := by
  intro E hEfin hEnum hEsep
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨ζ, hζ⟩ := hμ
    exact ⟨algebraMap K ↥E ζ,
      (hζ.map_of_injective (RingHom.injective (algebraMap K ↥E)))⟩
  · intro S
    exact Approximation.isKummerSurjective_of_weakApproximation ℓ S
      (Approximation.isWeakApproximation ↥E S) (Approximation.isOpenEllPowSubgroup ↥E ℓ hℓ)
  · intro 𝔭
    exact Approximation.exists_not_ellPow_unit_adicCompletion (K := ↥E) ℓ hℓ 𝔭
  · obtain ⟨ζ, hζ⟩ := hμ
    exact Kummer.isKummerLocalDichotomy_of_exists_isPrimitiveRoot ℓ hℓ
      ⟨algebraMap K ↥E ζ,
        (hζ.map_of_injective (RingHom.injective (algebraMap K ↥E)))⟩

/-- **The differentiation lemma of §5 from `μ_ℓ ⊆ K`.**

For a number field `K` containing a primitive `ℓ`-th root of unity, any finite list of distinct
finite primes of `K` and any prescribed exponents `a i` are realised as local degrees `ℓ ^ a i` by
a finite extension of `K` inside `K'`. -/
theorem isDifferentiable_of_exists_isPrimitiveRoot (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hμ : ∃ ζ : K, IsPrimitiveRoot ζ ℓ) : IsDifferentiable K K' ℓ :=
  Differentiation.isDifferentiable_of_kummerMachinery K K' ℓ hℓ
    (hasKummerMachinery_of_exists_isPrimitiveRoot ℓ hℓ hμ)

end NK.UchidaKummer
