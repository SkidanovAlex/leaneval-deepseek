import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.UchidaKummer.Approximation.exists_not_ellPow_unit_adicCompletion
import Submission.NK.UchidaKummer.Approximation.isKummerSurjective_of_weakApproximation
import Submission.NK.UchidaKummer.Approximation.isOpenEllPowSubgroup
import Submission.NK.UchidaKummer.Approximation.isWeakApproximation
import Submission.NK.UchidaKummer.Differentiation.isDifferentiable_of_kummerMachinery
import Submission.NK.UchidaKummer.Kummer.isKummerLocalDichotomy_of_exists_isPrimitiveRoot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

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
