import Mathlib
import Submission.NK.HeckeL.Zeta
import Submission.NK.HeckeL.Consequences.abelianLFunctions
import Submission.NK.Chebotarev.Corollaries

namespace NK.HeckeL.Consequences

/-- **Čebotarev produces a prime with a prescribed Frobenius outside any finite set.**

Let `L/K` be a finite Galois extension of number fields whose Galois group is abelian, `S` a finite
set of primes of `K` containing all the ramified ones, and assume that every non-trivial character
`ψ : Gal(L/K) → ℂˣ` has Artin `L`-series regular at `s = 1`.  Then for every `σ : Gal(L/K)` and
every finite set `T` of primes of `K` there is a prime `𝔭 ∉ T` whose Frobenius is `σ`.

Indeed `NK.HeckeL.Consequences.abelianLFunctions` turns the regularity hypothesis into the
analytic input `NK.Chebotarev.AbelianLFunctions`, whence Čebotarev
(`NK.Chebotarev.infinite_setOf_isFrobAtPrime_of_abelianLFunctions`) says that the set of primes
with Frobenius `σ` is infinite; an infinite set is never contained in a finite one. -/
theorem exists_prime_isFrobAtPrime_outside {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (hS : ∀ 𝔭 : NK.HeckeL.PrimeIdeal K, ¬ NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔭 → 𝔭 ∈ S)
    (h : ∀ ψ : Gal(L/K) →* ℂˣ, ψ ≠ 1 → NK.HeckeL.ArtinLRegularAtOne K L S ψ)
    (σ : Gal(L/K)) (T : Finset (NK.Chebotarev.PrimeIdeal K)) :
    ∃ 𝔭 : NK.Chebotarev.PrimeIdeal K, 𝔭 ∉ T ∧ NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) 𝔭 σ := by
  -- the Artin regularity hypothesis is the Hecke `L`-function input of Čebotarev
  have hLF : NK.Chebotarev.AbelianLFunctions K L := abelianLFunctions S hcomm hS h
  -- hence the set of primes with Frobenius `σ` is infinite
  have hinf : {𝔭 : NK.Chebotarev.PrimeIdeal K |
      NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) 𝔭 σ}.Infinite :=
    NK.Chebotarev.infinite_setOf_isFrobAtPrime_of_abelianLFunctions hcomm hLF σ
  -- an infinite set of primes cannot be contained in the finite set `T`
  by_contra hcon
  have hsub : {𝔭 : NK.Chebotarev.PrimeIdeal K |
      NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) 𝔭 σ} ⊆ (↑T : Set _) := by
    intro 𝔭 h𝔭
    by_contra h𝔭T
    exact hcon ⟨𝔭, h𝔭T, h𝔭⟩
  exact hinf (T.finite_toSet.subset hsub)

end NK.HeckeL.Consequences
