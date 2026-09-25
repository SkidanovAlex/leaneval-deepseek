import Mathlib
import Submission.NK.HeckeL.Zeta
import Submission.NK.HeckeL.Consequences.abelianLFunctions
import Submission.NK.Chebotarev.AbelianChebotarevOfLFunctions
import Submission.NK.Chebotarev.Density

namespace NK.HeckeL.Consequences

/-- **Čebotarev, unconditionally on the Galois group.**  Under the Hecke/Artin regularity
hypothesis the set of primes of `K` whose Frobenius is a prescribed element `σ` of the abelian
Galois group `Gal(L/K)` is infinite: it has Dirichlet density `1/|Gal(L/K)| > 0`.

The proof chains the three inputs: the analytic regularity hypothesis gives the Hecke `L`-function
input `NK.Chebotarev.AbelianLFunctions` (`abelianLFunctions`), which is the analytic form of
Čebotarev for the abelian extension (`AbelianChebotarevOfLFunctions`), and a set of primes of
positive Dirichlet density is infinite (`NK.Chebotarev.infinite_of_hasDirichletDensity_pos`). -/
theorem infinite_isFrobAtPrime {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (hS : ∀ 𝔭 : NK.HeckeL.PrimeIdeal K, ¬ NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔭 → 𝔭 ∈ S)
    (h : ∀ ψ : Gal(L/K) →* ℂˣ, ψ ≠ 1 → NK.HeckeL.ArtinLRegularAtOne K L S ψ)
    (σ : Gal(L/K)) :
    {𝔭 : NK.Chebotarev.PrimeIdeal K |
      NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) 𝔭 σ}.Infinite := by
  -- the analytic regularity hypothesis is the Hecke `L`-function input of Čebotarev
  have hLF : NK.Chebotarev.AbelianLFunctions K L := abelianLFunctions S hcomm hS h
  -- hence the Frobenius set has Dirichlet density `1/|Gal(L/K)|`
  have hd := NK.Chebotarev.AbelianChebotarevOfLFunctions (K := K) (L := L) hcomm hLF σ
  -- and a set of positive density is infinite
  refine NK.Chebotarev.infinite_of_hasDirichletDensity_pos hd ?_
  have hpos : (0 : ℝ) < (Nat.card (Gal(L/K)) : ℝ) := by
    have h0 : 0 < Nat.card (Gal(L/K)) := by
      rw [IsGalois.card_aut_eq_finrank K L]
      exact Module.finrank_pos
    exact_mod_cast h0
  exact one_div_pos.mpr hpos

end NK.HeckeL.Consequences
