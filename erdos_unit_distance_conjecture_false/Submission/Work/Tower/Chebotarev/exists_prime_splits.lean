import Mathlib
import Submission.Work.Defs.Basic
import Submission.Work.Tower.Chebotarev.Defs
import Submission.Work.Tower.Chebotarev.euclid_exists_prime_dvd_eval
import Submission.Work.Tower.Chebotarev.exists_integral_primitive
import Submission.Work.Tower.Chebotarev.exists_conductor_index
import Submission.Work.Tower.Chebotarev.splits_of_isGalois

/-!
# Existence of completely split primes in a Galois number field

The main result of this file, `Work.Tower.exists_prime_splits`, is the "Chebotarev-lite" existence
theorem: in every finite Galois extension `K/ℚ` there are arbitrarily large primes outside any
prescribed finite set which split completely in `K`.

The proof is elementary and uses no analytic number theory:

* choose a primitive element `θ : 𝓞 K` (integral form of the primitive element theorem);
* the conductor of `ℤ[θ]` in `𝓞 K` is a nonzero ideal, with positive integer generator dividing
  `RingOfIntegers.exponent θ`; avoid the finitely many primes dividing the exponent, so that
  Dedekind's factorisation theorem (Kummer–Dedekind) applies;
* run Euclid's argument on the values of `minpoly ℤ θ` to find a large prime outside the bad set
  dividing some value of the minimal polynomial, i.e. having a root modulo `q`;
* avoid the primes dividing `discr K`, so that `q` is unramified;
* conclude with Kummer–Dedekind, the transitivity of the Galois action on primes above `q`, and
  the fundamental identity `∑ e·f = [K : ℚ]`.
-/

open NumberField Ideal Polynomial
open scoped Classical nonZeroDivisors NumberField

namespace Work
namespace Tower

/-- If `θ : 𝓞 K` generates `K` over `ℚ`, then its minimal polynomial over `ℤ` is nonconstant.
(In fact this holds for every algebraic integer.) -/
theorem natDegree_minpoly_pos {K : Type} [Field K] [NumberField K] (θ : 𝓞 K)
    (_h : Algebra.adjoin ℚ ({(θ : K)} : Set K) = ⊤) : 0 < (minpoly ℤ θ).natDegree :=
  minpoly.natDegree_pos θ.isIntegral

/-- **The elementary split-prime theorem.** For every finite Galois extension `K/ℚ`, every finite
set `B` of natural numbers and every bound `n`, there is a prime `q > n`, `q ∉ B`, which splits
completely in `K`. -/
theorem exists_prime_splits (K : Type) [Field K] [NumberField K] [IsGalois ℚ K]
    (B : Finset ℕ) (n : ℕ) :
    ∃ q : ℕ, Nat.Prime q ∧ n < q ∧ q ∉ B ∧ Splits q K := by
  obtain ⟨θ, hθ⟩ := Chebotarev.exists_integral_primitive K
  obtain ⟨N, hNpos, _hNmem, hNdiv⟩ := Chebotarev.exists_conductor_index θ hθ
  let S : Finset ℕ := B ∪ {2} ∪ N.primeFactors ∪ (NumberField.discr K).natAbs.primeFactors
  obtain ⟨q, hq, hqn, hqS, a, ha⟩ :=
    Chebotarev.euclid_exists_prime_dvd_eval (minpoly ℤ θ) (natDegree_minpoly_pos θ hθ) S n
  refine ⟨q, hq, hqn, ?_, ?_⟩
  · intro hqB
    exact hqS (by simp only [S, Finset.mem_union, Finset.mem_singleton]; tauto)
  · refine Chebotarev.splits_of_isGalois θ q hq ?_ ?_ a ha
    · intro hdvd
      have hdvdN : q ∣ N := dvd_trans hdvd hNdiv
      exact hqS (by
        simp only [S, Finset.mem_union, Finset.mem_singleton]
        exact Or.inl (Or.inr (Nat.Prime.mem_primeFactors hq hdvdN hNpos.ne')))
    · intro hdvd
      have hnat : q ∣ (NumberField.discr K).natAbs := by
        have h' : (q : ℤ) ∣ ((NumberField.discr K).natAbs : ℤ) := Int.dvd_natAbs.mpr hdvd
        exact Int.natCast_dvd_natCast.mp h'
      exact hqS (by
        simp only [S, Finset.mem_union, Finset.mem_singleton]
        exact Or.inr (Nat.Prime.mem_primeFactors hq hnat
          (Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero K))))

end Tower
end Work
