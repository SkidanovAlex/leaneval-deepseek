import Mathlib
import Submission.Work.Tower.Chebotarev.Defs

set_option linter.style.haveILetI false

namespace Work.Tower.Chebotarev

open NumberField
open scoped Classical nonZeroDivisors NumberField

/-- If `K/ℚ` is Galois and every prime of `𝓞 K` above `q` is unramified with residue field
`𝔽_q`, then the number of such primes equals the degree `[K : ℚ]`. -/
theorem card_primesOver_eq_finrank {K : Type} [Field K] [NumberField K] [IsGalois ℚ K] (q : ℕ)
    [Fact (Nat.Prime q)]
    (h1 : ∀ P : (Ideal.span {(q : ℤ)}).primesOver (𝓞 K), P.1.ramificationIdx ℤ = 1)
    (h2 : ∀ P : (Ideal.span {(q : ℤ)}).primesOver (𝓞 K), P.1.inertiaDeg ℤ = 1) :
    Nat.card ((Ideal.span {(q : ℤ)}).primesOver (𝓞 K)) = Module.finrank ℚ K := by
  classical
  -- `q` is a prime element of `ℤ`
  have hq : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  -- the ideal `(q) ⊆ ℤ` is prime (hence maximal, `ℤ` having dimension ≤ 1)
  haveI hprime : (Ideal.span {(q : ℤ)} : Ideal ℤ).IsPrime :=
    (Ideal.span_singleton_prime hq.ne_zero).mpr hq
  have hp0 : (Ideal.span {(q : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hq.ne_zero
  haveI hmax : (Ideal.span {(q : ℤ)} : Ideal ℤ).IsMaximal := hprime.isMaximal hp0
  -- there are finitely many primes of `𝓞 K` above `(q)`
  haveI hfin : Fintype ((Ideal.span {(q : ℤ)}).primesOver (𝓞 K)) :=
    (Algebra.QuasiFinite.finite_primesOver (Ideal.span {(q : ℤ)})).fintype
  -- the fundamental identity of ramification theory
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(q : ℤ)}) (𝓞 K)
  calc Nat.card ((Ideal.span {(q : ℤ)}).primesOver (𝓞 K))
      = Fintype.card ((Ideal.span {(q : ℤ)}).primesOver (𝓞 K)) := Nat.card_eq_fintype_card
    _ = ∑ _ : (Ideal.span {(q : ℤ)}).primesOver (𝓞 K), (1 : ℕ) := by simp
    _ = ∑ x : (Ideal.span {(q : ℤ)}).primesOver (𝓞 K),
          x.1.ramificationIdx ℤ * x.1.inertiaDeg ℤ :=
        (Finset.sum_congr rfl (fun x _ => by rw [h1 x, h2 x, mul_one])).symm
    _ = Module.finrank ℤ (𝓞 K) := hsum
    _ = Module.finrank ℚ K := NumberField.RingOfIntegers.rank K

end Work.Tower.Chebotarev
