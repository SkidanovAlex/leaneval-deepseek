import Mathlib
import Submission.Work.Tower.Chebotarev.Defs
import Submission.Work.Tower.Chebotarev.exists_primesOver_inertiaDeg_eq_one

namespace Work.Tower.Chebotarev

open NumberField Polynomial
open scoped Classical nonZeroDivisors NumberField

/-- If `K/ℚ` is Galois and Kummer–Dedekind gives one prime above `q` with inertia degree one,
then *every* prime of `𝓞 K` above `q` has inertia degree one, because the Galois group acts
transitively on the primes above `q` and preserves inertia degrees.

(Companion of `Work.Tower.Chebotarev.exists_primesOver_inertiaDeg_eq_one` in the same directory;
if that file is available, it gives the existence of a prime of inertia degree one.) -/
theorem forall_inertiaDeg_eq_one {K : Type} [Field K] [NumberField K] [IsGalois ℚ K] (θ : 𝓞 K)
    (q : ℕ) [Fact (Nat.Prime q)] (hp : ¬ q ∣ RingOfIntegers.exponent θ) (a : ℤ)
    (ha : (q : ℤ) ∣ (minpoly ℤ θ).eval a) :
    ∀ P : (Ideal.span {(q : ℤ)}).primesOver (𝓞 K), P.1.inertiaDeg ℤ = 1 := by
  -- Kummer–Dedekind produces one prime above `q` with inertia degree one.
  obtain ⟨P₀, hP₀⟩ := exists_primesOver_inertiaDeg_eq_one θ q hp a ha
  -- Set up the Galois group of `K/ℚ` acting on `𝓞 K`.
  have := (IsIntegralClosure.algebraMap_injective (𝓞 K) ℤ K).isDomain
  have := IsIntegralClosure.isDedekindDomain ℤ ℚ K (𝓞 K)
  have := IsIntegralClosure.isFractionRing_of_finite_extension ℤ ℚ K (𝓞 K)
  have := IsIntegralClosure.finite ℤ ℚ K (𝓞 K)
  let : MulSemiringAction Gal(K/ℚ) (𝓞 K) := IsIntegralClosure.MulSemiringAction ℤ ℚ K (𝓞 K)
  have hgal : IsGaloisGroup Gal(K/ℚ) ℤ (𝓞 K) :=
    IsGaloisGroup.of_isFractionRing Gal(K/ℚ) ℤ (𝓞 K) ℚ K
  intro P
  -- Galois transitivity: all primes above `q` have the same inertia degree.
  exact (Ideal.inertiaDeg_eq_of_isGaloisGroup (Ideal.span {(q : ℤ)}) P.1 P₀.1 Gal(K/ℚ)).trans hP₀

end Work.Tower.Chebotarev
