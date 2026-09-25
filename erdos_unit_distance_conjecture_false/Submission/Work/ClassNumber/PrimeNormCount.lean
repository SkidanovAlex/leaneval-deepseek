import Mathlib

/-!
# The number of prime ideals of a given absolute norm is bounded by the degree

Let `K` be a number field with ring of integers `𝓞 K`, and let `k ≥ 2`. Any prime ideal `℘`
of `𝓞 K` has absolute norm a power of a rational prime, and the rational prime in question is
determined by the norm (`Ideal.exists_prime_and_absNorm_eq_pow`). Consequently all prime ideals
of a fixed absolute norm `k` lie above one and the same rational prime `p`: if `℘` has norm `k`
and `p` is the rational prime below `℘`, then `k = p ^ n` for some `n > 0`.

Distinct maximal ideals are pairwise coprime, so the Chinese remainder theorem expressed as
multiplicativity of `Ideal.absNorm` shows that the product of the elements of a finite set `Q`
of such primes divides the principal ideal `(p)`. Taking norms,

  `k ^ Q.card = absNorm (∏ ℘ ∈ Q, ℘) ∣ absNorm (span {p}) = p ^ finrank ℤ (𝓞 K)`.

Since `k = p ^ n` with `n ≥ 1`, this forces `Q.card ≤ finrank ℤ (𝓞 K) = finrank ℚ K`.
-/

namespace Work.ClassNumber

open NumberField

theorem PrimeNormCount (K : Type*) [Field K] [NumberField K] (k : ℕ) (hk : 2 ≤ k)
    (Q : Finset (Ideal (NumberField.RingOfIntegers K))) (hQ : ∀ ℘ ∈ Q, ℘.IsPrime)
    (hN : ∀ ℘ ∈ Q, Ideal.absNorm ℘ = k) :
    Q.card ≤ Module.finrank ℚ K := by
  classical
  rcases Q.eq_empty_or_nonempty with hQ0 | ⟨𝔭₀, h𝔭₀⟩
  · simp [hQ0]
  -- Elements of `Q` are prime ideals of norm `k ≥ 2`, hence nonzero, hence maximal.
  have hne : ∀ q ∈ Q, q ≠ ⊥ := by
    intro q hq hbot
    have h := hN q hq
    rw [hbot, Ideal.absNorm_bot] at h
    omega
  have hmax : ∀ q ∈ Q, q.IsMaximal := fun q hq => (hQ q hq).isMaximal (hne q hq)
  -- The absolute norm of any maximal ideal is a power of a rational prime lying in the ideal.
  have : 𝔭₀.IsMaximal := hmax 𝔭₀ h𝔭₀
  obtain ⟨p, n₀, hn₀, -, hpprime, h𝔭₀norm⟩ := Ideal.exists_prime_and_absNorm_eq_pow 𝔭₀
  have hk_eq : k = p ^ n₀ := by rw [← hN 𝔭₀ h𝔭₀, h𝔭₀norm]
  -- Every element of `Q` contains the same rational prime `p`.
  have hmem : ∀ q ∈ Q, (p : 𝓞 K) ∈ q := by
    intro q hq
    have : q.IsMaximal := hmax q hq
    obtain ⟨p', n', hn', hp'mem, hp'prime, hqnorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow q
    have hpow : p' ^ n' = p ^ n₀ := by rw [← hqnorm, ← h𝔭₀norm, hN q hq, hN 𝔭₀ h𝔭₀]
    have hdvd0 : p' ∣ p ^ n₀ := by
      rw [← hpow]
      exact dvd_pow_self p' hn'.ne'
    have hdvd : p' ∣ p := hp'prime.dvd_of_dvd_pow hdvd0
    have hpeq : p' = p := (Nat.prime_dvd_prime_iff_eq hp'prime hpprime).mp hdvd
    rwa [hpeq] at hp'mem
  -- Distinct maximal ideals are coprime, so the product of the elements of `Q` divides `(p)`.
  have hdvd : (∏ q ∈ Q, q) ∣ Ideal.span {(p : 𝓞 K)} := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro a ha b hb hab
      exact Ideal.isCoprime_iff_sup_eq.mpr
        (Ideal.IsMaximal.coprime_of_ne (hmax a ha) (hmax b hb) hab)
    · intro q hq
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact hmem q hq
  -- Taking absolute norms: `k ^ Q.card ∣ p ^ finrank ℤ (𝓞 K)`.
  have hkey : k ^ Q.card ∣ p ^ Module.finrank ℤ (𝓞 K) := by
    have h1 : Ideal.absNorm (∏ q ∈ Q, q) = k ^ Q.card := by
      rw [map_prod Ideal.absNorm (fun q => q) Q]
      rw [Finset.prod_congr rfl (fun q hq => hN q hq), Finset.prod_const]
    have h2 := map_dvd Ideal.absNorm hdvd
    rw [h1, Ideal.absNorm_span_natCast] at h2
    exact h2
  -- Conclude with `k = p ^ n₀`, `n₀ ≥ 1` and `finrank ℤ (𝓞 K) = finrank ℚ K`.
  rw [hk_eq] at hkey
  rw [← pow_mul] at hkey
  have hle : n₀ * Q.card ≤ Module.finrank ℚ K := by
    rw [← NumberField.RingOfIntegers.rank K]
    exact (Nat.pow_dvd_pow_iff_le_right hpprime.one_lt).mp hkey
  exact le_trans (Nat.le_mul_of_pos_left Q.card hn₀) hle

end Work.ClassNumber
