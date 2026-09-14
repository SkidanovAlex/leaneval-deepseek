import Mathlib

namespace Commons.Data.Nat

/-- The exponent of the square part in the splitting `2*x + 3*y = e`:
for even `e` it is `e/2`; for odd `e` it is `(e-3)/2`. -/
private def sqPart (e : ℕ) : ℕ := if Even e then e / 2 else (e - 3) / 2

/-- The exponent of the cube part in the splitting `2*x + 3*y = e`:
it is `0` for even `e` and `1` for odd `e`. -/
private def cubePart (e : ℕ) : ℕ := if Even e then 0 else 1

/-- Every exponent `e ≥ 2` is a nonnegative combination `2*x + 3*y`. -/
private lemma exp_split (e : ℕ) (he : 2 ≤ e) :
    2 * sqPart e + 3 * cubePart e = e := by
  rcases Nat.even_or_odd e with hev | hod
  · rw [sqPart, cubePart, if_pos hev, if_pos hev]
    have h := Nat.two_mul_div_two_of_even hev
    omega
  · have hnot : ¬ Even e := Nat.not_even_iff_odd.mpr hod
    rw [sqPart, cubePart, if_neg hnot, if_neg hnot]
    have heven : Even (e - 3) := Nat.Odd.sub_odd hod (by norm_num : Odd 3)
    have hdiv := Nat.two_mul_div_two_of_even heven
    have h3 : 3 ≤ e := by
      rcases hod with ⟨k, hk⟩
      omega
    omega

/-- **Charactersation of numbers of the form `a ^ 2 * b ^ 3` (powerful numbers).**
If every prime dividing `N` has its square dividing `N` (equivalently, every prime
exponent in `N` is at least `2`), then `N` can be written as `a ^ 2 * b ^ 3`.

Indeed, for a prime `p` with exponent `e = N.factorization p ≥ 2`, distribute the
exponent as `e = 2 * sqPart e + 3 * cubePart e`. -/
theorem exists_sq_mul_cube (N : ℕ) (hN : N ≠ 0)
    (h : ∀ p : ℕ, Nat.Prime p → p ∣ N → p ^ 2 ∣ N) :
    ∃ a b : ℕ, a ^ 2 * b ^ 3 = N := by
  classical
  refine ⟨∏ p ∈ N.primeFactors, p ^ sqPart (N.factorization p),
          ∏ p ∈ N.primeFactors, p ^ cubePart (N.factorization p), ?_⟩
  have h2 : ∀ p ∈ N.primeFactors, 2 ≤ N.factorization p := by
    intro p hp
    have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hp2 : p ^ 2 ∣ N := h p hpp (Nat.dvd_of_mem_primeFactors hp)
    exact (hpp.pow_dvd_iff_le_factorization hN).mp hp2
  have hA : (∏ p ∈ N.primeFactors, p ^ sqPart (N.factorization p)) ^ 2
      = ∏ p ∈ N.primeFactors, p ^ (2 * sqPart (N.factorization p)) := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl (fun p _ => by rw [← pow_mul, Nat.mul_comm])
  have hB : (∏ p ∈ N.primeFactors, p ^ cubePart (N.factorization p)) ^ 3
      = ∏ p ∈ N.primeFactors, p ^ (3 * cubePart (N.factorization p)) := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl (fun p _ => by rw [← pow_mul, Nat.mul_comm])
  have hkey : (∏ p ∈ N.primeFactors, p ^ (2 * sqPart (N.factorization p)))
      * (∏ p ∈ N.primeFactors, p ^ (3 * cubePart (N.factorization p)))
      = ∏ p ∈ N.primeFactors, p ^ (N.factorization p) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun p hp => by
      rw [← pow_add]; congr 1; exact exp_split (N.factorization p) (h2 p hp))
  rw [hA, hB, hkey, ← Nat.prod_primeFactors_pow_factorization hN]

end Commons.Data.Nat
