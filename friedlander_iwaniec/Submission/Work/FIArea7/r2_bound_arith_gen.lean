import Mathlib
import Submission.Work.FIArea7.ACDefs

namespace Work.FIArea7

open Finset
open scoped BigOperators

-- Same content as `r2_bound_arith` but with no hypothesis on `d` at all (not squarefreeness,
-- not the congruence condition on its prime factors).  This is the form the main chain uses.
-- Hint: cancel the factor 4 and compare the two products primewise.  For a prime p ≡ 1 (mod 4)
-- with a = d.factorization p and b = s.factorization p, the left factor is
-- (d * s^2 * 2^j).factorization p + 1 = a + 2*b + 1 (use Nat.factorization_mul for the nonzero
-- factors, and the fact that p ≠ 2 excludes the 2^j part), while the right side contributes
-- 2 ^ a * (2 * b + 1) because 2 ^ (ArithmeticFunction.cardFactors d) = ∏_{q ∈ d.primeFactors} 2 ^ (d.factorization q)
-- (Mathlib: ArithmeticFunction.cardFactors is Ω, with cardFactors_apply = primeFactorsList.length
-- and cardFactors_mul).  Pointwise use a + 1 ≤ 2 ^ a.  Primes q of d with q % 4 ≠ 1 only add
-- factors ≥ 1 to the right-hand side; primes p ≡ 1 (mod 4) dividing s but not d give the same
-- factor on both sides; the left-hand product has no other factors since a prime p ≡ 1 (mod 4)
-- dividing d * s^2 * 2^j divides d or s.

/-- Pointwise arithmetic input: `a + 2b + 1 ≤ 2^a (2b + 1)`. -/
private lemma ptwise_two_pow (a b : ℕ) : a + 2 * b + 1 ≤ 2 ^ a * (2 * b + 1) := by
  have h1 : a + 1 ≤ 2 ^ a := Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := a))
  have h2 : 2 * b ≤ 2 ^ a * (2 * b) := by
    calc 2 * b = 1 * (2 * b) := by ring
      _ ≤ 2 ^ a * (2 * b) := Nat.mul_le_mul_right _ (Nat.one_le_two_pow (n := a))
  calc a + 2 * b + 1 = (a + 1) + 2 * b := by ring
    _ ≤ 2 ^ a + 2 ^ a * (2 * b) := Nat.add_le_add h1 h2
    _ = 2 ^ a * (2 * b + 1) := by ring

/-- The same inequality, in `ℝ`. -/
private lemma ptwise_two_pow_R (a b : ℕ) :
    (a : ℝ) + 2 * (b : ℝ) + 1 ≤ (2 : ℝ) ^ a * (2 * (b : ℝ) + 1) := by
  exact_mod_cast ptwise_two_pow a b

/-- The `p`-adic exponent of `d * s^2 * 2^j` at an odd prime `p` is `v_p(d) + 2 v_p(s)`. -/
private lemma factorization_mul_sq_two_pow (d s j p : ℕ) (hd : d ≠ 0) (hs : s ≠ 0)
    (hp : p.Prime) (hp2 : p ≠ 2) :
    ((d * s ^ 2 * 2 ^ j).factorization p) = d.factorization p + 2 * s.factorization p := by
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero _ hs
  have h1 : d * s ^ 2 ≠ 0 := mul_ne_zero hd hs2
  have h2 : 2 ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
  have hzero : (2 ^ j).factorization p = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hdvd
    have h2d : p ∣ 2 := hp.dvd_of_dvd_pow hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp h2d with h | h
    · exact hp.ne_one h
    · exact hp2 h
  rw [Nat.factorization_mul h1 h2, Nat.factorization_mul hd hs2]
  rw [Finsupp.add_apply, Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, hzero]
  simp

/-- `Ω n` is the sum of the exponents in the prime factorization of `n`. -/
private lemma cardFactors_eq_sum_primeFactors (d : ℕ) :
    ArithmeticFunction.cardFactors d = ∑ p ∈ d.primeFactors, d.factorization p := by
  rw [ArithmeticFunction.cardFactors_eq_sum_factorization]
  rw [Finsupp.sum_of_support_subset d.factorization
      (by rw [Nat.support_factorization]) (fun _ k => k) (by intro i hi; rfl)]

theorem r2_bound_arith_gen (d s j : ℕ) (hd : 0 < d) (hs : 0 < s) :
    4 * (∏ p ∈ (d * s ^ 2 * 2 ^ j).primeFactors.filter (fun p => p % 4 = 1),
        ((d * s ^ 2 * 2 ^ j).factorization p + 1) : ℝ)
      ≤ 4 * (2 : ℝ) ^ ArithmeticFunction.cardFactors d * Work.FIArea7.Gwt s := by
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hs0 : s ≠ 0 := ne_of_gt hs
  set M := d * s ^ 2 * 2 ^ j with hMdef
  set A := M.primeFactors.filter (fun p => p % 4 = 1) with hAdef
  have hM0 : M ≠ 0 := by
    rw [hMdef]
    exact mul_ne_zero (mul_ne_zero hd0 (pow_ne_zero _ hs0)) (pow_ne_zero _ (by norm_num))
  -- Per-prime comparison: `v_p(M) + 1 ≤ 2 ^ v_p(d) * (2 v_p(s) + 1)`.
  have hpt : ∀ p ∈ A, (M.factorization p : ℝ) + 1
      ≤ (2 : ℝ) ^ (d.factorization p) * (2 * (s.factorization p : ℝ) + 1) := by
    intro p hp
    rw [hAdef, Finset.mem_filter] at hp
    obtain ⟨hpM, hp4⟩ := hp
    obtain ⟨hpp, -, -⟩ := Nat.mem_primeFactors.mp hpM
    have hp2 : p ≠ 2 := by rintro rfl; norm_num at hp4
    have hfac : M.factorization p = d.factorization p + 2 * s.factorization p :=
      factorization_mul_sq_two_pow d s j p hd0 hs0 hpp hp2
    have hfacR : (M.factorization p : ℝ)
        = (d.factorization p : ℝ) + 2 * (s.factorization p : ℝ) := by
      rw [hfac]; push_cast; ring
    rw [hfacR]
    exact ptwise_two_pow_R (d.factorization p) (s.factorization p)
  have h1 : (∏ p ∈ A, ((M.factorization p : ℝ) + 1))
      ≤ ∏ p ∈ A, ((2 : ℝ) ^ (d.factorization p) * (2 * (s.factorization p : ℝ) + 1)) :=
    Finset.prod_le_prod₀ (fun p _ => by positivity) hpt
  have h2 : (∏ p ∈ A, ((2 : ℝ) ^ (d.factorization p) * (2 * (s.factorization p : ℝ) + 1)))
      = (∏ p ∈ A, (2 : ℝ) ^ (d.factorization p))
        * (∏ p ∈ A, (2 * (s.factorization p : ℝ) + 1)) :=
    Finset.prod_mul_distrib
  -- The first factor is bounded by `2 ^ Ω(d)`.
  have h3 : (∏ p ∈ A, (2 : ℝ) ^ (d.factorization p))
      ≤ (2 : ℝ) ^ ArithmeticFunction.cardFactors d := by
    set B := A.filter (fun p => d.factorization p ≠ 0) with hBdef
    have hBA : B ⊆ A := Finset.filter_subset _ _
    have h_eq : (∏ p ∈ A, (2 : ℝ) ^ (d.factorization p))
        = ∏ p ∈ B, (2 : ℝ) ^ (d.factorization p) := by
      rw [Finset.prod_subset hBA]
      intro x hxA hxB
      by_cases hx : d.factorization x = 0
      · rw [hx]; simp
      · exact absurd (by rw [hBdef]; exact Finset.mem_filter.mpr ⟨hxA, hx⟩) hxB
    have hBsub : B ⊆ d.primeFactors := by
      intro x hx
      rw [hBdef, Finset.mem_filter] at hx
      obtain ⟨hxA, hxne⟩ := hx
      rw [hAdef, Finset.mem_filter] at hxA
      obtain ⟨hxM, hx4⟩ := hxA
      obtain ⟨hxp, -, -⟩ := Nat.mem_primeFactors.mp hxM
      have hxdvd : x ∣ d := by
        by_contra h
        exact hxne (Nat.factorization_eq_zero_of_not_dvd h)
      rw [Nat.mem_primeFactors]
      exact ⟨hxp, hxdvd, hd0⟩
    have h_le : (∏ p ∈ B, (2 : ℝ) ^ (d.factorization p))
        ≤ ∏ p ∈ d.primeFactors, (2 : ℝ) ^ (d.factorization p) :=
      Finset.prod_le_prod_of_subset_of_one_le₀ hBsub (fun p hp => by positivity)
        (fun p hp hnp => one_le_pow₀ (by norm_num))
    have hR : (∏ p ∈ d.primeFactors, (2 : ℝ) ^ (d.factorization p))
        = (2 : ℝ) ^ ArithmeticFunction.cardFactors d := by
      rw [cardFactors_eq_sum_primeFactors, Finset.prod_pow_eq_pow_sum]
    calc (∏ p ∈ A, (2 : ℝ) ^ (d.factorization p)) = ∏ p ∈ B, (2 : ℝ) ^ (d.factorization p) := h_eq
      _ ≤ ∏ p ∈ d.primeFactors, (2 : ℝ) ^ (d.factorization p) := h_le
      _ = (2 : ℝ) ^ ArithmeticFunction.cardFactors d := hR
  -- The second factor is exactly `Gwt s`.
  have h4 : (∏ p ∈ A, (2 * (s.factorization p : ℝ) + 1)) = Gwt s := by
    have hsM : s ∣ M := ⟨d * s * 2 ^ j, by rw [hMdef]; ring⟩
    have hBM : s.primeFactors ⊆ M.primeFactors := Nat.primeFactors_mono hsM hM0
    have hAG : (∏ p ∈ A, (2 * (s.factorization p : ℝ) + 1))
        = ∏ p ∈ A, ((2 * s.factorization p + 1 : ℕ) : ℝ) := by
      apply Finset.prod_congr rfl
      intro x hx
      push_cast
      ring
    rw [hAG, Gwt]
    refine (Finset.prod_subset (Finset.filter_subset_filter (fun p => p % 4 = 1) hBM) ?_).symm
    intro x hxA hxB
    simp only [Finset.mem_filter] at hxA
    obtain ⟨hxM, hx4⟩ := hxA
    obtain ⟨hxp, -, -⟩ := Nat.mem_primeFactors.mp hxM
    have hxs : s.factorization x = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hxdvd
      exact hxB (Finset.mem_filter.mpr ⟨hxp.mem_primeFactors hxdvd hs0, hx4⟩)
    rw [hxs]; norm_num
  have h5 : (∏ p ∈ A, ((M.factorization p : ℝ) + 1))
      ≤ (2 : ℝ) ^ ArithmeticFunction.cardFactors d * Gwt s := by
    calc (∏ p ∈ A, ((M.factorization p : ℝ) + 1))
        ≤ ∏ p ∈ A, ((2 : ℝ) ^ (d.factorization p) * (2 * (s.factorization p : ℝ) + 1)) := h1
      _ = (∏ p ∈ A, (2 : ℝ) ^ (d.factorization p))
            * (∏ p ∈ A, (2 * (s.factorization p : ℝ) + 1)) := h2
      _ ≤ (2 : ℝ) ^ ArithmeticFunction.cardFactors d * Gwt s := by
        apply mul_le_mul h3 (le_of_eq h4) _ _
        · exact Finset.prod_nonneg (fun p hp => by positivity)
        · positivity
  calc 4 * (∏ p ∈ A, ((M.factorization p : ℝ) + 1))
      ≤ 4 * ((2 : ℝ) ^ ArithmeticFunction.cardFactors d * Gwt s) :=
        mul_le_mul_of_nonneg_left h5 (by norm_num)
    _ = 4 * (2 : ℝ) ^ ArithmeticFunction.cardFactors d * Gwt s := by ring

end Work.FIArea7
