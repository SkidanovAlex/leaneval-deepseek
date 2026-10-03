/-
# `Submission.Work.FIArea7.summand_eq_hfac`

The arithmetic core of the `τ(m)⁴`-machinery of *FI* (23.11): for `k ∣ m^J` the weighted
divisor function `k^{-1/4} τ(mk)²` factors as `τ(m)² · hfac m k`, where `hfac` is the
*multiplicative* (in `k`) normalised summand of `MSmoothDefs`.

Indeed, since `k ∣ m^J` every prime of `k` divides `m`, and so, writing `a_p = v_p m`,
`b_p = v_p k`,

`τ(mk) = ∏_{p | m} (a_p + b_p + 1)`,   `k^{-1/4} = ∏_{p | m} (xp p)^{b_p}`,

while `hfac m k = ∏_{p | m} ((a_p + b_p + 1)/(a_p + 1))² (xp p)^{b_p}`.  Multiplying the
last identity by `τ(m)² = ∏_{p | m} (a_p + 1)²` exhibits both sides as one and the same
product over `m.primeFactors`.
-/
import Mathlib
import Submission.Work.FIArea7.MSmoothDefs
import Submission.Work.FIArea7.card_divisors_mul_primeFactors
import Submission.Work.FIArea7.xp_inv_eq_prod

set_option autoImplicit false

namespace Work.FIArea7

open Finset

noncomputable section

/-- For `k ∣ m^J` with `m ≥ 1`, every prime factor of `k` is a prime factor of `m`. -/
lemma primeFactors_subset_of_dvd_pow (m k J : ℕ) (hm : 1 ≤ m) (hk : k ∣ m ^ J) :
    k.primeFactors ⊆ m.primeFactors := by
  intro p hp
  obtain ⟨hpp, hpdvd, -⟩ := Nat.mem_primeFactors.mp hp
  have hm0 : m ≠ 0 := by omega
  exact Nat.mem_primeFactors.mpr ⟨hpp, hpp.dvd_of_dvd_pow (dvd_trans hpdvd hk), hm0⟩

/-- The pointwise normalisation: `(a+1)² · hterm m v (b) = (a+b+1)² · (xp p)^b`. -/
lemma sq_mul_hterm (m p i : ℕ) :
    (((m.factorization p + 1 : ℕ) : ℝ)) ^ 2 * hterm m p i
      = (((m.factorization p + i + 1 : ℕ) : ℝ)) ^ 2 * (xp p) ^ i := by
  rw [hterm]
  field_simp

/-- `k^{-1/4} · τ(mk)² = τ(m)² · hfac m k` for `1 ≤ m`, `1 ≤ k`, `k ∣ m^J`. -/
lemma summand_eq_hfac (m k J : ℕ) (hm : 1 ≤ m) (hk : k ∣ m ^ J) (hk1 : 1 ≤ k) :
    ((k : ℝ) ^ ((1 : ℝ) / 4))⁻¹ * (((m * k).divisors.card : ℕ) : ℝ) ^ 2
      = (((m.divisors.card : ℕ) : ℝ)) ^ 2 * hfac m k := by
  have hsub : k.primeFactors ⊆ m.primeFactors := primeFactors_subset_of_dvd_pow m k J hm hk
  have hm0 : m ≠ 0 := by omega
  -- `τ(mk)`, as a real product over `m.primeFactors`
  have htaumk : (((m * k).divisors.card : ℕ) : ℝ)
      = ∏ p ∈ m.primeFactors, ((m.factorization p + k.factorization p + 1 : ℕ) : ℝ) := by
    rw [card_divisors_mul_primeFactors m k hm hk1 hsub, Nat.cast_prod]
  -- `τ(m)`, as a real product over the same index set
  have htaum : (((m.divisors.card : ℕ) : ℝ))
      = ∏ p ∈ m.primeFactors, ((m.factorization p + 1 : ℕ) : ℝ) := by
    rw [Nat.card_divisors hm0, Nat.cast_prod]
  -- the common value of both sides
  have hLHS : ((k : ℝ) ^ ((1 : ℝ) / 4))⁻¹ * (((m * k).divisors.card : ℕ) : ℝ) ^ 2
      = ∏ p ∈ m.primeFactors,
          ((xp p) ^ (k.factorization p)
            * (((m.factorization p + k.factorization p + 1 : ℕ) : ℝ)) ^ 2) := by
    rw [xp_inv_eq_prod m k hm hk1 hsub, htaumk, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  have hRHS : (((m.divisors.card : ℕ) : ℝ)) ^ 2 * hfac m k
      = ∏ p ∈ m.primeFactors,
          ((xp p) ^ (k.factorization p)
            * (((m.factorization p + k.factorization p + 1 : ℕ) : ℝ)) ^ 2) := by
    rw [htaum, ← Finset.prod_pow, hfac, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [sq_mul_hterm]
    ring
  rw [hLHS, hRHS]

end

end Work.FIArea7
