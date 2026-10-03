/-
# `Submission.Work.FIArea7.MSmoothDefs`

Vocabulary for the `τ(m)⁴`-arithmetic of *FI* (23.11) (lemma
`Work.FIArea7.msmooth_sum_bound`).

For `k | m^J` every prime of `k` divides `m`, and one has the exact factorisation

`k^{-1/4} τ(mk)² = τ(m)² · ∏_{p | m} ((a_p + v_p k + 1)/(a_p + 1))² · (p^{-1/4})^{v_p k}`,   `a_p = v_p m`,

and the product on the right is *multiplicative* in `k`, whereas `k ↦ k^{-1/4}τ(mk)²` is not.
The normalised per-prime term is `hterm`, the normalised summand is `hfac` and its divisor sum is
`Hsum`; this is the object to which the Euler-product / `Nat.multiplicative_factorization`
machinery applies.  `kconst` collects the per-prime constants (`34` for the small primes `p ≤ 23`,
`1` for all `p ≥ 29`).
-/
import Mathlib

set_option autoImplicit false

namespace Work.FIArea7

open Finset

noncomputable section

/-- `xp p = p^{-1/4}`, the weight of the prime `p`. -/
def xp (p : ℕ) : ℝ := ((p : ℝ) ^ ((1 : ℝ) / 4))⁻¹

/-- The normalised per-prime term: for `a = v_p m`, `i = v_p k`, the factor of
`τ(m)⁻² · k^{-1/4} τ(mk)²` coming from `p`. -/
def hterm (m p i : ℕ) : ℝ :=
  (((m.factorization p + i + 1 : ℕ) : ℝ) / ((m.factorization p + 1 : ℕ) : ℝ)) ^ 2 * (xp p) ^ i

/-- The normalised summand `τ(m)⁻² · k^{-1/4} τ(mk)²` (for `k | m^J`). -/
def hfac (m k : ℕ) : ℝ := ∏ p ∈ m.primeFactors, hterm m p (k.factorization p)

/-- The divisor sum of the normalised summand. -/
def Hsum (m n : ℕ) : ℝ := ∑ d ∈ n.divisors, hfac m d

/-- Per-prime constants. -/
def kconst (p : ℕ) : ℝ := if p ≤ 23 then 34 else 1

@[simp] lemma hterm_zero (m p : ℕ) : hterm m p 0 = 1 := by
  rw [hterm, Nat.add_zero, pow_zero, mul_one,
    div_self (by positivity : (((m.factorization p + 1 : ℕ) : ℝ)) ≠ 0), one_pow]

@[simp] lemma hfac_zero (m : ℕ) : hfac m 0 = 1 := by
  simp [hfac]

lemma hfac_one (m : ℕ) : hfac m 1 = 1 := by
  simp [hfac]

lemma Hsum_one (m : ℕ) : Hsum m 1 = 1 := by
  simp [Hsum, hfac_one]

lemma xp_nonneg (p : ℕ) : 0 ≤ xp p := by
  rw [xp]; positivity

lemma xp_pos (p : ℕ) (hp : p ≠ 0) : 0 < xp p := by
  rw [xp]; apply inv_pos.mpr
  exact Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hp) _

end

end Work.FIArea7
