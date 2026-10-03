/-
# `Submission.Work.FIArea7CF.r2count_sq_lower` — clash-free copy of `Submission.Work.FIArea7.r2count_sq_lower`

Imports redirected to the `FIArea7CF` copies; renamed: gnorm_mk_eq→cfx_gnorm_mk_eq, mem_gBox_iff→r2c_mem_gBox_iff.  The workspace contains several
incompatible declarations of `Work.FIArea7.mem_gBox_iff` (and of `norm_uniCoeff_le`,
`log_pow_le_rpow`, `gnorm_mk_eq`), so the amended area-7 assembly and the *FI* §§19–26
chain can only meet through copies.  See NOTES §63.
-/
import Mathlib
import Submission.Work.FIArea7.ACDefs
import Submission.Commons.NumberTheory.GaussianInt.two_squares_repr_count

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The Gaussian box and the pair box -/

/-- On a Gaussian integer written out in coordinates, `gnorm` is the sum of the squares of the
coordinates: `|a + bi|² = a² + b²`. -/
lemma cfx_gnorm_mk_eq (a b : ℤ) :
    Work.FIPlan.gnorm (⟨a, b⟩ : GaussianInt) = (a ^ 2 + b ^ 2).natAbs := by
  rw [Work.FIPlan.gnorm, Commons.NumberTheory.GaussianInt.norm_mk]

/-- `(a,b) ↦ a + bi` realises the box of integer pairs bijectively as a finset of Gaussian
integers, and the norm condition `a² + b² = n` is exactly `gnorm = n`. -/
lemma gnorm_mk_eq_iff {a b : ℤ} {n : ℕ} :
    Work.FIPlan.gnorm (⟨a, b⟩ : GaussianInt) = n ↔ a ^ 2 + b ^ 2 = (n : ℤ) := by
  rw [cfx_gnorm_mk_eq, Int.natAbs_eq_iff]
  constructor
  · rintro (h | h)
    · exact h
    · -- `a² + b² = -(n : ℤ)` forces `n = 0` since the left side is nonnegative
      have hnn : (0 : ℤ) ≤ a ^ 2 + b ^ 2 := by positivity
      have : (n : ℤ) = 0 := by linarith
      rw [this]; linarith
  · intro h; exact Or.inl h

/-- `Work.FIArea7.r2pair` is `targetF`: the pairs `(a,b)` with `a² + b² = n` in the box
`|a|, |b| ≤ n`.  (Definitionally equal: both are the same filtered product.) -/
lemma r2pair_eq_targetF_card (n : ℕ) :
    r2pair n = (Commons.NumberTheory.GaussianInt.targetF n).card := rfl

/-- `r2count n` counts the same pairs as `targetF n`: the box `gBox n` of Gaussian integers is
the image of the box `[-n,n]²` of integer pairs under the injection `(a,b) ↦ a + bi`, and on the
image the condition `gnorm = n` becomes `a² + b² = n`. -/
lemma r2count_eq_targetF_card (n : ℕ) :
    r2count n = (Commons.NumberTheory.GaussianInt.targetF n).card := by
  rw [r2count, Work.FIPlan.gBox, Finset.filter_image]
  rw [Finset.card_image_of_injective _ Work.FIPlan.gaussMk_injective]
  show (Finset.filter (fun q : ℤ × ℤ => Work.FIPlan.gnorm (⟨q.1, q.2⟩ : GaussianInt) = n)
      ((Finset.Icc (-(n : ℤ)) (n : ℤ)) ×ˢ (Finset.Icc (-(n : ℤ)) (n : ℤ)))).card
    = (Commons.NumberTheory.GaussianInt.targetF n).card
  congr 1
  apply Finset.filter_congr
  intro q _
  exact gnorm_mk_eq_iff

/-! ## 2. The number of associate classes of norm `s²` -/

/-- **`A (s²) = ∏_{p ∣ s, p ≡ 1 (4)} (2 v_p(s) + 1)`.**  This is
`Commons.NumberTheory.GaussianInt.A`, the number of associate classes of Gaussian integers of
norm `s²`, i.e. `r₂(s²)/4`.

Multiplicativity over the prime factorisation of `s²` reduces to the local values
`A(p^e) = e + 1` for `p ≡ 1 (4)`, `A(2^e) = 1`, `A(q^e) = [e even]` for `q ≡ 3 (4)`; since the
exponent of every prime in `s²` is even and `2 % 4 ≠ 1`, each prime except those `≡ 1 (4)`
contributes `1`, and a prime `p ≡ 1 (4)` with `p^{2v} ‖ s²` contributes `2v + 1`. -/
lemma A_sq_eq_prod (s : ℕ) (hs : 0 < s) :
    Commons.NumberTheory.GaussianInt.A (s ^ 2) =
      ∏ p ∈ s.primeFactors.filter (fun p => p % 4 = 1), (2 * s.factorization p + 1) := by
  have hs2 : s ^ 2 ≠ 0 := by positivity
  -- multiplicativity of `A` on coprime factors, including the degenerate cases
  have hmul : ∀ x y : ℕ, x.Coprime y →
      Commons.NumberTheory.GaussianInt.A (x * y)
        = Commons.NumberTheory.GaussianInt.A x * Commons.NumberTheory.GaussianInt.A y := by
    intro x y h
    rcases Nat.eq_zero_or_pos x with hx | hx
    · subst hx
      have hy : y = 1 := (Nat.coprime_zero_left y).mp h
      subst hy; simp [Commons.NumberTheory.GaussianInt.A_one]
    · rcases Nat.eq_zero_or_pos y with hy | hy
      · subst hy
        have hx1 : x = 1 := (Nat.coprime_zero_right x).mp h
        subst hx1; simp [Commons.NumberTheory.GaussianInt.A_one]
      · exact Commons.NumberTheory.GaussianInt.A_mul_of_coprime x y hx hy h
  -- the Euler product for `A (s²)`
  have hprod : Commons.NumberTheory.GaussianInt.A (s ^ 2)
      = ∏ p ∈ s.primeFactors,
          Commons.NumberTheory.GaussianInt.A (p ^ (s ^ 2).factorization p) := by
    rw [Nat.multiplicative_factorization (Commons.NumberTheory.GaussianInt.A) hmul
      Commons.NumberTheory.GaussianInt.A_one hs2]
    rw [Nat.prod_factorization_eq_prod_primeFactors]
    rw [Nat.primeFactors_pow s (by norm_num : 2 ≠ 0)]
  -- the exponent of `p` in `s²` is twice its exponent in `s`
  have hfac : ∀ p : ℕ, (s ^ 2).factorization p = 2 * s.factorization p := by
    intro p
    rw [Nat.factorization_pow]
    simp
  -- the local value at `p ^ (2 v_p(s))`
  have hval : ∀ p ∈ s.primeFactors,
      Commons.NumberTheory.GaussianInt.A (p ^ (s ^ 2).factorization p)
        = if p % 4 = 1 then 2 * s.factorization p + 1 else 1 := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    rw [hfac p, Commons.NumberTheory.GaussianInt.A_prime_pow p (2 * s.factorization p) hpp]
    by_cases h2 : p = 2
    · subst h2; norm_num
    · rw [if_neg h2]
      by_cases h41 : p % 4 = 1
      · rw [if_pos h41, if_pos h41]
      · rw [if_neg h41, if_neg h41]
        rw [if_pos (show Even (2 * s.factorization p) from ⟨s.factorization p, by ring⟩)]
  calc Commons.NumberTheory.GaussianInt.A (s ^ 2)
      = ∏ p ∈ s.primeFactors,
          Commons.NumberTheory.GaussianInt.A (p ^ (s ^ 2).factorization p) := hprod
    _ = ∏ p ∈ s.primeFactors, (if p % 4 = 1 then 2 * s.factorization p + 1 else 1) :=
        Finset.prod_congr rfl hval
    _ = ∏ p ∈ s.primeFactors.filter (fun p => p % 4 = 1), (2 * s.factorization p + 1) := by
        rw [Finset.prod_filter]

/-! ## 3. The theorem -/

-- Hint: write s = r * ∏_{p ∈ s.primeFactors.filter (fun p => p % 4 = 1)} p ^ (s.factorization p),
-- i.e. r collects the prime factors of s that are not ≡ 1 (mod 4).  For each such p use
-- Nat.Prime.sq_add_sq to get p = a^2 + b^2 and put π_p = ⟨a, b⟩ : GaussianInt, a prime element of
-- norm p (its norm is the rational prime p, hence it is irreducible).  For every family of exponents
-- (k_p, j_p) with k_p + j_p = 2 * s.factorization p the element
--   w = (∏_p π_p ^ k_p * star π_p ^ j_p) * r
-- has Work.FIPlan.gnorm w = s^2 (the norm is multiplicative: Zsqrtd.norm_mul, and gnorm of a
-- natural number is its square), and |re w|, |im w| ≤ s ≤ s^2 so w lies in the box
-- Work.FIPlan.gBox (s^2) (an easy size bound on the complex product).  Distinct exponent vectors
-- give pairwise non-equal elements and the four units act freely, so the resulting map is
-- injective: use UniqueFactorizationMonoid (an instance for ℤ[i], since it is a EuclideanDomain)
-- to see that an element of norm p is not associated to one of norm q ≠ p and that π_p is not
-- associated to star π_p.  Counting the vectors gives ∏ (2 v_p(s) + 1); multiplying by the 4 units
-- gives the claim.
/-- **The lower bound for `r₂` at a square.**  For `s > 0`,
`4 · ∏_{p ∣ s, p ≡ 1 (4)} (2 v_p(s) + 1) ≤ r2count (s²)`.

In fact equality holds: `r2count (s²) = 4 * A (s²) = 4 · ∏_{p ∣ s, p ≡ 1 (4)} (2 v_p(s) + 1)`,
by the exact representation count `targetF_card_eq_four_mul_A` together with
`A_sq_eq_prod`. -/
theorem r2count_sq_lower (s : ℕ) (hs : 0 < s) :
    4 * ∏ p ∈ s.primeFactors.filter (fun p => p % 4 = 1), (2 * s.factorization p + 1) ≤
      Work.FIArea7.r2count (s ^ 2) := by
  have h1 : r2count (s ^ 2)
      = 4 * ∏ p ∈ s.primeFactors.filter (fun p => p % 4 = 1), (2 * s.factorization p + 1) := by
    rw [r2count_eq_targetF_card,
      Commons.NumberTheory.GaussianInt.targetF_card_eq_four_mul_A (s ^ 2) (Nat.one_le_pow 2 s hs),
      A_sq_eq_prod s hs]
  exact le_of_eq h1.symm

end

end Work.FIArea7
