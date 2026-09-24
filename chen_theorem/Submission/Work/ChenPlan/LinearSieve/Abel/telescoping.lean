import Mathlib
import Submission.Work.ChenPlan.LinearSieve.basic
import Submission.Work.ChenPlan.LinearSieve.Framework

/-!
# The Abel / telescoping identity for the linear sieve

For a `BoundingSieve` `A` with `P = A.prodPrimes` and `ν = A.nu`, and any `v, Z : ℕ`,

`Σ_{v ≤ p < Z} ν p · Π_{p ≤ q < Z} (1 - ν q)⁻¹ = Π_{v ≤ q < Z} (1 - ν q)⁻¹ - 1`

(the sum and products over the primes of `P`).  This is the "Stieltjes measure" identity that turns
the Buchstab sum over primes into an integral: the jump of `Φ(w) = Π_{q ≥ w} (1 - ν q)⁻¹` at the
prime `p` is exactly `ν p · Φ(p)`.

The proof goes through the general finite telescoping identity, valid in any linear order,

`Σ_{p ∈ S} (b p - 1) · Π_{q ∈ S, p < q} b q = (Π_{q ∈ S} b q) - 1`,

applied with `b q = (1 - ν q)⁻¹` (so that `ν q · b q = b q - 1`).
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.ChenPlan.LinearSieve.Abel

/-! ## The general telescoping identity in a linear order -/

/-- **Telescoping product identity.** In a linear order, summing the "difference `b p - 1` times the
tail product" telescopes to the full product minus `1`. -/
private theorem telescope_step {α : Type*} [LinearOrder α] [DecidableEq α]
    (S : Finset α) (b : α → ℝ) :
    (∑ p ∈ S, (b p - 1) * ∏ q ∈ S.filter (fun q => p < q), b q)
      = (∏ q ∈ S, b q) - 1 := by
  classical
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have ha : a ∉ s := fun h => absurd (hlt a h) (lt_irrefl a)
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hempty : (insert a s).filter (fun q => a < q) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with hxa | hx
      · rw [hxa]; exact lt_irrefl a
      · exact not_lt.mpr (le_of_lt (hlt x hx))
    rw [hempty, Finset.prod_empty, mul_one]
    have hsum : (∑ p ∈ s, (b p - 1) * ∏ q ∈ (insert a s).filter (fun q => p < q), b q)
        = b a * ∑ p ∈ s, (b p - 1) * ∏ q ∈ s.filter (fun q => p < q), b q := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun p hp => ?_)
      rw [Finset.filter_insert, if_pos (hlt p hp)]
      rw [Finset.prod_insert (fun h => ha (Finset.mem_of_mem_filter _ h))]
      ring
    rw [hsum, ih]
    ring

/-- Splitting the "`p ≤ q`" product at `q = p`. -/
private theorem prod_filter_le_eq {α : Type*} [LinearOrder α] [DecidableEq α]
    (S : Finset α) (b : α → ℝ) {p : α} (hp : p ∈ S) :
    (∏ q ∈ S.filter (fun q => p ≤ q), b q)
      = b p * ∏ q ∈ S.filter (fun q => p < q), b q := by
  have h : S.filter (fun q => p ≤ q) = insert p (S.filter (fun q => p < q)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hqS, hpq⟩
      rcases lt_or_eq_of_le hpq with hlt | heq
      · exact Or.inr ⟨hqS, hlt⟩
      · exact Or.inl heq.symm
    · rintro (heq | ⟨hqS, hlt⟩)
      · rw [heq]; exact ⟨hp, le_refl p⟩
      · exact ⟨hqS, le_of_lt hlt⟩
  rw [h, Finset.prod_insert]
  exact fun hmem => absurd (Finset.mem_filter.mp hmem).2 (lt_irrefl p)

/-- The telescoping identity in the form used by the sieve: with `b q = (1 - c q)⁻¹`,
`c p · ∏_{q ≥ p} (1 - c q)⁻¹ = ((1 - c p)⁻¹ - 1) · ∏_{q > p} (1 - c q)⁻¹`, so the sum over `S`
telescopes.  Here `c p ≠ 1` on `S` is what makes `c p · (1 - c p)⁻¹ = (1 - c p)⁻¹ - 1`. -/
theorem telescope_le_sum {α : Type*} [LinearOrder α] [DecidableEq α]
    (S : Finset α) (c : α → ℝ) (hc : ∀ p ∈ S, c p ≠ 1) :
    (∑ p ∈ S, c p * ∏ q ∈ S.filter (fun q => p ≤ q), (1 - c q)⁻¹)
      = (∏ q ∈ S, (1 - c q)⁻¹) - 1 := by
  have key : ∀ p ∈ S, c p * ∏ q ∈ S.filter (fun q => p ≤ q), (1 - c q)⁻¹
      = ((1 - c p)⁻¹ - 1) * ∏ q ∈ S.filter (fun q => p < q), (1 - c q)⁻¹ := by
    intro p hp
    rw [prod_filter_le_eq S (fun q => (1 - c q)⁻¹) hp]
    have h1 : 1 - c p ≠ 0 := by intro h; exact hc p hp (by linarith)
    have h2 : c p * (1 - c p)⁻¹ = (1 - c p)⁻¹ - 1 := by
      field_simp
      ring
    rw [← mul_assoc, h2]
  rw [Finset.sum_congr rfl key]
  exact telescope_step S (fun q => (1 - c q)⁻¹)

/-! ## The sieve form -/

theorem telescoping (A : BoundingSieve) (v Z : ℕ) :
    (∑ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => v ≤ p ∧ p < Z),
        A.nu p * (∏ q ∈ A.prodPrimes.primeFactors.filter (fun q : ℕ => p ≤ q ∧ q < Z),
          (1 - A.nu q)⁻¹))
      = (∏ q ∈ A.prodPrimes.primeFactors.filter (fun q : ℕ => v ≤ q ∧ q < Z),
          (1 - A.nu q)⁻¹) - 1 := by
  classical
  have hc : ∀ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => v ≤ p ∧ p < Z),
      A.nu p ≠ 1 := by
    intro p hp
    have hpT : p ∈ A.prodPrimes.primeFactors := (Finset.mem_filter.mp hp).1
    have hlt := A.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hpT)
      (Nat.mem_primeFactors.mp hpT).2.1
    linarith
  have hbridge : ∀ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => v ≤ p ∧ p < Z),
      A.prodPrimes.primeFactors.filter (fun q : ℕ => p ≤ q ∧ q < Z)
        = (A.prodPrimes.primeFactors.filter (fun q : ℕ => v ≤ q ∧ q < Z)).filter
            (fun q : ℕ => p ≤ q) := by
    intro p hp
    have hvp : v ≤ p := (Finset.mem_filter.mp hp).2.1
    ext q
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hqT, hpq, hqZ⟩
      exact ⟨⟨hqT, le_trans hvp hpq, hqZ⟩, hpq⟩
    · rintro ⟨⟨hqT, -, hqZ⟩, hpq⟩
      exact ⟨hqT, hpq, hqZ⟩
  have hsum : (∑ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => v ≤ p ∧ p < Z),
        A.nu p * (∏ q ∈ A.prodPrimes.primeFactors.filter (fun q : ℕ => p ≤ q ∧ q < Z),
          (1 - A.nu q)⁻¹))
      = ∑ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => v ≤ p ∧ p < Z),
        A.nu p * (∏ q ∈ (A.prodPrimes.primeFactors.filter (fun q : ℕ => v ≤ q ∧ q < Z)).filter
          (fun q : ℕ => p ≤ q), (1 - A.nu q)⁻¹) := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hbridge p hp]
  rw [hsum]
  exact telescope_le_sum _ A.nu hc

end Work.ChenPlan.LinearSieve.Abel
