import Mathlib
import Submission.Vdw.CaseISieve
import Submission.Vdw.IndexBounded

open Polynomial
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# The exact per-discriminant Case-I bound (1/D form)

Refinements of `CaseISieve.perDiscriminant_clean_le` needed for the
Case-I summation over squarefull discriminants `D`:

1. **Empty classes**: the index of a degree-`n` polynomial is `< n`
   (`IndexBounded.indexClass_self_false`), so the counted set is EMPTY as
   soon as some prime factor `p` of `D` has `n ≤ v_p(D)`
   (`perDiscriminant_zero_of_exponent_ge`);
2. for `D` with all exponents `< n` (`v_p(D) < n` for every `p | D`), the
   capped exponent `min (v_p(D)) n` equals `v_p(D)`, and the product
   `∏_p p^{−v_p(D)}` is exactly `1/D` (by `Nat.prod_primeFactors_pow_factorization`),
   giving the clean **`O(c^{ω(D)}·H^n/D)` bound**
   (`perDiscriminant_exact_le`).

Together: for the purposes of Case I the sum over squarefull
`D > H^{2+2δ}` only ranges over exponents `< n`, where the honest `1/D`
denominator applies — this is the input to the CI-4 squarefull-tail estimate.
-/

namespace Submission.Vdw

noncomputable section

open UniqueFactorizationMonoid

/-- The per-`D` index-class set vanishes if some prime factor `p` of `D`
satisfies `n ≤ v_p(D)`: no degree-`n` polynomial has index `≥ n`. -/
theorem perDiscriminant_zero_of_exponent_ge (n H : ℕ) (hn : 1 ≤ n) (D : ℕ)
    (hpge : ∃ p ∈ D.primeFactors, n ≤ D.factorization p) :
    Nat.card {f : ↥(Box n H) // ∀ p : D.primeFactors,
        indexClass (F := ZMod (p : ℕ)) n (min (D.factorization (p : ℕ)) n)
          (boxResidue n H (p : ℕ) f)} = 0 := by
  classical
  let X := {f : ↥(Box n H) // ∀ p : D.primeFactors,
        indexClass (F := ZMod (p : ℕ)) n (min (D.factorization (p : ℕ)) n)
          (boxResidue n H (p : ℕ) f)}
  have hXempty : IsEmpty X := by
    rcases hpge with ⟨p0, hp0, hpn⟩
    refine ⟨fun x => ?_⟩
    have hp0prime : Nat.Prime p0 := (Nat.mem_primeFactors.mp hp0).1
    haveI : Fact (Nat.Prime p0) := ⟨hp0prime⟩
    have hx := (x.2 ⟨p0, hp0⟩)
    have hmin : min (D.factorization p0) n = n := Nat.min_eq_right hpn
    dsimp at hx
    rw [hmin] at hx
    exact (indexClass_self_false (F := ZMod p0) n hn (boxResidue n H p0 x.1)) hx
  haveI : IsEmpty X := hXempty
  change Nat.card X = 0
  rw [Nat.card_eq_fintype_card]
  simp

/-- `1/D = ∏_p 1/p^{v_p(D)}` (real), from the prime factorization of `D`. -/
theorem prod_inv_factorization (D : ℕ) (hD : D ≠ 0) :
    (∏ p ∈ D.primeFactors, 1 / ((p : ℕ) : ℝ) ^ D.factorization p) = 1 / (D : ℝ) := by
  classical
  have hDnat : D = ∏ p ∈ D.primeFactors, p ^ D.factorization p :=
    Nat.prod_primeFactors_pow_factorization hD
  have hD' : (D : ℝ) = ∏ p ∈ D.primeFactors, ((p : ℕ) : ℝ) ^ D.factorization p := by
    nth_rw 1 [hDnat]
    simp
  calc
    (∏ p ∈ D.primeFactors, 1 / ((p : ℕ) : ℝ) ^ D.factorization p)
        = ∏ p ∈ D.primeFactors, (((p : ℕ) : ℝ) ^ D.factorization p)⁻¹ := by
            simp [one_div]
    _ = (∏ p ∈ D.primeFactors, ((p : ℕ) : ℝ) ^ D.factorization p)⁻¹ :=
            (Finset.prod_inv_distrib (s := D.primeFactors)
              (f := fun p : ℕ => ((p : ℕ) : ℝ) ^ D.factorization p))
    _ = 1 / (D : ℝ) := by
            rw [← hD']
            simp [one_div]

/-- **Exact per-discriminant Case-I bound.**  If `C := radical D ≤ H`, every
prime exponent of `D` is `< n`, and `H ≥ 1`, then the number of degree-`n`
box polynomials whose reduction mod every `p | D` has index at least
`v_p(D)` is at most

    4^n · 2^(((n+1)^4)·ω(D)) · H^n / D

— Bhargava's `O(c^{ω(D)} H^n/D)` estimate, to be summed over squarefull
`D > H^{2+2δ}`. -/
theorem perDiscriminant_exact_le (n H : ℕ) (_hn : 1 ≤ n) (hH : 1 ≤ H) (D : ℕ)
    (hD : D ≠ 0) (hC : radical D ≤ H)
    (hsmall : ∀ p ∈ D.primeFactors, D.factorization p < n) :
    (Nat.card {f : ↥(Box n H) // ∀ p : D.primeFactors,
        indexClass (F := ZMod (p : ℕ)) n (min (D.factorization (p : ℕ)) n)
          (boxResidue n H (p : ℕ) f)} : ℝ) ≤
      (4 : ℝ) ^ n * (2 : ℝ) ^ (((n + 1) ^ 4) * (D.primeFactors).card) * (H : ℝ) ^ n / (D : ℝ) := by
  classical
  have hclean := perDiscriminant_clean_le n H (by omega) hH D hC
  have hmin : ∀ p ∈ D.primeFactors,
      min (D.factorization p) n = D.factorization p := by
    intro p hp
    exact Nat.min_eq_left (le_of_lt (hsmall p hp))
  have hprod : (∏ p ∈ D.primeFactors, 1 / ((p : ℕ) : ℝ) ^ min (D.factorization p) n) =
      1 / (D : ℝ) := by
    calc
      (∏ p ∈ D.primeFactors, 1 / ((p : ℕ) : ℝ) ^ min (D.factorization p) n)
          = ∏ p ∈ D.primeFactors, 1 / ((p : ℕ) : ℝ) ^ D.factorization p := by
              apply Finset.prod_congr rfl
              intro p hp
              rw [hmin p hp]
      _ = 1 / (D : ℝ) := prod_inv_factorization D hD
  calc
    (Nat.card {f : ↥(Box n H) // ∀ p : D.primeFactors,
        indexClass (F := ZMod (p : ℕ)) n (min (D.factorization (p : ℕ)) n)
          (boxResidue n H (p : ℕ) f)} : ℝ) ≤
        (4 : ℝ) ^ n * (2 : ℝ) ^ (((n + 1) ^ 4) * (D.primeFactors).card) * (H : ℝ) ^ n *
          (∏ p ∈ D.primeFactors, 1 / ((p : ℕ) : ℝ) ^ min (D.factorization p) n) := hclean
    _ = (4 : ℝ) ^ n * (2 : ℝ) ^ (((n + 1) ^ 4) * (D.primeFactors).card) * (H : ℝ) ^ n / (D : ℝ) := by
      rw [hprod]
      ring

