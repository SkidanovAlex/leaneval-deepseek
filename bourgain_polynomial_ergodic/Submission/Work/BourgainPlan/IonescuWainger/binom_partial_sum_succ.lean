import Mathlib

/-!
# A truncated Pascal (binomial) partial-sum identity

For a commutative semiring `R`, elements `P c : R` and naturals `n k`, the partial sums of the
two binomial expansions `(c + P)^(n+1)` and `(c + P)^n` are linked by the recursion

`∑_{m ≤ k} C(n+1,m) c^(n+1-m) P^m
   = P * ∑_{m < k} C(n,m) c^(n-m) P^m + c * ∑_{m ≤ k} C(n,m) c^(n-m) P^m`,

which is Pascal's rule `C(n+1,m) = C(n,m) + C(n,m-1)` reindexed.  This is the algebraic
identity used to control the Cauchy–Schwarz/partial-summation steps in the Ionescu–Wainger
circle-method decomposition.

The proof uses a general Pascal identity for an arbitrary weight function `f : ℕ → R`
(`pascal_aux`), together with the two elementary rewritings
`c^(n+1-m) = c * c^(n-m)` (for `m ≤ n`) and `C(n,m) = 0` (for `m > n`).
-/

namespace Work.BourgainPlan.IonescuWainger

open Finset

/-- For `n < m` the binomial coefficient `C(n,m)` vanishes. -/
lemma coeff_zero_of_lt {R : Type*} [CommSemiring R] {n m : ℕ} (h : n < m) :
    ((n.choose m : ℕ) : R) = 0 := by
  rw [Nat.choose_eq_zero_of_lt h, Nat.cast_zero]

/-- For `m ≤ n` one has `c^(n+1-m) = c * c^(n-m)`. -/
lemma pow_sub_succ {R : Type*} [Monoid R] (c : R) {n m : ℕ} (h : m ≤ n) :
    c ^ (n + 1 - m) = c * c ^ (n - m) := by
  have hm : n + 1 - m = (n - m) + 1 := by omega
  rw [hm, pow_succ']

/-- General Pascal identity for a weighted truncated binomial sum, with an arbitrary weight
`f : ℕ → R`: the `(n+1)`-row partial sum equals the `n`-row partial sum with the same weights
plus the `n`-row partial sum of the shifted weights. -/
lemma pascal_aux {R : Type*} [CommSemiring R] (f : ℕ → R) (n : ℕ) :
    ∀ k : ℕ, (∑ m ∈ Finset.range (k + 1), ((n + 1).choose m : R) * f m)
      = (∑ m ∈ Finset.range (k + 1), (n.choose m : R) * f m)
        + (∑ m ∈ Finset.range k, (n.choose m : R) * f (m + 1)) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ (fun m => ((n + 1).choose m : R) * f m) (k + 1),
        Finset.sum_range_succ (fun m => (n.choose m : R) * f m) (k + 1),
        Finset.sum_range_succ (fun m => (n.choose m : R) * f (m + 1)) k,
        ih, Nat.choose_succ_succ, Nat.cast_add]
    ring

theorem binom_partial_sum_succ {R : Type*} [CommSemiring R] (P c : R) (n k : ℕ) :
    (∑ m ∈ Finset.range (k + 1), ((n + 1).choose m : R) * c ^ (n + 1 - m) * P ^ m)
      = P * (∑ m ∈ Finset.range k, (n.choose m : R) * c ^ (n - m) * P ^ m)
        + c * (∑ m ∈ Finset.range (k + 1), (n.choose m : R) * c ^ (n - m) * P ^ m) := by
  have h1 := pascal_aux (fun m => c ^ (n + 1 - m) * P ^ m) n k
  have h2 : (∑ m ∈ Finset.range (k + 1), (n.choose m : R) * (c ^ (n + 1 - m) * P ^ m))
      = c * (∑ m ∈ Finset.range (k + 1), (n.choose m : R) * (c ^ (n - m) * P ^ m)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    by_cases hmn : m ≤ n
    · rw [pow_sub_succ c hmn]; ring
    · rw [coeff_zero_of_lt (Nat.lt_of_not_le hmn)]; ring
  have h3 : (∑ m ∈ Finset.range k, (n.choose m : R) * (c ^ (n + 1 - (m + 1)) * P ^ (m + 1)))
      = P * (∑ m ∈ Finset.range k, (n.choose m : R) * (c ^ (n - m) * P ^ m)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    have hm' : n + 1 - (m + 1) = n - m := by omega
    rw [hm', pow_succ]
    ring
  simp only [mul_assoc]
  rw [h1, h2, h3]
  ring

end Work.BourgainPlan.IonescuWainger
