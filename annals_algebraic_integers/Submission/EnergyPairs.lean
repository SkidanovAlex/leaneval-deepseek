import Submission.ThreePages
import Mathlib.Tactic

/-!
# The ordered/unordered double-log-sum identity (`EnergyPairs`)

Purely combinatorial helper for `Submission.EnergyHalf.energy_half`.

CLAIM: for every natural `n`,

    Σ_{k ∈ Icc 1 n} Σ_{j ∈ (Icc 1 n) \ {k}} log |α_{n,k} − α_{n,j}|
        = 2 · Σ_{i ∈ Icc 1 n} Σ_{j ∈ Icc (i+1) n} log |α_{n,i} − α_{n,j}|

where `α = Submission.Quantile.alpha`.  The left side runs over all ORDERED
pairs `(k,j)` of distinct indices in `[1..n]`; the right side runs over all
UNORDERED pairs `i < j`.  The only property of `α` used is symmetry of the
summand:  `log |α_k − α_j| = log |α_j − α_k|` (i.e. `abs_sub_comm`).  No
distinctness, no positivity of the arguments is needed (`Real.log 0 = 0` in
mathlib, so even if some `|α_k − α_j| = 0` nothing breaks — but in fact roots
are distinct).

## Suggested Lean route (rewrite the ordered pair sum)

Let `g (a b : ℕ) : ℝ := Real.log |alpha n a - alpha n b|`.

1. Rewrite the LHS as a sum over the set `P : Finset (ℕ × ℕ)` of pairs
   `(k,j)` with `k,j ∈ Icc 1 n` and `k ≠ j`:

       (Finset.Icc 1 n).product (Finset.Icc 1 n) filtered by (fun p => p.1 ≠ p.2)

   The identity `Σ_{k∈s} Σ_{j∈s.erase k} f k j = Σ_{(k,j) ∈ (s.product s).filter (·.1 ≠ ·.2)} f k.1 k.2`
   follows from `Finset.sum_product` and `Finset.sum_filter` (or by `Finset.sum_bij`).
   Note that `(Finset.Icc 1 n).erase k = (Finset.Icc 1 n).filter (· ≠ k)`.

2. Split the filtered product set by trichotomy `p.1 < p.2 ∨ p.2 < p.1`
   (use `Finset.filter_or` with the two disjoint filters and `Finset.sum_filter`),
   giving  LHS = A + B where
       A = Σ_{i<j} g i j ,  B = Σ_{j<i} g i j  (both with indices in [1..n]).

3. Reindex B by swapping the coordinates (a `Finset.sum_bij` with the swap
   function `fun p => (p.2, p.1)` — it is an involution on the filtered set),
   giving  B = Σ_{i<j} g j i = Σ_{i<j} g i j  by symmetry
   (`Real.log (|a - b|) = Real.log (|b - a|)`, from `abs_sub_comm`), so
   LHS = 2·A.

4. Finally identify  A = Σ_{i ∈ Icc 1 n} Σ_{j ∈ Icc (i+1) n} g i j
   (i.e. `Σ_{(i,j) : i<j, i∈[1..n]} g i j` with the iterated form): the pairs
   `(i,j)` with `i ∈ Icc 1 n ∧ i < j ∧ j ≤ n` are exactly `{(i,j) : i ∈ Icc 1 n,
   j ∈ Icc (i+1) n}` since `j ∈ Icc (i+1) n` iff `i+1 ≤ j ≤ n` iff `i < j ≤ n`.

Some hints for the API of THIS mathlib version (2026, Lean v4.33): the file
must import `Submission.ThreePages` FIRST (before any large mathlib import) so
that the standard names are available; within the body use `open scoped
BigOperators`, and `open Finset` if helpful.  `Nat.card_Icc` exists (use it,
not `Finset.card_Icc`, if you need cardinalities).  Test any lemma name with
`#check` in a scratch file before relying on it.  `Finset.sum_congr`,
`Finset.sum_filter`, `Finset.sum_product`, `Finset.sum_bij`,
`Finset.sum_erase_add`, `Finset.mem_erase`, `abs_sub_comm` are all available.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators
open Polynomial

namespace Submission.EnergyPairs

open Submission.Quantile
open Submission.PotentialContinuity
open Submission.SerreExample
open Submission.ThreePages
open Submission.PotentialDefs

/-- Pointwise trichotomy split used inside the sums:
`[j ≠ k]·v = [j < k]·v + [k < j]·v`. -/
private lemma split_ne (j k : ℕ) (v : ℝ) :
    (if j ≠ k then v else 0) = (if j < k then v else 0) + (if k < j then v else 0) := by
  by_cases hlt : j < k
  · have hkj : ¬ k < j := by omega
    have hne : j ≠ k := by omega
    simp [hne, hlt, hkj]
  · by_cases hgt : k < j
    · have hne : j ≠ k := by omega
      simp [hne, hlt, hgt]
    · have hjeq : j = k := by omega
      simp [hjeq]

/-- Pointwise trichotomy split, disjunction form:
`[j < k ∨ k < j]·v = [j < k]·v + [k < j]·v`. -/
private lemma split_or (j k : ℕ) (v : ℝ) :
    (if j < k ∨ k < j then v else 0) = (if j < k then v else 0) + (if k < j then v else 0) := by
  by_cases hlt : j < k
  · have hkj : ¬ k < j := by omega
    simp [hlt, hkj]
  · by_cases hgt : k < j
    · simp [hlt, hgt]
    · have hjeq : j = k := by omega
      simp [hjeq]

/-- The ordered sum over pairs `(k,j)`, `k ≠ j`, of a symmetric function is twice
the unordered (`i < j`) sum.  This is the purely combinatorial content of
`erase_sum_eq_two_lt_sum`: `g` is any pairwise-symmetric function. -/
private lemma main_id (n : ℕ) (g : ℕ → ℕ → ℝ) (hsym : ∀ a b : ℕ, g a b = g b a) :
    (∑ k ∈ Finset.Icc 1 n, ∑ j ∈ (Finset.Icc 1 n).erase k, g k j)
      = 2 * (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc (i + 1) n, g i j) := by
  classical
  let s : Finset ℕ := Finset.Icc 1 n
  let U : Finset (ℕ × ℕ) := (s ×ˢ s).filter (fun p : ℕ × ℕ => p.1 < p.2)
  let D : Finset (ℕ × ℕ) := (s ×ˢ s).filter (fun p : ℕ × ℕ => p.2 < p.1)
  -- LHS = (pairs with second < first) + (pairs with first < second)
  have hLHS :
      (∑ k ∈ s, ∑ j ∈ s.erase k, g k j)
        = (∑ p ∈ D, g p.1 p.2) + (∑ p ∈ U, g p.1 p.2) := by
    rw [show (∑ p ∈ D, g p.1 p.2)
          = ∑ k ∈ s, ∑ j ∈ s, (if j < k then g k j else 0) by
            dsimp [D]
            rw [Finset.sum_filter, Finset.sum_product]]
    rw [show (∑ p ∈ U, g p.1 p.2)
          = ∑ k ∈ s, ∑ j ∈ s, (if k < j then g k j else 0) by
            dsimp [U]
            rw [Finset.sum_filter, Finset.sum_product]]
    rw [show (∑ k ∈ s, ∑ j ∈ s.erase k, g k j)
          = ∑ k ∈ s, ∑ j ∈ s, (if j ≠ k then g k j else 0) by
            apply Finset.sum_congr rfl
            intro k hk
            have h : s.erase k = s.filter (fun j => j ≠ k) := by
              ext j
              constructor
              · intro hj
                exact Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hj).2, (Finset.mem_erase.mp hj).1⟩
              · intro hj
                exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hj).2, (Finset.mem_filter.mp hj).1⟩
            rw [h]
            rw [Finset.sum_filter]]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    exact split_ne j k (g k j)
  -- the two "unoriented" halves are equal (swap coordinates)
  have hswap : (∑ p ∈ D, g p.1 p.2) = ∑ p ∈ U, g p.1 p.2 := by
    refine Finset.sum_bij (fun p hp => (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro p hp
      have hpD := (Finset.mem_filter.mp hp)
      have hpPr := (Finset.mem_product.mp hpD.1)
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hpPr.2, hpPr.1⟩, hpD.2⟩
    · intro p₁ hp₁ p₂ hp₂ h
      apply Prod.ext
      · exact congrArg Prod.snd h
      · exact congrArg Prod.fst h
    · intro q hq
      have hqU := (Finset.mem_filter.mp hq)
      have hqPr := (Finset.mem_product.mp hqU.1)
      refine ⟨(q.2, q.1), ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hqPr.2, hqPr.1⟩, hqU.2⟩
      · rfl
    · intro p hp
      exact hsym p.1 p.2
  -- the i < j half is exactly the iterated RHS inner sum
  have hUU :
      (∑ i ∈ s, ∑ j ∈ Finset.Icc (i + 1) n, g i j) = ∑ p ∈ U, g p.1 p.2 := by
    rw [show (∑ p ∈ U, g p.1 p.2)
          = ∑ i ∈ s, ∑ j ∈ s, (if i < j then g i j else 0) by
            dsimp [U]
            rw [Finset.sum_filter, Finset.sum_product]]
    rw [show (∑ i ∈ s, ∑ j ∈ Finset.Icc (i + 1) n, g i j)
          = ∑ i ∈ s, ∑ j ∈ s, (if i < j then g i j else 0) by
            apply Finset.sum_congr rfl
            intro i hi
            rw [show Finset.Icc (i + 1) n = s.filter (fun j => i < j) by
              ext j
              dsimp [s]
              constructor
              · intro hj
                have h1 : i + 1 ≤ j := (Finset.mem_Icc.mp hj).1
                have h2 : j ≤ n := (Finset.mem_Icc.mp hj).2
                exact Finset.mem_filter.mpr
                  ⟨Finset.mem_Icc.mpr ⟨by omega, h2⟩, by omega⟩
              · intro hj
                have h1 : i < j := (Finset.mem_filter.mp hj).2
                have h2 : j ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).2
                exact Finset.mem_Icc.mpr ⟨by omega, h2⟩]
            rw [Finset.sum_filter]]
  calc
    (∑ k ∈ Finset.Icc 1 n, ∑ j ∈ (Finset.Icc 1 n).erase k, g k j)
        = (∑ k ∈ s, ∑ j ∈ s.erase k, g k j) := by
          dsimp [s]
    _ = (∑ p ∈ D, g p.1 p.2) + (∑ p ∈ U, g p.1 p.2) := hLHS
    _ = (∑ p ∈ U, g p.1 p.2) + (∑ p ∈ U, g p.1 p.2) := by rw [hswap]
    _ = 2 * (∑ p ∈ U, g p.1 p.2) := by ring
    _ = 2 * (∑ i ∈ s, ∑ j ∈ Finset.Icc (i + 1) n, g i j) := by rw [hUU]
    _ = 2 * (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc (i + 1) n, g i j) := by
          dsimp [s]

/-- `deliver_me`-style helper: the ordered log-sum is twice the unordered one. -/
theorem erase_sum_eq_two_lt_sum (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, ∑ j ∈ (Finset.Icc 1 n).erase k,
        Real.log |alpha n k - alpha n j|)
      = 2 * (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc (i + 1) n,
          Real.log |alpha n i - alpha n j|) := by
  simpa using
    main_id n (fun a b => Real.log |alpha n a - alpha n b|) (by
      intro a b
      exact congrArg Real.log (abs_sub_comm (alpha n a) (alpha n b)))

end Submission.EnergyPairs
