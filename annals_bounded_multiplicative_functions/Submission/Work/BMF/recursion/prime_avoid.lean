import Mathlib
import Submission.Work.BMF.recursion.Defs
import Submission.Work.BMF.recursion.card_primes_gt_dvd_le
import Submission.Work.BMF.recursion.card_filter_lt_fin_prod

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.recursion

open scoped BigOperators

/-- For naturals `1 ≤ a ≤ c` and `1 ≤ b ≤ c`, we have `|a - b| < c`. -/
private lemma int_natAbs_nat_sub_lt {a b c : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ c) (hb1 : 1 ≤ b)
    (hb : b ≤ c) : (((a : ℤ) - (b : ℤ)).natAbs) < c := by
  have h : (((a : ℤ) - (b : ℤ)).natAbs : ℤ) = |(a : ℤ) - (b : ℤ)| := by
    rw [Nat.cast_natAbs, Int.cast_id]
  have hZ : (((a : ℤ) - (b : ℤ)).natAbs : ℤ) < (c : ℤ) := by
    rw [h, abs_lt]
    constructor <;> omega
  exact_mod_cast hZ

/-- **Prime avoidance for the head of a tuple** (Wooley, Michigan Math. J. **40** (1993), 175–180,
§2, case (b)).  Let `x` be a `k`-tuple with entries in `[1,Q]` whose coordinates are pairwise
distinct, let `M ≥ 1` with `Q < M^k`, and let `P` be a set of primes all `> M` of size
`> k(k-1)²/2`.  Then some `p ∈ P` has the coordinates of `x` pairwise distinct modulo `p`
(`HDp p k (le_refl k) x`, i.e. `p ∤ (x i - x j)` for `i ≠ j`).

Route.  If every `p ∈ P` failed, each `p ∈ P` would divide some difference `x i - x j`, hence the
product `∏_{i<j} (x i - x j)`, a nonzero integer of absolute value `< Q^{k(k-1)/2}` (using
`Q < M^k`).  Now, distinct primes `> M` dividing a nonzero integer `n` with `|n| < M^t` number at
most `t - 1`: if `q_1,…,q_s > M` all divide `n` then `M^s < q_1⋯q_s ≤ |n| < M^t`.  Apply this to
each of the `k(k-1)/2` differences (each nonzero and `< Q < M^k`, so at most `k-1` primes `> M`
divide it): at most `(k(k-1)/2)·(k-1) = k(k-1)²/2` primes of `P` divide the product, which
contradicts `k(k-1)² < 2·|P|`. -/
theorem prime_avoid (k Q M : ℕ) (x : Tup k Q) (hx : HD (le_refl k) x) (hMQ : Q < M ^ k)
    (P : Finset ℕ) (hPp : ∀ p ∈ P, Nat.Prime p) (hPM : ∀ p ∈ P, M < p)
    (hPc : k * (k - 1) * (k - 1) < 2 * P.card) :
    ∃ p ∈ P, HDp p k (le_refl k) x := by
  classical
  by_contra hcon
  push Not at hcon
  -- Each failing prime divides one of the head differences.
  have hcon' : ∀ p ∈ P, ∃ i j : Fin k, i ≠ j ∧
      (p : ℤ) ∣ ((x (hIdx (le_refl k) i)).1 : ℤ) - ((x (hIdx (le_refl k) j)).1 : ℤ) := by
    intro p hp
    have h := hcon p hp
    simp only [HDp] at h
    push Not at h
    exact h
  let d : Fin k → Fin k → ℤ := fun i j =>
    ((x (hIdx (le_refl k) i)).1 : ℤ) - ((x (hIdx (le_refl k) j)).1 : ℤ)
  -- Head coordinates are distinct, so each difference is nonzero.
  have hd_ne : ∀ i j : Fin k, i ≠ j → d i j ≠ 0 := by
    intro i j hij h
    have h1 : ((x (hIdx (le_refl k) i)).1 : ℤ) = ((x (hIdx (le_refl k) j)).1 : ℤ) := by
      have := sub_eq_zero.mp h
      simpa only [d] using this
    have h2 : (x (hIdx (le_refl k) i)).1 = (x (hIdx (le_refl k) j)).1 := by exact_mod_cast h1
    exact hx i j hij (Subtype.ext h2)
  -- Each difference has absolute value `< Q < M ^ k`.
  have hd_lt : ∀ i j : Fin k, d i j ≠ 0 → (d i j).natAbs < M ^ k := by
    intro i j _
    have hi := Finset.mem_Icc.mp (x (hIdx (le_refl k) i)).2
    have hj := Finset.mem_Icc.mp (x (hIdx (le_refl k) j)).2
    have hltQ : (d i j).natAbs < Q := by
      simpa only [d] using int_natAbs_nat_sub_lt hi.1 hi.2 hj.1 hj.2
    exact lt_of_lt_of_le hltQ (le_of_lt hMQ)
  -- The unordered pairs `i < j`, and, for each, the primes of `P` dividing `x i - x j`.
  let A : Finset (Fin k × Fin k) := (Finset.univ : Finset (Fin k × Fin k)).filter (fun p => p.1 < p.2)
  let B : Fin k × Fin k → Finset ℕ := fun p => P.filter (fun q => (q : ℤ) ∣ d p.1 p.2)
  have hsub : P ⊆ A.biUnion B := by
    intro q hq
    obtain ⟨i, j, hij, hdvd⟩ := hcon' q hq
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · refine Finset.mem_biUnion.mpr ⟨(i, j), ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
      · exact Finset.mem_filter.mpr ⟨hq, hdvd⟩
    · refine Finset.mem_biUnion.mpr ⟨(j, i), ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩
      · refine Finset.mem_filter.mpr ⟨hq, ?_⟩
        have hneg : d j i = - d i j := by simp only [d]; ring
        rw [hneg]; exact dvd_neg.mpr hdvd
  -- Union bound: at most `k - 1` primes of `P` divide each difference.
  have hcard : P.card ≤ A.card * (k - 1) := by
    calc P.card ≤ (A.biUnion B).card := Finset.card_le_card hsub
      _ ≤ A.card * (k - 1) := by
        refine Finset.card_biUnion_le_card_mul A B (k - 1) ?_
        intro p hp
        have hplt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
        have hne : p.1 ≠ p.2 := ne_of_lt hplt
        have hd0 : d p.1 p.2 ≠ 0 := hd_ne p.1 p.2 hne
        exact card_primes_gt_dvd_le (d p.1 p.2) k M hd0 (hd_lt p.1 p.2 hd0) (B p)
          (fun q hq => hPp q (Finset.mem_of_mem_filter q hq))
          (fun q hq => hPM q (Finset.mem_of_mem_filter q hq))
          (fun q hq => (Finset.mem_filter.mp hq).2)
  have hA2 : A.card * 2 = k * (k - 1) := card_filter_lt_fin_prod k
  have hfin : 2 * P.card ≤ k * (k - 1) * (k - 1) := by
    calc 2 * P.card ≤ 2 * (A.card * (k - 1)) := Nat.mul_le_mul_left 2 hcard
      _ = (A.card * 2) * (k - 1) := by ring
      _ = (k * (k - 1)) * (k - 1) := by rw [hA2]
  exact absurd hPc (not_lt.mpr hfin)

end Work.BMF.recursion
