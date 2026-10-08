import Mathlib
import Submission.Work.BSW.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.BCountSum
import Submission.Work.CORE3.SumMulBCount

namespace Work.BSW.Cases.K4

open Work.GW2

/-! ## Elementary truncation lemmas for `bCount`

`bCount H n` is the number of nontrivial cosets of `H` containing exactly `n` involutions.

* `bCount_eq_zero_of_lt`: a coset of `H` contains at most `Nat.card H` involutions, so
  `bCount H n = 0` for `n > Nat.card H`.
* `sum_range_extend`: a finite sum may be extended over a larger range as long as the extra
  terms vanish.
* `sum_range_three`, `sum_range_mul_three`: under the hypothesis `h3` that all `bCount H n` with
  `n ≥ 3` vanish, the total sums `∑ b_n` and `∑ n b_n` truncate to the first three terms.
-/

/-- A coset of `H` contains at most `Nat.card H` involutions, hence `bCount H n = 0` for
`n > Nat.card H`. -/
private lemma bCount_eq_zero_of_lt {G : Type} [Group G] [Finite G] (H : Subgroup G) {n : ℕ}
    (hn : Nat.card ↥H < n) : Work.GW2.bCount H n = 0 := by
  rw [bCount]
  rw [show {c : G ⧸ H | c ≠ ((1 : G) : G ⧸ H) ∧ cosetInvCount H (Quotient.out c) = n} = ∅ from ?_,
    Set.ncard_empty]
  rw [Set.eq_empty_iff_forall_notMem]
  rintro c ⟨-, hc⟩
  have := Work.CORE2A.cosetInvCount_le H (Quotient.out c)
  omega

/-- Extend a finite sum over a larger range when all the extra terms vanish. -/
private lemma sum_range_extend {f : ℕ → ℕ} {M K : ℕ} (hMK : M ≤ K)
    (hf : ∀ n, M ≤ n → f n = 0) :
    (∑ n ∈ Finset.range M, f n) = ∑ n ∈ Finset.range K, f n := by
  refine Finset.sum_subset (Finset.range_mono hMK) ?_
  intro x hx hx'
  exact hf x (by simp only [Finset.mem_range] at hx'; omega)

/-- Under `h3`, the total sum of the `b_n` truncates to its first three terms. -/
private lemma sum_range_three (b : ℕ → ℕ) (hb : ∀ n, 3 ≤ n → b n = 0) {M : ℕ} (hM : 3 ≤ M) :
    (∑ n ∈ Finset.range M, b n) = b 0 + b 1 + b 2 := by
  have htail : (∑ x ∈ Finset.range (M - 3), b (3 + x)) = 0 :=
    Finset.sum_eq_zero (fun x _ => hb (3 + x) (by omega))
  rw [show M = 3 + (M - 3) by omega, Finset.sum_range_add, htail, add_zero]
  simp [Finset.sum_range_succ]

/-- Under `h3`, the weighted sum `∑ n * b_n` truncates to `b_1 + 2 b_2`. -/
private lemma sum_range_mul_three (b : ℕ → ℕ) (hb : ∀ n, 3 ≤ n → b n = 0) {M : ℕ}
    (hM : 3 ≤ M) : (∑ n ∈ Finset.range M, n * b n) = b 1 + 2 * b 2 := by
  have htail : (∑ x ∈ Finset.range (M - 3), (3 + x) * b (3 + x)) = 0 :=
    Finset.sum_eq_zero (fun x _ => by rw [hb (3 + x) (by omega), mul_zero])
  rw [show M = 3 + (M - 3) by omega, Finset.sum_range_add, htail, add_zero]
  simp [Finset.sum_range_succ]

/-- The involutions of `G` split into those in `H` and those outside `H`. -/
private lemma ncard_involutions_split {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    ({x : G | orderOf x = 2} : Set G).ncard =
      ({x : G | orderOf x = 2 ∧ x ∈ H} : Set G).ncard +
      ({x : G | orderOf x = 2 ∧ x ∉ H} : Set G).ncard := by
  have hdisj : Disjoint {x : G | orderOf x = 2 ∧ x ∈ H} {x : G | orderOf x = 2 ∧ x ∉ H} := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hx'.2 hx.2
  have hunion : {x : G | orderOf x = 2 ∧ x ∈ H} ∪ {x : G | orderOf x = 2 ∧ x ∉ H}
      = {x : G | orderOf x = 2} := by
    ext x; simp only [Set.mem_union, Set.mem_ofPred_eq]; tauto
  rw [← hunion, Set.ncard_union_eq hdisj]

/-- Counting the involutions of `G` coset by coset, and counting the nontrivial cosets of `H`:
if `b_n = 0` for every `n ≥ 3` then

* `|I(G)| = |I(H)| + b_1 + 2 b_2` (each nontrivial coset contributes `n b_n` involutions, and
  only `n = 1, 2` can occur), and
* `b_0 + b_1 + b_2 = [G : H] - 1` (every nontrivial coset falls into exactly one of the three
  cases `n = 0, 1, 2`).

The two combinatorial inputs `Work.CORE3.SumMulBCount` (`∑ n b_n` = number of involutions
outside `H`) and `Work.CORE3.BCountSum` (`∑ b_n` = number of nontrivial cosets) are truncated
using `h3`. -/
theorem countingFacts {G : Type} [Group G] [Finite G] (H : Subgroup G)
    (h3 : ∀ n : ℕ, 3 ≤ n → Work.GW2.bCount H n = 0) :
    ({x : G | orderOf x = 2} : Set G).ncard =
        ({x : G | orderOf x = 2 ∧ x ∈ H} : Set G).ncard + Work.GW2.bCount H 1
          + 2 * Work.GW2.bCount H 2 ∧
      Work.GW2.bCount H 0 + Work.GW2.bCount H 1 + Work.GW2.bCount H 2 = H.index - 1 := by
  classical
  constructor
  · -- `∑ n b_n` counts the involutions outside `H`
    have hsum := Work.CORE3.SumMulBCount G H
    have hkey : (∑ n ∈ Finset.range (Nat.card ↥H + 1), n * Work.GW2.bCount H n)
        = Work.GW2.bCount H 1 + 2 * Work.GW2.bCount H 2 := by
      rw [sum_range_extend (f := fun n => n * Work.GW2.bCount H n)
        (M := Nat.card ↥H + 1) (K := max (Nat.card ↥H + 1) 3) (le_max_left _ _)
        (fun n hn => by rw [bCount_eq_zero_of_lt H (by omega), mul_zero])]
      exact sum_range_mul_three _ h3 (le_max_right _ _)
    have hout : ({x : G | orderOf x = 2 ∧ x ∉ H} : Set G).ncard =
        Work.GW2.bCount H 1 + 2 * Work.GW2.bCount H 2 := by
      rw [← hsum, hkey]
    rw [ncard_involutions_split H, hout]
    ring
  · -- `∑ b_n` counts the nontrivial cosets of `H`
    rw [← Work.CORE3.BCountSum G H]
    rw [sum_range_extend (f := fun n => Work.GW2.bCount H n)
      (M := Nat.card ↥H + 1) (K := max (Nat.card ↥H + 1) 3) (le_max_left _ _)
      (fun n hn => bCount_eq_zero_of_lt H (by omega))]
    exact (sum_range_three _ h3 (le_max_right _ _)).symm

end Work.BSW.Cases.K4
