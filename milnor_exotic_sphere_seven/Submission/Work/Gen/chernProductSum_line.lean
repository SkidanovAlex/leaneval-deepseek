import Mathlib
import Submission.Work.Whitney.ChernProduct
import Submission.Work.Whitney.chernProductSum_eq_fin
import Submission.Work.LerayHirsch.Series
import Submission.Work.Thom.chernClass_zero_eq_oneH

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Work.Gen

/-- **The right-hand side of the Whitney formula with a *line* bundle in the first slot.**  Since
`c_i(L) = 0` for `i ≥ 2` (the rank of `L` is `1`), all summands of `chernProductSum L W k` with
index `≥ 2` vanish, and the two remaining ones collapse to `c_k(W)` (for `i = 0`, via the graded
unit law) and `c₁(L) ⌣ c_{k-1}(W)` (for `i = 1`).  The result is stated with the elementary
symmetric-style degree cast `2 * (1 + (k - 1)) = 2 * k`, matching the shape of the recursion of
`Work.Gen.eSym` (which is the other side of the split Whitney formula).

Proof route: `Work.Whitney.chernProductSum` is `∑ i ∈ Finset.range (k + 1), …` (or `Fin (k+1)`-indexed
via `Work.Whitney.chernProductSum_eq_fin`); the summand at index `i` contains
`Work.Thom.chernClass 1 i L`, which is `0` for `i ≥ 2` by `Work.Thom.chernClass_succ_of_gt` (and the
graded product of `0` with anything is `0`, `Work.LerayHirsch.cupChern_zero_left`), so the sum equals
its `i = 0` and `i = 1` terms; the `i = 0` term is `c_0(L) ⌣ c_k(W) = 1 ⌣ c_k(W) = c_k(W)` by
`Work.Thom.chernClass_zero_eq_oneH`, `Work.Cohomology.cupH'_one_left` and the degree-cast bookkeeping
(the same computation as in `Work.LerayHirsch.chernProductSum_rank_zero_first` or
`Work.Gen.chernProductSum_zero`).  (For `i ≥ 2` it helps to rewrite `1` as `0 + 1` so that
`chernClass_succ_of_gt` fires.) -/
theorem chernProductSum_line {B : Type} [TopologicalSpace B] {ι ι' : Type} [Fintype ι] [Fintype ι']
    {m : ℕ} (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') (k : ℕ) :
    Work.Whitney.chernProductSum L W k
      = Work.Thom.chernClass m k W
        + (if h : 1 ≤ k then Work.Thom.cohTransport (by omega : 2 * (1 + (k - 1)) = 2 * k)
             (Work.Whitney.cupChern 1 (k - 1) (Work.Thom.chernClass 1 1 L)
               (Work.Thom.chernClass m (k - 1) W)) else 0) := by
  -- The `i`-th summand of `chernProductSum L W k`, as a function of `i : ℕ`.
  let f : ℕ → Work.Thom.Coh ℤ (2 * k) B := fun i =>
    if h : i ≤ k then
      Work.Thom.cohTransport (by omega : 2 * (i + (k - i)) = 2 * k)
        (Work.Whitney.chernSummand L W i (k - i))
    else 0
  have hgoal : Work.Whitney.chernProductSum L W k = ∑ i ∈ Finset.range (k + 1), f i := rfl
  -- Every summand with index `≥ 2` vanishes: `c_i(L) = 0` for `i > 1` (and the summand is `0`
  -- outside the range `i ≤ k` by the guard).
  have hvan : ∀ i, 2 ≤ i → f i = 0 := by
    intro i hi
    by_cases hik : i ≤ k
    · rw [show f i = (if h : i ≤ k then
          Work.Thom.cohTransport (by omega : 2 * (i + (k - i)) = 2 * k)
            (Work.Whitney.chernSummand L W i (k - i)) else 0) from rfl,
        dif_pos hik, Work.Whitney.chernSummand_def,
        Work.Thom.chernClass_eq_zero_of_lt L (by omega : 1 < i),
        Work.LerayHirsch.cupChern_zero_left, Work.Thom.cohTransport_zero]
    · rw [show f i = (if h : i ≤ k then
          Work.Thom.cohTransport (by omega : 2 * (i + (k - i)) = 2 * k)
            (Work.Whitney.chernSummand L W i (k - i)) else 0) from rfl, dif_neg hik]
  -- The `i = 0` term is `c_0(L) ⌣ c_k(W) = 1 ⌣ c_k(W) = c_k(W)`.
  have hf0 : f 0 = Work.Thom.chernClass m k W := by
    rw [show f 0 = (if h : (0:ℕ) ≤ k then
          Work.Thom.cohTransport (by omega : 2 * (0 + (k - 0)) = 2 * k)
            (Work.Whitney.chernSummand L W 0 (k - 0)) else 0) from rfl,
        dif_pos (Nat.zero_le k), Work.Whitney.chernSummand_def,
        Work.Thom.chernClass_zero_eq_oneH, Work.Whitney.cupChern_def,
        Work.Cohomology.cupH'_one_left, Work.LerayHirsch.eqRec_eq_cohTransport,
        Work.Whitney.cohTransport_trans, Work.Whitney.cohTransport_trans]
    exact (Work.LerayHirsch.cohTransport_congr_proof _ (rfl : 2 * k = 2 * k)).trans
      (Work.Thom.cohTransport_rfl _)
  -- The `i = 1` term is the second summand of the statement.
  have hone : f 1 = (if h : 1 ≤ k then Work.Thom.cohTransport (by omega : 2 * (1 + (k - 1)) = 2 * k)
        (Work.Whitney.cupChern 1 (k - 1) (Work.Thom.chernClass 1 1 L)
          (Work.Thom.chernClass m (k - 1) W)) else 0) := by
    by_cases hk : 1 ≤ k
    · rw [show f 1 = (if h : (1:ℕ) ≤ k then Work.Thom.cohTransport (by omega : 2 * (1 + (k - 1)) = 2 * k)
          (Work.Whitney.chernSummand L W 1 (k - 1)) else 0) from rfl,
        dif_pos hk, dif_pos hk]
      rw [Work.Whitney.chernSummand_def]
    · rw [show f 1 = (if h : (1:ℕ) ≤ k then Work.Thom.cohTransport (by omega : 2 * (1 + (k - 1)) = 2 * k)
          (Work.Whitney.chernSummand L W 1 (k - 1)) else 0) from rfl,
        dif_neg hk, dif_neg hk]
  -- The sum only sees the indices `0` and `1`.
  have hsum : ∑ i ∈ Finset.range (k + 1), f i = f 0 + f 1 := by
    by_cases hk : 1 ≤ k
    · have h2 : 2 ≤ k + 1 := by omega
      rw [← Work.LerayHirsch.sum_range_extend (f := f) h2 hvan]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
      simp
    · have hf1z : f 1 = 0 := hone.trans (dif_neg hk)
      have hle : k + 1 ≤ 1 := by omega
      have hvan' : ∀ j, k + 1 ≤ j → f j = 0 := by
        intro j hj
        rw [show f j = (if h : j ≤ k then
              Work.Thom.cohTransport (by omega : 2 * (j + (k - j)) = 2 * k)
                (Work.Whitney.chernSummand L W j (k - j)) else 0) from rfl,
            dif_neg (by omega : ¬ j ≤ k)]
      rw [Work.LerayHirsch.sum_range_extend (f := f) hle hvan', Finset.sum_range_one,
        hf1z, add_zero]
  rw [hgoal, hsum, hf0, hone]

end Work.Gen
