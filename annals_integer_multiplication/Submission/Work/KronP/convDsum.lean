import Mathlib
import Submission.Work.KronP.kdefs

/-!
# `convCoef = dsumL` (KronP)

`Work.KronP.convCoef l₁ l₂ m` is the `m`-th convolution coefficient of two coefficient lists,
written as a single (filtered) sum over the index of the *first* list; `Work.KronP.dsumL l₁ l₂ r m`
is the same coefficient written as the double sum over `{(i,j) : i,j < r, i+j = m}`, which is the
form in which polynomial multiplication of two length-`r` polynomials is phrased.

Both are identified with the explicit filtered sum
`Σ_{i ∈ range r, i ≤ m, m-i < r} l₁[i]·l₂[m-i]`.

(The hypothesis `m < 2 * r` of the statement is not needed: when `m ≥ 2 * r` the index set is
empty and both sides vanish.)
-/

set_option autoImplicit false

namespace Work.KronP

open HvdH

/-- The two filters defining `convCoef` describe the same index set as
`i < r ∧ i ≤ m ∧ m - i < r`. -/
theorem convCoef_range_min_filter (a m r : ℕ) :
    (Finset.range (min a (m + 1))).filter (fun j => m - j < r)
      = (Finset.range a).filter (fun j => j ≤ m ∧ m - j < r) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_min, Nat.lt_succ_iff]
  constructor
  · rintro ⟨⟨ha, hm⟩, hr⟩; exact ⟨ha, hm, hr⟩
  · rintro ⟨ha, hm, hr⟩; exact ⟨⟨ha, hm⟩, hr⟩

/-- `convCoef` as a `Finset` sum over its index set. -/
theorem convCoef_eq_finsetSum (l₁ l₂ : List ℤ) (m : ℕ) :
    convCoef l₁ l₂ m
      = ∑ j ∈ (Finset.range (min l₁.length (m + 1))).filter (fun j => m - j < l₂.length),
          l₁.getD j 0 * l₂.getD (m - j) 0 := by
  unfold convCoef
  rw [← List.sum_toFinset (fun j => l₁.getD j 0 * l₂.getD (m - j) 0)
        (List.Nodup.filter (fun j => decide (m - j < l₂.length)) (List.nodup_range)),
      List.toFinset_filter, List.toFinset_range]
  simp only [decide_eq_true_eq]

/-- The inner sum of `dsumL`: for fixed `i`, only the index `j = m - i` contributes, and only if
that index lies in `range r`; if `i > m` every term vanishes. -/
theorem dsumL_inner_sum (a b : List ℤ) (r m i : ℕ) :
    (∑ j ∈ Finset.range r, if i + j = m then a.getD i 0 * b.getD j 0 else 0)
      = (if i ≤ m ∧ m - i < r then a.getD i 0 * b.getD (m - i) 0 else 0) := by
  by_cases hi : i ≤ m
  · have h1 : (∑ j ∈ Finset.range r, if i + j = m then a.getD i 0 * b.getD j 0 else 0)
        = (∑ j ∈ Finset.range r, if j = m - i then a.getD i 0 * b.getD j 0 else 0) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hij : i + j = m
      · rw [ite_eq_left hij, ite_eq_left (show j = m - i by omega)]
      · rw [ite_eq_right hij, ite_eq_right (show ¬ (j = m - i) by omega)]
    rw [h1, Finset.sum_ite_eq']
    simp only [Finset.mem_range]
    by_cases hr : m - i < r
    · rw [ite_eq_left hr, ite_eq_left (show i ≤ m ∧ m - i < r from ⟨hi, hr⟩)]
    · rw [ite_eq_right hr, ite_eq_right (show ¬ (i ≤ m ∧ m - i < r) from fun h => hr h.2)]
  · have hz : (∑ j ∈ Finset.range r, if i + j = m then a.getD i 0 * b.getD j 0 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [ite_eq_right (show ¬ (i + j = m) by omega)]
    rw [hz, ite_eq_right (show ¬ (i ≤ m ∧ m - i < r) by omega)]

/-- `dsumL` as a single filtered sum. -/
theorem dsumL_eq_finsetSum (l₁ l₂ : List ℤ) (r m : ℕ) :
    dsumL l₁ l₂ r m
      = ∑ i ∈ (Finset.range r).filter (fun i => i ≤ m ∧ m - i < r),
          l₁.getD i 0 * l₂.getD (m - i) 0 := by
  unfold dsumL
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact dsumL_inner_sum l₁ l₂ r m i

theorem convDsum {l₁ l₂ : List ℤ} {r m : ℕ} (h₁ : l₁.length = r) (h₂ : l₂.length = r)
    (hm : m < 2 * r) : Work.KronP.convCoef l₁ l₂ m = Work.KronP.dsumL l₁ l₂ r m := by
  rw [dsumL_eq_finsetSum, convCoef_eq_finsetSum, h₁, h₂, convCoef_range_min_filter]

end Work.KronP
