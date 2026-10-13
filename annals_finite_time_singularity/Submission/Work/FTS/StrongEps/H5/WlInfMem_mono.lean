import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.WlInf_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.H5

set_option autoImplicit false

/-! ## Two `Finset` lemmas comparing sums over `range m` with sums over `range n`, `m ≤ n`

Both sums in `Work.Spaces.WlInf` are sums over `Finset.range (l + 1)` of terms that are
manifestly nonnegative once the corresponding `SupFinite` slots are available.  Enlarging the
range therefore only adds nonnegative terms. -/

/-- A sum over `range m` of a nonnegative summand is at most the sum over the larger
`range n` (`m ≤ n`). -/
private theorem range_sum_le_range_sum {A : ℕ → ℝ} {m n : ℕ} (hmn : m ≤ n)
    (hA : ∀ k ∈ Finset.range n, 0 ≤ A k) :
    ∑ k ∈ Finset.range m, A k ≤ ∑ k ∈ Finset.range n, A k :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hmn)
    (fun k hk _ => hA k hk)

/-- The two-dimensional version of `range_sum_le_range_sum`: a double sum over the smaller
rectangle `range m × range m` is at most the double sum over `range n × range n`. -/
private theorem range_sum₂_le {B : ℕ → ℕ → ℝ} {m n : ℕ} (hmn : m ≤ n)
    (hB : ∀ j ∈ Finset.range n, ∀ k ∈ Finset.range n, 0 ≤ B j k) :
    ∑ j ∈ Finset.range m, ∑ k ∈ Finset.range m, B j k
      ≤ ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, B j k := by
  have h1 : ∑ j ∈ Finset.range m, ∑ k ∈ Finset.range m, B j k
      ≤ ∑ j ∈ Finset.range m, ∑ k ∈ Finset.range n, B j k :=
    Finset.sum_le_sum fun j hj =>
      range_sum_le_range_sum hmn (fun k hk =>
        hB j (Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) hmn)) k hk)
  refine h1.trans ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hmn) ?_
  intro j hj _
  exact Finset.sum_nonneg fun k hk => hB j hj k hk

/-- The angular double sum of `WlInf`: replacing the truncation level `l'` by a larger `l`
only weakens the truncation condition `1 ≤ j ∧ k + j ≤ m`, and enlarging the two ranges adds
nonnegative terms. -/
private theorem angular_sum_le {C : ℕ → ℕ → ℝ} {l l' : ℕ} (hll : l' ≤ l)
    (hC : ∀ j ≤ l, ∀ k ≤ l, 1 ≤ j → k + j ≤ l → 0 ≤ C j k) :
    (∑ j ∈ Finset.range (l' + 1), ∑ k ∈ Finset.range (l' + 1),
        if 1 ≤ j ∧ k + j ≤ l' then C j k else 0)
      ≤ ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
        if 1 ≤ j ∧ k + j ≤ l then C j k else 0 := by
  -- termwise comparison of the two `if`s
  have hpt : ∀ j ≤ l', ∀ k ≤ l',
      (if 1 ≤ j ∧ k + j ≤ l' then C j k else 0)
        ≤ (if 1 ≤ j ∧ k + j ≤ l then C j k else 0) := by
    intro j hj k hk
    by_cases hc : 1 ≤ j ∧ k + j ≤ l'
    · have hc' : 1 ≤ j ∧ k + j ≤ l := ⟨hc.1, le_trans hc.2 hll⟩
      rw [if_pos hc, if_pos hc']
    · rw [if_neg hc]
      by_cases hc' : 1 ≤ j ∧ k + j ≤ l
      · rw [if_pos hc']
        exact hC j (le_trans hj hll) k (le_trans hk hll) hc'.1 hc'.2
      · rw [if_neg hc']
  have h1 : (∑ j ∈ Finset.range (l' + 1), ∑ k ∈ Finset.range (l' + 1),
        if 1 ≤ j ∧ k + j ≤ l' then C j k else 0)
      ≤ ∑ j ∈ Finset.range (l' + 1), ∑ k ∈ Finset.range (l' + 1),
        if 1 ≤ j ∧ k + j ≤ l then C j k else 0 :=
    Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk =>
      hpt j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
        k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  refine h1.trans ?_
  refine range_sum₂_le (Nat.succ_le_succ hll) ?_
  intro j hj k hk
  by_cases hc : 1 ≤ j ∧ k + j ≤ l
  · rw [if_pos hc]
    exact hC j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
      k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) hc.1 hc.2
  · rw [if_neg hc]

/-- `WlInfMem` and the `𝒲^{l,∞}`-norm are monotone in the order: from `WlInfMem α l f` and
`l' ≤ l`, both the memory statement `WlInfMem α l' f` and the inequality `WlInf α l' f ≤ WlInf α l f`
follow.  (The slots of `WlInf α l' f` are a subset of those of `WlInf α l f`, and `WlInfMem α l f`
makes all the `sSup`s honest.) -/
theorem WlInfMem_mono {α : ℝ} {l l' : ℕ} (hll : l' ≤ l) {f : ℝ → ℝ → ℝ}
    (h : Work.Spaces.WlInfMem α l f) :
    Work.Spaces.WlInfMem α l' f ∧ Work.Spaces.WlInf α l' f ≤ Work.Spaces.WlInf α l f := by
  constructor
  · exact ⟨fun k hk => h.1 k (le_trans hk hll),
      fun j hj k hk hj1 hjk => h.2 j (le_trans hj hll) k (le_trans hk hll) hj1 (le_trans hjk hll)⟩
  · simp only [Work.Spaces.WlInf]
    refine add_le_add ?_ ?_
    · exact range_sum_le_range_sum (Nat.succ_le_succ hll) (fun k hk =>
        Work.Spaces.supAbs_nonneg (h.1 k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))))
    · exact angular_sum_le hll (fun j hj k hk hj1 hjk =>
        Work.Spaces.supAbs_nonneg (h.2 j hj k hk hj1 hjk))

end Work.FTS.StrongEps.H5
