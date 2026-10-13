import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `sum_shift_identity` of the level-`5` `W^{l,∞}` bookkeeping

Both sides of the identity are the *triangular* sum
`∑_{j < l+1} ∑_{k < l+1-j} V (j+1) k`:

* the right-hand side is `∑_{1 ≤ j ≤ l+1} ∑_{k < l+2-j} V j k`, i.e. the same triangular
  sum, after dropping the `j = 0` term (which vanishes because of the `1 ≤ j` guard) and
  observing that the guard `k + j ≤ l + 1` cuts `k` down to `k < l + 2 - j`;
* the left-hand side is the `j = 0` layer `∑_{k < l+1} V 1 k = ∑_{k < l+1-0} V (0+1) k`
  together with the layers `j = i+1`, `i < l`, which again are `∑_{k < l+1-(i+1)} V (i+2) k`
  because the guard `k + (i+1) ≤ l` cuts `k` down to `k < l+1-(i+1)`.

The two elementary ingredients are `sum_shift_filter_range` (the guard `k + j ≤ M` selects
exactly `Finset.range (M+1-j)` inside `Finset.range N`, for `M + 1 ≤ N`) and the split
`Finset.sum_range_succ'`, which peels off the `j = 0` term of a `range (l+1)`-sum.
-/

namespace Work.FTS.StrongEps.H5.WlInfDthAux

/-- Inside `Finset.range N` (with `M + 1 ≤ N`), the indices `k` with `k + j ≤ M` are exactly
`Finset.range (M + 1 - j)`. -/
lemma sum_shift_filter_range (N M j : ℕ) (h : M + 1 ≤ N) :
    (Finset.range N).filter (fun k => k + j ≤ M) = Finset.range (M + 1 - j) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- The inner `k`-sum of the left-hand side, evaluated at a fixed `j`: the guards
`1 ≤ j` and `k + j ≤ l` cut it down to `∑_{k < l+1-j} V (j+1) k` (and kill it when `j = 0`). -/
lemma sum_shift_inner_left (V : ℕ → ℕ → ℝ) (l j : ℕ) :
    (∑ k ∈ Finset.range (l + 1), (if 1 ≤ j ∧ k + j ≤ l then V (j + 1) k else 0))
      = (if 1 ≤ j then ∑ k ∈ Finset.range (l + 1 - j), V (j + 1) k else 0) := by
  by_cases hj : 1 ≤ j
  · rw [ite_eq_left hj]
    simp only [hj, true_and]
    rw [← Finset.sum_filter]
    congr 1
    exact sum_shift_filter_range (l + 1) l j le_rfl
  · rw [ite_eq_right hj]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [ite_eq_right]
    exact fun h => hj h.1

/-- The inner `k`-sum of the right-hand side at the shifted index `i + 1`: the guard
`k + (i+1) ≤ l + 1` cuts it down to `∑_{k < l+1-i} V (i+1) k`. -/
lemma sum_shift_inner_right (V : ℕ → ℕ → ℝ) (l i : ℕ) :
    (∑ k ∈ Finset.range (l + 2), (if 1 ≤ i + 1 ∧ k + (i + 1) ≤ l + 1 then V (i + 1) k else 0))
      = ∑ k ∈ Finset.range (l + 1 - i), V (i + 1) k := by
  have h1 : 1 ≤ i + 1 := by omega
  simp only [h1, true_and]
  rw [← Finset.sum_filter]
  congr 1
  rw [sum_shift_filter_range (l + 2) (l + 1) (i + 1) (by omega)]
  congr 1
  omega

theorem sum_shift_identity (V : ℕ → ℕ → ℝ) (l : ℕ) :
    (∑ k ∈ Finset.range (l + 1), V 1 k)
      + (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
          (if 1 ≤ j ∧ k + j ≤ l then V (j + 1) k else 0))
    = ∑ j ∈ Finset.range (l + 2), ∑ k ∈ Finset.range (l + 2),
        (if 1 ≤ j ∧ k + j ≤ l + 1 then V j k else 0) := by
  -- the common triangular form
  have hL : (∑ k ∈ Finset.range (l + 1), V 1 k)
      + (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
          (if 1 ≤ j ∧ k + j ≤ l then V (j + 1) k else 0))
      = ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1 - j), V (j + 1) k := by
    have hB : (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
          (if 1 ≤ j ∧ k + j ≤ l then V (j + 1) k else 0))
        = ∑ j ∈ Finset.range (l + 1),
            (if 1 ≤ j then ∑ k ∈ Finset.range (l + 1 - j), V (j + 1) k else 0) :=
      Finset.sum_congr rfl (fun j _ => sum_shift_inner_left V l j)
    rw [hB]
    rw [Finset.sum_range_succ'
      (fun j => (if 1 ≤ j then ∑ k ∈ Finset.range (l + 1 - j), V (j + 1) k else 0)) l]
    rw [Finset.sum_range_succ' (fun j => ∑ k ∈ Finset.range (l + 1 - j), V (j + 1) k) l]
    have h10 : ¬ ((1 : ℕ) ≤ 0) := by omega
    rw [ite_eq_right h10]
    simp only [Nat.sub_zero, add_zero]
    exact add_comm _ _
  have hR : (∑ j ∈ Finset.range (l + 2), ∑ k ∈ Finset.range (l + 2),
        (if 1 ≤ j ∧ k + j ≤ l + 1 then V j k else 0))
      = ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1 - j), V (j + 1) k := by
    rw [Finset.sum_range_succ'
      (fun j => (∑ k ∈ Finset.range (l + 2),
        (if 1 ≤ j ∧ k + j ≤ l + 1 then V j k else 0))) (l + 1)]
    have hJ0 : (∑ k ∈ Finset.range (l + 2),
        (if 1 ≤ 0 ∧ k + 0 ≤ l + 1 then V 0 k else 0)) = 0 := by simp
    rw [hJ0, add_zero]
    exact Finset.sum_congr rfl (fun i _ => sum_shift_inner_right V l i)
  exact hL.trans hR.symm

end Work.FTS.StrongEps.H5.WlInfDthAux
