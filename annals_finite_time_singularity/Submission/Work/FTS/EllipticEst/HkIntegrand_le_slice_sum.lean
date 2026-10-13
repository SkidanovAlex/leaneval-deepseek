import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-! ## Index bookkeeping for the `H^k`-integrand

The second sum of `Work.Spaces.HkIntegrand α k f z θ` runs over the pairs `(i,j)` with
`0 ≤ i, j ≤ k` and carries the indicator `if 1 ≤ i ∧ i + j ≤ k then · else 0`.  For fixed `j`
this indicator selects exactly the index set `Finset.Icc 1 (k - j)` (truncated subtraction: for
`j > k` both sets are empty), which is the `θ`-slice index set of the stated right-hand side. -/

/-- For all `i j k : ℕ`, the `i ∈ {0,…,k}` with `1 ≤ i` and `i + j ≤ k` are exactly the
integers in `Icc 1 (k - j)`. -/
lemma filter_range_succ_eq_Icc (k j : ℕ) :
    (Finset.range (k + 1)).filter (fun i => 1 ≤ i ∧ i + j ≤ k) = Finset.Icc 1 (k - j) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  omega

/-- The `if`-sum over `i ∈ range (k+1)` with indicator `1 ≤ i ∧ i + j ≤ k` is the sum over the
slice index set `Icc 1 (k-j)`. -/
lemma sum_range_ite_eq_sum_Icc (k j : ℕ) (c : ℕ → ℝ) :
    (∑ i ∈ Finset.range (k + 1), (if 1 ≤ i ∧ i + j ≤ k then c i else 0))
      = ∑ i ∈ Finset.Icc 1 (k - j), c i := by
  rw [← Finset.sum_filter]
  congr 1
  exact filter_range_succ_eq_Icc k j

/-- Pointwise decomposition of the `H^k`-integrand into the contributions of the individual
`θ`-slices: for every `z`, `θ`,

`HkIntegrand α k f z θ ≤ ∑_{j ≤ k} [ (D_z^j f z θ · w z / sin(2θ)^{η/2})²
                                   + ∑_{1 ≤ i, i+j ≤ k} (D_z^j D_θ^i f z θ · Wt α z θ)² ]`.

The left-hand side is the *sum* over the same index set (its second double sum carries the
indicator `1 ≤ i ∧ i + j ≤ k`), so this is the statement that all dropped terms are
nonnegative (in fact the two sides are equal); every square appearing is a square of a real
number.  Routine `Finset` bookkeeping: `Finset.sum_comm` to swap the two inner sums, then, for
each `j`, compare `∑ i ∈ range (k+1), if 1 ≤ i ∧ i + j ≤ k then T i j else 0` with
`∑ i ∈ Icc 1 (k-j), T i j` (the `if` selects exactly the index set `Icc 1 (k-j)` when `j ≤ k`),
using `Finset.sum_le_sum_of_subset_of_nonneg` for the inclusion
`(range (k+1)).filter (fun i => 1 ≤ i ∧ i+j ≤ k) ⊆ Icc 1 (k-j)`. -/
theorem HkIntegrand_le_slice_sum (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k f z θ
      ≤ ∑ j ∈ Finset.range (k + 1),
          ((Work.Spaces.DzIter j f z θ * (Work.Spaces.w z
                / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            + ∑ i ∈ Finset.Icc 1 (k - j),
                (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
  rw [Work.Spaces.HkIntegrand]
  rw [Finset.sum_add_distrib]
  refine add_le_add le_rfl ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun j _ => le_of_eq ?_)
  exact sum_range_ite_eq_sum_Icc k j
    (fun i => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)

end Work.FTS.EllipticEst
