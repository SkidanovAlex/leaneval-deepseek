import Mathlib
import Submission.Work.NN.Newton.C1smallSetup
import Submission.Work.NN.Newton.C1smallSumBounds
import Submission.Work.NN.Newton.asize_le_delta_pow_div
import Submission.Work.NN.Newton.delta_pow_asize_sq_le

/-!
# Product bound for the `C^{1,α}`-small Newton iteration

Writing `A = C ε 2^{3N}` and `r = 2^{-N}`, the correction sizes satisfy
`bsize C N ε m = A r^m` (see `C1smallSumBounds`), so under the smallness
hypothesis `C ε 2^{5N} ≤ 1` one has `A ≤ 2^{-2N}` and
`∑_{i<k} bsize C N ε i ≤ 1/32`.  Hence

  `∏_{i<k} (1 + bsize C N ε i) ≤ exp (∑_{i<k} bsize C N ε i) ≤ exp (1/32) ≤ 32/31`,

which is the first component of `C1smallProdBounds`.  The other two components
are the pointwise comparisons of `asize` with `delta ^ N / C` proved in the
companion modules `asize_le_delta_pow_div` and `delta_pow_asize_sq_le`.
-/

namespace Work.NN.Newton

open Finset

/-- The product of the correction factors `1 + β_i` is at most `32/31`. -/
theorem prod_bsize_le {C ε : ℝ} {N : ℕ} (hC : 0 < C) (hN : 3 ≤ N) (hε0 : 0 ≤ ε)
    (hε : C * ε * (2:ℝ)^(5*N) ≤ 1) (k : ℕ) :
    ∏ i ∈ Finset.range k, (1 + bsize C N ε i) ≤ 32/31 := by
  obtain ⟨-, -, hb0, -, hsum, -⟩ := C1smallSumBounds hC hN hε0 hε
  have hprod : ∏ i ∈ Finset.range k, (1 + bsize C N ε i)
      ≤ Real.exp (∑ i ∈ Finset.range k, bsize C N ε i) :=
    Real.prod_one_add_le_exp_sum _ hb0
  have hexp : Real.exp (∑ i ∈ Finset.range k, bsize C N ε i) ≤ Real.exp (1/32) :=
    Real.exp_le_exp.mpr (hsum k)
  have hnum : Real.exp (1/32) ≤ 32/31 := by
    have h := Real.exp_le_two_add_div_two_sub (x := 1/32) (by norm_num) (by norm_num)
    norm_num at h ⊢
    linarith
  linarith

/-- **Bound on the correction sizes, the stage sizes and their products.**

* the product of the correction factors `1 + β_i` is at most `32/31`;
* the quadratic term of the Newton correction is dominated by the next stage size;
* every stage size is at most `δ_m^N / C`. -/
theorem C1smallProdBounds {C ε : ℝ} {N : ℕ} (hC : 0 < C) (hN : 3 ≤ N) (hε0 : 0 ≤ ε)
    (hε : C * ε * (2:ℝ)^(5*N) ≤ 1) :
    (∀ k : ℕ, ∏ i ∈ Finset.range k, (1 + bsize C N ε i) ≤ 32/31) ∧
    (∀ m : ℕ, C / delta m ^ N * (asize ε N m)^2 ≤ asize ε N (m+1)) ∧
    (∀ m : ℕ, asize ε N m ≤ delta m ^ N / C) := by
  exact ⟨fun k => prod_bsize_le hC hN hε0 hε k,
    fun m => delta_pow_asize_sq_le hC hN hε0 hε m,
    fun m => asize_le_delta_pow_div hC hN hε0 hε m⟩

end Work.NN.Newton
