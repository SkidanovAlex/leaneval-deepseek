import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.one_add_sum_pow_le
import Submission.Work.Diff.STE.one_add_zpow_le_monomialSum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `wt k ^ s ≤ C * monomialSum s k`: the weight is dominated by the Leibniz sum

`wt m = 1 + Σᵢ mᵢ²` and `monomialSum k m = Σ_{|α| ≤ k} ∏ᵢ (2π mᵢ)^{2 αᵢ}`.  Both are weights of
order `2k` in `m`, and indeed the first is bounded by a constant times the second: the point is
that `(1 + Σᵢ mᵢ²)^k` is a polynomial of degree `2k` whose monomials `∏ᵢ mᵢ^{2βᵢ}` (`|β| = k`)
are dominated by the corresponding terms of `monomialSum`, so the bound has the expected shape.

The proof splits into two independently established estimates, each of which is a strictly weaker
statement than the target:

* `one_add_sum_pow_le`  : `(1 + Σᵢ xᵢ)^k ≤ (card ι + 1)^k * (1 + Σᵢ xᵢ^k)` for `xᵢ ≥ 0`
  (Jensen/power mean for the `card ι + 1` nonnegative numbers `1, x₁, …, x_d`);
* `one_add_zpow_le_monomialSum` : `1 + Σᵢ mᵢ^{2k} ≤ (card ι + 1) * monomialSum k m`
  (the multi-indices `0` and `k·eᵢ` all occur in `monomialSum`, and all its terms are `≥ 0`).

Applying the first with `xᵢ = mᵢ²` and the second to its right-hand factor gives the claim with
`C = (card ι + 1)^{k+1}`; note that no case distinction on `k` is needed, the two estimates are
valid for `k = 0` as well.
-/

namespace Work.Diff.STE

theorem wt_pow_le_monomialSum {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ι → ℤ,
      (Work.Diff.STE.wt m) ^ k ≤ C * Work.Diff.STE.monomialSum k m := by
  classical
  refine ⟨(((Fintype.card ι : ℕ) : ℝ) + 1) ^ (k + 1), by positivity, ?_⟩
  intro m
  have hx : ∀ i : ι, 0 ≤ ((m i : ℝ)) ^ 2 := fun i => sq_nonneg _
  have h1 : (1 + ∑ i, ((m i : ℝ)) ^ 2) ^ k
      ≤ (((Fintype.card ι : ℕ) : ℝ) + 1) ^ k * (1 + ∑ i, (((m i : ℝ)) ^ 2) ^ k) :=
    one_add_sum_pow_le (fun i => ((m i : ℝ)) ^ 2) hx k
  have h2 : 1 + ∑ i, (m i : ℝ) ^ (2 * k)
      ≤ (((Fintype.card ι : ℕ) : ℝ) + 1) * monomialSum k m :=
    one_add_zpow_le_monomialSum k m
  have hsum : (∑ i, (((m i : ℝ)) ^ 2) ^ k) = ∑ i, (m i : ℝ) ^ (2 * k) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← pow_mul]
  calc (Work.Diff.STE.wt m) ^ k
      = (1 + ∑ i, ((m i : ℤ) : ℝ) ^ 2) ^ k := by rw [Work.Diff.STE.wt]
    _ ≤ (((Fintype.card ι : ℕ) : ℝ) + 1) ^ k * (1 + ∑ i, (((m i : ℝ)) ^ 2) ^ k) := h1
    _ = (((Fintype.card ι : ℕ) : ℝ) + 1) ^ k * (1 + ∑ i, (m i : ℝ) ^ (2 * k)) := by rw [hsum]
    _ ≤ (((Fintype.card ι : ℕ) : ℝ) + 1) ^ k
          * ((((Fintype.card ι : ℕ) : ℝ) + 1) * monomialSum k m) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (((Fintype.card ι : ℕ) : ℝ) + 1) ^ (k + 1) * monomialSum k m := by
        rw [pow_succ]; ring

end Work.Diff.STE
