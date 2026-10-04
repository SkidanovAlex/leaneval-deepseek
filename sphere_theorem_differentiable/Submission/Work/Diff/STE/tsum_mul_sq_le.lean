import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Weighted Cauchy–Schwarz for `tsum`

For nonnegative weights `w` and nonnegative values `f`, with `∑ w` and `∑ w f²` summable:

  `(∑' i, w i * f i)^2 ≤ (∑' i, w i) * (∑' i, w i * f i^2)`.

This is Cauchy–Schwarz applied pointwise on each finite set of indices, where
`w i * f i = √(w i) · (√(w i) · f i)`, followed by passage to the limit along the
directed net of finite sets.  The finiteness of the two factors is exactly the two
summability hypotheses; the middle series `∑' i, w i * f i` is summable by comparison
with `∑ (w i + w i * f i^2)` since `f i ≤ 1 + f i^2` for `f i ≥ 0`.
-/

namespace Work.Diff.STE

open Filter

theorem tsum_mul_sq_le {α : Type*} (w f : α → ℝ) (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i)
    (hw' : Summable w) (hf' : Summable fun i => w i * f i ^ 2) :
    (∑' i, w i * f i) ^ 2 ≤ (∑' i, w i) * (∑' i, w i * f i ^ 2) := by
  -- Step 1: the cross term `∑' i, w i * f i` is summable.
  have hsum : Summable fun i => w i * f i := by
    refine Summable.of_nonneg_of_le (fun i => mul_nonneg (hw i) (hf i)) (fun i => ?_)
      (hw'.add hf')
    have hle : f i ≤ 1 + f i ^ 2 := by nlinarith [sq_nonneg (f i - 1), hf i]
    calc w i * f i ≤ w i * (1 + f i ^ 2) := mul_le_mul_of_nonneg_left hle (hw i)
      _ = w i + w i * f i ^ 2 := by ring
  have hbnn : ∀ i, 0 ≤ w i * f i ^ 2 := fun i => mul_nonneg (hw i) (sq_nonneg (f i))
  -- Step 2: the inequality for every finite set of indices, with the right-hand side
  -- already replaced by the full (infinite) sums.
  have key : ∀ t : Finset α, (∑ i ∈ t, w i * f i) ^ 2
      ≤ (∑' i, w i) * (∑' i, w i * f i ^ 2) := by
    intro t
    have h1 : (∑ i ∈ t, w i * f i) ^ 2 ≤ (∑ i ∈ t, w i) * ∑ i ∈ t, w i * f i ^ 2 :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul t (fun i _ => hw i) (fun i _ => hbnn i)
        (fun i _ => le_of_eq (by ring))
    calc (∑ i ∈ t, w i * f i) ^ 2
        ≤ (∑ i ∈ t, w i) * ∑ i ∈ t, w i * f i ^ 2 := h1
      _ ≤ (∑' i, w i) * (∑' i, w i * f i ^ 2) := by
          refine mul_le_mul (Summable.sum_le_tsum t (fun i _ => hw i) hw')
            (Summable.sum_le_tsum t (fun i _ => hbnn i) hf') ?_ ?_
          · exact Finset.sum_nonneg (fun i _ => hbnn i)
          · exact tsum_nonneg hw
  -- Step 3: pass to the limit along the net of finite sets.
  have hlim : Tendsto (fun t : Finset α => (∑ i ∈ t, w i * f i) ^ 2) atTop
      (nhds ((∑' i, w i * f i) ^ 2)) := by
    have hh := hsum.hasSum
    simp only [HasSum, SummationFilter.unconditional_filter] at hh
    exact hh.pow 2
  exact le_of_tendsto' hlim key

end Work.Diff.STE
