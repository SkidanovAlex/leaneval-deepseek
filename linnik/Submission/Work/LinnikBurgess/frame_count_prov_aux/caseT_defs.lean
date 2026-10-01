import Mathlib
import Submission.Work.LinnikBurgess.frame_count_prov_defs
import Submission.Work.LinnikBurgess.frame_count_prov_helpers

/-!
# Helpers for the Case-T estimate (`caseT_bound`)

For the Case-T part of the frame count (`x1 ≠ x2`, both `x1` and `x2` occurring among the
entries of `b`) the second triple is a permutation of `(x1, x2, γ)` with `γ ∈ [1,H]` free.
The necessary divisibility `g ∣ contAB a b` then forces
`g ∣ |x0 - x1| * |x0 - x2| * |x0 - γ|`, and the weight becomes
`(wg x0 x1)^2 (wg x0 x2)^2 wg x0 γ`.

This file collects the bookkeeping definitions used to make that reduction precise:
`gammaSum` is the remaining sum over `γ`, and `Asum`, `Bsum` are the two building blocks of
the divisor expansion of the divisibility condition.
-/

open scoped BigOperators

namespace Work.LinnikBurgess.frame_count_prov_aux

open Classical
open Work.LinnikBurgess

/-- The sum over the free slot value `γ` in Case T. -/
noncomputable def gammaSum (H m g : ℕ) (x0 x1 x2 : ℕ) : ℝ :=
  ∑ γ ∈ Finset.Icc 1 H,
    (if γ ≠ x0 ∧ g ∣ del x0 x1 * del x0 x2 * del x0 γ then wg m x0 γ else 0)

/-- The `x`-sum of the *squares* of the weight `wg m x0 x`, over `x ≠ x0` with `e ∣ |x0 - x|`. -/
noncomputable def Asum (H m e x0 : ℕ) : ℝ :=
  ∑ x ∈ Finset.Icc 1 H, (if x ≠ x0 ∧ e ∣ del x0 x then (wg m x0 x) ^ 2 else 0)

/-- The `x`-sum of the weight `wg m x0 x`, over `x ≠ x0` with `e ∣ |x0 - x|`. -/
noncomputable def Bsum (H m e x0 : ℕ) : ℝ :=
  ∑ x ∈ Finset.Icc 1 H, (if x ≠ x0 ∧ e ∣ del x0 x then wg m x0 x else 0)

lemma gammaSum_nonneg (H m g x0 x1 x2 : ℕ) : 0 ≤ gammaSum H m g x0 x1 x2 := by
  unfold gammaSum
  refine Finset.sum_nonneg fun γ _ => ?_
  split_ifs with h
  · exact wg_nonneg m x0 γ
  · exact le_refl 0

lemma Asum_nonneg (H m e x0 : ℕ) : 0 ≤ Asum H m e x0 := by
  unfold Asum
  refine Finset.sum_nonneg fun x _ => ?_
  split_ifs with h
  · exact sq_nonneg _
  · exact le_refl 0

lemma Bsum_nonneg (H m e x0 : ℕ) : 0 ≤ Bsum H m e x0 := by
  unfold Bsum
  refine Finset.sum_nonneg fun x _ => ?_
  split_ifs with h
  · exact wg_nonneg m x0 x
  · exact le_refl 0

end Work.LinnikBurgess.frame_count_prov_aux
