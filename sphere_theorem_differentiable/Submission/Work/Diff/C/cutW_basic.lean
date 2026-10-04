import Mathlib
import Submission.Work.Diff.C.cutoff_psi_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Basic pointwise properties of the transition profile `cutW`

`cutW u = (3/2) * smoothTransition (2u) - (1/2) * smoothTransition (2u - 1)`, where
`smoothTransition` is `0` on `(-∞,0]`, `1` on `[1,∞)`, monotone and takes values in `[0,1]`.
Hence `cutW` vanishes on `(-∞,0]`, equals `1` on `[1,∞)`, and is nonnegative; moreover
`cutW u ≤ 3/2 ≤ 2` since `3/2 * smoothTransition (2u) ≤ 3/2`.
-/

namespace Work.Diff.C

/-- `cutW` vanishes on `(-∞,0]`. -/
lemma cutW_eq_zero_of_nonpos {u : ℝ} (hu : u ≤ 0) : cutW u = 0 := by
  simp only [cutW]
  rw [Real.smoothTransition.zero_of_nonpos (show 2 * u ≤ 0 by linarith),
    Real.smoothTransition.zero_of_nonpos (show 2 * u - 1 ≤ 0 by linarith)]
  ring

/-- `cutW` equals `1` on `[1,∞)`. -/
lemma cutW_eq_one_of_one_le {u : ℝ} (hu : 1 ≤ u) : cutW u = 1 := by
  simp only [cutW]
  rw [Real.smoothTransition.one_of_one_le (show (1 : ℝ) ≤ 2 * u by linarith),
    Real.smoothTransition.one_of_one_le (show (1 : ℝ) ≤ 2 * u - 1 by linarith)]
  norm_num

/-- `cutW` is nonnegative: `smoothTransition (2u-1) ≤ smoothTransition (2u)`, so
`cutW u ≥ 3/2 * st(2u-1) - 1/2 * st(2u-1) = st(2u-1) ≥ 0`. -/
lemma cutW_nonneg (u : ℝ) : 0 ≤ cutW u := by
  have hmono : Real.smoothTransition (2 * u - 1) ≤ Real.smoothTransition (2 * u) :=
    Real.smoothTransition.monotone (by linarith)
  have h0 : 0 ≤ Real.smoothTransition (2 * u - 1) := Real.smoothTransition.nonneg _
  simp only [cutW]
  nlinarith

/-- `cutW u ≤ 2`: the first term is at most `3/2` and the second at least `0`. -/
lemma cutW_le_two (u : ℝ) : cutW u ≤ 2 := by
  have h1 : Real.smoothTransition (2 * u) ≤ 1 := Real.smoothTransition.le_one _
  have h0 : 0 ≤ Real.smoothTransition (2 * u - 1) := Real.smoothTransition.nonneg _
  simp only [cutW]
  linarith

theorem cutW_basic :
    (∀ u : ℝ, u ≤ 0 → cutW u = 0) ∧ (∀ u : ℝ, 1 ≤ u → cutW u = 1) ∧
      (∀ u : ℝ, 0 ≤ cutW u) ∧ (∀ u : ℝ, cutW u ≤ 2) :=
  ⟨fun _ hu => cutW_eq_zero_of_nonpos hu, fun _ hu => cutW_eq_one_of_one_le hu,
    cutW_nonneg, cutW_le_two⟩

end Work.Diff.C
