import Mathlib
import Submission.Work.GM.S3.prop71_defs
import Submission.Work.GM.S3.R_l2

namespace Work.GM.S3

/-- A `1`-separated finite set of reals inside `[0, M N]` has at most `2 * M N` elements, for `N ≥ 1`
(here `M N = N^{6/5} ≥ 1`). This is the crude bound `|W| ≤ 2 M N` used in GM Prop 7.1 to estimate
the `O(T^{-200})` error term.

Proof route: `Work.GM.S3.card_le_of_separated` (in `Submission/Work/GM/S3/R_l2.lean`) gives
`(W.card : ℝ) ≤ (M N - 0)/1 + 1 = M N + 1`, and `M N ≥ 1` (`Submission.LargeValues.M_ge_one`)
finishes. -/
theorem prop71_card_bound (N : ℕ) (hN : 1 ≤ N) (W : Finset ℝ)
    (hW : ∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N))
    (hsep : ∀ t ∈ W, ∀ s ∈ W, t ≠ s → 1 ≤ |t - s|) :
    (W.card : ℝ) ≤ 2 * Submission.LargeValues.M N := by
  have hM1 : (1 : ℝ) ≤ Submission.LargeValues.M N := Submission.LargeValues.M_ge_one hN
  have hM0 : (0 : ℝ) ≤ Submission.LargeValues.M N := le_trans zero_le_one hM1
  have hcard := card_le_of_separated (W := W) (a := (0 : ℝ)) (b := Submission.LargeValues.M N)
    (δ := (1 : ℝ)) one_pos hM0 (fun w hw => Set.mem_Icc.mp (hW w hw)) hsep
  rw [sub_zero, div_one] at hcard
  linarith

end Work.GM.S3
