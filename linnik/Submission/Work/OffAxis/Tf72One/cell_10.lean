import Mathlib
import Submission.Work.OffAxis.Tf72One.cell_3
import Submission.Work.OffAxis.Tf72One.corner_top

namespace Work.OffAxis.Tf72One

open Work.ZeroFreeTables.OffAxis

/-- One grid cell of the `s`-range on the box `t ∈ [23/5, 24/5]`: the `corner_top` bound `1/500`
at both `t`-endpoints plus the two interpolation errors give `Isub s t ≤ 1/100`. -/
private lemma cellbound10 (s t s0 s1 : ℝ) (hs0' : s0 ≤ s) (hs1' : s ≤ s1)
    (h0 : 0 ≤ s0) (h17 : s1 ≤ 17/16) (ht0 : 23/5 ≤ t) (ht1 : t ≤ 24/5)
    (hg0 : s0 ∈ ({0, 3/20, 3/10, 9/20, 3/5, 3/4, 9/10, 21/20, 17/16} : Finset ℝ))
    (hg1 : s1 ∈ ({0, 3/20, 3/10, 9/20, 3/5, 3/4, 9/10, 21/20, 17/16} : Finset ℝ))
    (hnum : (s1 - s0)^2/8*(13/10) + (24/5 - 23/5)^2/8*(5/8) ≤ 1/100 - 1/500) :
    Isub s t ≤ 1/100 := by
  have h := Isub_le_box2 s t s0 s1 (23/5) (24/5) (1/500) (1/500) (1/500) (1/500)
      hs0' hs1' ht0 ht1 h0 h17
      (corner_top s0 (23/5) hg0 (by simp)) (corner_top s0 (24/5) hg0 (by simp))
      (corner_top s1 (23/5) hg1 (by simp)) (corner_top s1 (24/5) hg1 (by simp))
  simp only [max_self] at h
  linarith [h, hnum]

/-- **HB (10.8) on the box `σ ∈ [23/5, 24/5]`.**  For `0 ≤ s ≤ 17/16` and `t ∈ [23/5, 24/5]`,
`Isub s t ≤ 1/100`.

Proof route: as in `cell_6`, with `corner_top` (`1/500`) at both endpoints; the interpolation error is
at most `0.00678`, giving `0.0088 ≤ 1/100`. -/
theorem cell_10 (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 17/16) (ht0 : 23/5 ≤ t) (ht1 : t ≤ 24/5) :
    Work.ZeroFreeTables.OffAxis.Isub s t ≤ 1/100 := by
  rcases le_or_gt s (3/20) with h1 | h1
  · exact cellbound10 s t 0 (3/20) hs0 h1 (by norm_num) (by norm_num) ht0 ht1
      (by simp) (by simp) (by norm_num)
  rcases le_or_gt s (3/10) with h2 | h2
  · exact cellbound10 s t (3/20) (3/10) (le_of_lt h1) h2 (by norm_num) (by norm_num) ht0 ht1
      (by simp) (by simp) (by norm_num)
  rcases le_or_gt s (9/20) with h3 | h3
  · exact cellbound10 s t (3/10) (9/20) (le_of_lt h2) h3 (by norm_num) (by norm_num) ht0 ht1
      (by simp) (by simp) (by norm_num)
  rcases le_or_gt s (3/5) with h4 | h4
  · exact cellbound10 s t (9/20) (3/5) (le_of_lt h3) h4 (by norm_num) (by norm_num) ht0 ht1
      (by simp) (by simp) (by norm_num)
  rcases le_or_gt s (3/4) with h5 | h5
  · exact cellbound10 s t (3/5) (3/4) (le_of_lt h4) h5 (by norm_num) (by norm_num) ht0 ht1
      (by simp) (by simp) (by norm_num)
  rcases le_or_gt s (9/10) with h6 | h6
  · exact cellbound10 s t (3/4) (9/10) (le_of_lt h5) h6 (by norm_num) (by norm_num) ht0 ht1
      (by simp) (by simp) (by norm_num)
  rcases le_or_gt s (21/20) with h7 | h7
  · exact cellbound10 s t (9/10) (21/20) (le_of_lt h6) h7 (by norm_num) (by norm_num) ht0 ht1
      (by simp) (by simp) (by norm_num)
  · exact cellbound10 s t (21/20) (17/16) (le_of_lt h7) hs1 (by norm_num) (by norm_num) ht0 ht1
      (by simp) (by simp) (by norm_num)

end Work.OffAxis.Tf72One
