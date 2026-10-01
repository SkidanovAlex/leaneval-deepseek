import Mathlib
import Submission.Work.OffAxis.Tf72One.Box
import Submission.Work.OffAxis.Tf72One.corner_low
import Submission.Work.OffAxis.Tf72One.corner_mid
import Submission.Work.OffAxis.Tf72One.Cell2Interp

noncomputable section

namespace Work.OffAxis.Tf72One

open Work.ZeroFreeTables Work.ZeroFreeTables.OffAxis

/-- **Box bound from corner bounds** (sorry-free analogue of `Isub_le_box`, using the
interpolation lemmas `Isub_le_interp_s_cell2` / `Isub_le_interp_t_cell2`). -/
theorem Isub_le_box_cell2 (s t s0 s1 t0 t1 B00 B01 B10 B11 : ℝ)
    (hs0 : s0 ≤ s) (hs1 : s ≤ s1) (ht0 : t0 ≤ t) (ht1 : t ≤ t1)
    (h0 : 0 ≤ s0) (h17 : s1 ≤ 17/16)
    (h00 : Isub s0 t0 ≤ B00) (h01 : Isub s0 t1 ≤ B01)
    (h10 : Isub s1 t0 ≤ B10) (h11 : Isub s1 t1 ≤ B11) :
    Isub s t ≤ max (max B00 B01) (max B10 B11)
      + (s1 - s0) ^ 2 / 8 * (13/10) + (t1 - t0) ^ 2 / 8 * (5/8) := by
  have hs1' : 0 ≤ s1 := le_trans h0 (le_trans hs0 hs1)
  have hs017 : s0 ≤ 17/16 := le_trans hs0 (le_trans hs1 h17)
  have hIs := Isub_le_interp_s_cell2 s t s0 s1 hs0 hs1 h0 h17
  have h0t := Isub_le_interp_t_cell2 s0 t t0 t1 h0 hs017 ht0 ht1
  have h1t := Isub_le_interp_t_cell2 s1 t t0 t1 hs1' h17 ht0 ht1
  have hmax0 : max (Isub s0 t0) (Isub s0 t1) ≤ max B00 B01 := max_le_max h00 h01
  have hmax1 : max (Isub s1 t0) (Isub s1 t1) ≤ max B10 B11 := max_le_max h10 h11
  have h0t' : Isub s0 t ≤ max (max B00 B01) (max B10 B11) + (t1 - t0) ^ 2 / 8 * (5/8) := by
    have hle : max B00 B01 ≤ max (max B00 B01) (max B10 B11) := le_max_left _ _
    linarith [h0t, hmax0, hle]
  have h1t' : Isub s1 t ≤ max (max B00 B01) (max B10 B11) + (t1 - t0) ^ 2 / 8 * (5/8) := by
    have hle : max B10 B11 ≤ max (max B00 B01) (max B10 B11) := le_max_right _ _
    linarith [h1t, hmax1, hle]
  have hmax : max (Isub s0 t) (Isub s1 t)
      ≤ max (max B00 B01) (max B10 B11) + (t1 - t0) ^ 2 / 8 * (5/8) := max_le h0t' h1t'
  linarith [hIs, hmax]

/-- One grid cell of the `s`-range for the box `t ∈ [5/2, 3]`: the corner bounds
`-193/1000` at `t = 5/2` (`corner_low`) and `-7/200` at `t = 3` (`corner_mid`), together with the
two interpolation errors, give `Isub s t ≤ 1/100`. -/
private lemma cell2bound (s t s0 s1 : ℝ) (hs0' : s0 ≤ s) (hs1' : s ≤ s1)
    (h0 : 0 ≤ s0) (h17 : s1 ≤ 17/16) (ht0 : 5/2 ≤ t) (ht1 : t ≤ 3)
    (hg0 : s0 ∈ ({0, 3/20, 3/10, 9/20, 3/5, 3/4, 9/10, 21/20, 17/16} : Finset ℝ))
    (hg1 : s1 ∈ ({0, 3/20, 3/10, 9/20, 3/5, 3/4, 9/10, 21/20, 17/16} : Finset ℝ))
    (hnum : (s1 - s0)^2/8*(13/10) + (3 - 5/2)^2/8*(5/8) ≤ 1/100 + 7/200) :
    Isub s t ≤ 1/100 := by
  have h := Isub_le_box_cell2 s t s0 s1 (5/2) 3 (-193/1000) (-7/200) (-193/1000) (-7/200)
      hs0' hs1' ht0 ht1 h0 h17
      (corner_low s0 (5/2) hg0 (by simp)) (corner_mid s0 3 hg0 (by simp))
      (corner_low s1 (5/2) hg1 (by simp)) (corner_mid s1 3 hg1 (by simp))
  have hmax : max (max (-193/1000) (-7/200)) (max (-193/1000) (-7/200)) = (-7/200 : ℝ) := by
    norm_num
  rw [hmax] at h
  linarith [h, hnum]

/-- **HB (10.8) on the box `σ ∈ [5/2, 3]`.**  For `0 ≤ s ≤ 17/16` and `t ∈ [5/2, 3]`,
`Isub s t ≤ 1/100`.

Proof route: as in `cell_0`, with `corner_low` at `t = 5/2` (`-193/1000`) and `corner_mid` at `t = 3`
(`-7/200`); the maximum corner bound is `-7/200` and the interpolation error at most
`(3/20)²/8·(13/10) + (1/2)²/8·(5/8) = 0.0232`, giving `-0.0118 ≤ 1/100`. -/
theorem cell_2 (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 17/16) (ht0 : 5/2 ≤ t) (ht1 : t ≤ 3) :
    Work.ZeroFreeTables.OffAxis.Isub s t ≤ 1/100 := by
  rcases le_or_gt s (3/20) with h1 | h1
  · exact cell2bound s t 0 (3/20) hs0 h1 (by norm_num) (by norm_num) ht0 ht1
      (by simp) (by simp) (by norm_num)
  rcases le_or_gt s (3/10) with h2 | h2
  · exact cell2bound s t (3/20) (3/10) (le_of_lt h1) h2 (by norm_num) (by norm_num) ht0 ht1
      (by simp) (by simp) (by norm_num)
  rcases le_or_gt s (9/20) with h3 | h3
  · exact cell2bound s t (3/10) (9/20) (le_of_lt h2) h3 (by norm_num) (by norm_num) ht0 ht1
      (by simp) (by simp) (by norm_num)
  rcases le_or_gt s (3/5) with h4 | h4
  · exact cell2bound s t (9/20) (3/5) (le_of_lt h3) h4 (by norm_num) (by norm_num) ht0 ht1
      (by simp) (by simp) (by norm_num)
  rcases le_or_gt s (3/4) with h5 | h5
  · exact cell2bound s t (3/5) (3/4) (le_of_lt h4) h5 (by norm_num) (by norm_num) ht0 ht1
      (by simp) (by simp) (by norm_num)
  rcases le_or_gt s (9/10) with h6 | h6
  · exact cell2bound s t (3/4) (9/10) (le_of_lt h5) h6 (by norm_num) (by norm_num) ht0 ht1
      (by simp) (by simp) (by norm_num)
  rcases le_or_gt s (21/20) with h7 | h7
  · exact cell2bound s t (9/10) (21/20) (le_of_lt h6) h7 (by norm_num) (by norm_num) ht0 ht1
      (by simp) (by simp) (by norm_num)
  · exact cell2bound s t (21/20) (17/16) (le_of_lt h7) hs1 (by norm_num) (by norm_num) ht0 ht1
      (by simp) (by simp) (by norm_num)

end Work.OffAxis.Tf72One
