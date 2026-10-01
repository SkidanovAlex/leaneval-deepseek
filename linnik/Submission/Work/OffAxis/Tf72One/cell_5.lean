import Mathlib
import Submission.Work.OffAxis.Tf72One.Core
import Submission.Work.OffAxis.Tf72One.Cell2Interp
import Submission.Work.OffAxis.Tf72One.corner_mid
import Submission.Work.OffAxis.Tf72One.corner_high

noncomputable section
namespace Work.OffAxis.Tf72One

open Work.ZeroFreeTables
open Work.ZeroFreeTables.OffAxis

/-- The nine-point `s`-grid `{0, 3/20, 3/10, 9/20, 3/5, 3/4, 9/10, 21/20, 17/16}` on which the
corner bounds `corner_mid` (at `σ = 7/2`) and `corner_high` (at `σ = 15/4`) are certified. -/
def cornerGrid : Finset ℝ := {0, 3/20, 3/10, 9/20, 3/5, 3/4, 9/10, 21/20, 17/16}

/-- **Corner bounds on the grid.**  For `s` in the nine-point grid, both corner values needed for
the box `σ ∈ [7/2, 15/4]` satisfy the common bound `-1/500`: at `σ = 7/2` this follows from
`corner_mid` (`Isub s (7/2) ≤ -7/200`) and at `σ = 15/4` from `corner_high` directly. -/
theorem Isub_grid_corner (s : ℝ)
    (hs : s ∈ ({0, 3/20, 3/10, 9/20, 3/5, 3/4, 9/10, 21/20, 17/16} : Finset ℝ)) :
    Work.ZeroFreeTables.OffAxis.Isub s (7/2) ≤ (-1/500 : ℝ) ∧
      Work.ZeroFreeTables.OffAxis.Isub s (15/4) ≤ (-1/500 : ℝ) :=
  ⟨le_trans (corner_mid s (7/2) hs (by norm_num)) (by norm_num),
   le_trans (corner_high s (15/4) hs (by norm_num)) (by norm_num)⟩

/-- **Box bound on `σ ∈ [7/2, 15/4]`.**  If `Isub` is at most `-1/500` at the four corners
`{s0,s1} × {7/2,15/4}` of the box, then on the box
`Isub s t ≤ -1/500 + (1/4)²/8·(5/8) + (3/20)²/8·(13/10) ≤ 1/100`.

The two interpolation lemmas `Isub_le_interp_t_cell2` (error `(t1-t0)²/8·(5/8)`) and
`Isub_le_interp_s_cell2` (error `(s1-s0)²/8·(13/10)`) are applied in the two variables. -/
theorem Isub_box_le (s t s0 s1 : ℝ) (hs0 : s0 ≤ s) (hs1 : s ≤ s1)
    (h0 : 0 ≤ s0) (h17 : s1 ≤ 17/16) (hΔ : s1 - s0 ≤ 3/20)
    (ht0 : 7/2 ≤ t) (ht1 : t ≤ 15/4)
    (hA : Work.ZeroFreeTables.OffAxis.Isub s0 (7/2) ≤ (-1/500 : ℝ))
    (hB : Work.ZeroFreeTables.OffAxis.Isub s0 (15/4) ≤ (-1/500 : ℝ))
    (hC : Work.ZeroFreeTables.OffAxis.Isub s1 (7/2) ≤ (-1/500 : ℝ))
    (hD : Work.ZeroFreeTables.OffAxis.Isub s1 (15/4) ≤ (-1/500 : ℝ)) :
    Work.ZeroFreeTables.OffAxis.Isub s t ≤ 1/100 := by
  have hs1' : 0 ≤ s1 := le_trans h0 (le_trans hs0 hs1)
  have hs017 : s0 ≤ 17/16 := le_trans hs0 (le_trans hs1 h17)
  have hSt := Isub_le_interp_s_cell2 s t s0 s1 hs0 hs1 h0 h17
  have h0t := Isub_le_interp_t_cell2 s0 t (7/2) (15/4) h0 hs017 ht0 ht1
  have h1t := Isub_le_interp_t_cell2 s1 t (7/2) (15/4) hs1' h17 ht0 ht1
  have hmax0 : max (Isub s0 (7/2)) (Isub s0 (15/4)) ≤ (-1/500 : ℝ) := max_le hA hB
  have hmax1 : max (Isub s1 (7/2)) (Isub s1 (15/4)) ≤ (-1/500 : ℝ) := max_le hC hD
  have hm0 : Isub s0 t ≤ (-1/500 : ℝ) + (15/4 - 7/2) ^ 2 / 8 * (5/8) := by linarith
  have hm1 : Isub s1 t ≤ (-1/500 : ℝ) + (15/4 - 7/2) ^ 2 / 8 * (5/8) := by linarith
  have hm : max (Isub s0 t) (Isub s1 t)
      ≤ (-1/500 : ℝ) + (15/4 - 7/2) ^ 2 / 8 * (5/8) := max_le hm0 hm1
  have hΔ2 : (s1 - s0) ^ 2 / 8 * (13/10) ≤ (3/20 : ℝ) ^ 2 / 8 * (13/10) := by
    have h : 0 ≤ s1 - s0 := by linarith
    have h3 : (0:ℝ) ≤ 3/20 := by norm_num
    have hsq : (s1 - s0) ^ 2 ≤ (3/20 : ℝ) ^ 2 := by nlinarith
    linarith
  have hnum : (-1/500 : ℝ) + (15/4 - 7/2) ^ 2 / 8 * (5/8) + (3/20 : ℝ) ^ 2 / 8 * (13/10)
      ≤ 1/100 := by norm_num
  linarith

/-- **HB (10.8) on the box `σ ∈ [7/2, 15/4]`.**  For `0 ≤ s ≤ 17/16` and `t ∈ [7/2, 15/4]`,
`Isub s t ≤ 1/100`.

Proof route: as in `cell_0`, with `corner_mid` at `t = 7/2` (`-7/200`) and `corner_high` at
`t = 15/4` (`-1/500`); the maximum corner bound is `-1/500 = -0.002` and the error at most `0.00854`,
giving `0.0065 ≤ 1/100`. -/
theorem cell_5 (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 17/16) (ht0 : 7/2 ≤ t) (ht1 : t ≤ 15/4) :
    Work.ZeroFreeTables.OffAxis.Isub s t ≤ 1/100 := by
  -- assembles the four corner bounds of a cell with `Isub_box_le`
  have cell : ∀ s0 s1 : ℝ,
      s0 ∈ ({0, 3/20, 3/10, 9/20, 3/5, 3/4, 9/10, 21/20, 17/16} : Finset ℝ) →
      s1 ∈ ({0, 3/20, 3/10, 9/20, 3/5, 3/4, 9/10, 21/20, 17/16} : Finset ℝ) →
      s0 ≤ s → s ≤ s1 → 0 ≤ s0 → s1 ≤ 17/16 → s1 - s0 ≤ 3/20 →
      Work.ZeroFreeTables.OffAxis.Isub s t ≤ 1/100 := by
    intro s0 s1 hm0 hm1 ha hb h0 h17 hδ
    obtain ⟨hA, hB⟩ := Isub_grid_corner s0 hm0
    obtain ⟨hC, hD⟩ := Isub_grid_corner s1 hm1
    exact Isub_box_le s t s0 s1 ha hb h0 h17 hδ ht0 ht1 hA hB hC hD
  rcases le_or_gt s (3/20) with h1 | h1
  · exact cell 0 (3/20) (by norm_num) (by norm_num) hs0 h1 (by norm_num) (by norm_num) (by norm_num)
  · rcases le_or_gt s (3/10) with h2 | h2
    · exact cell (3/20) (3/10) (by norm_num) (by norm_num) (le_of_lt h1) h2
        (by norm_num) (by norm_num) (by norm_num)
    · rcases le_or_gt s (9/20) with h3 | h3
      · exact cell (3/10) (9/20) (by norm_num) (by norm_num) (le_of_lt h2) h3
          (by norm_num) (by norm_num) (by norm_num)
      · rcases le_or_gt s (3/5) with h4 | h4
        · exact cell (9/20) (3/5) (by norm_num) (by norm_num) (le_of_lt h3) h4
            (by norm_num) (by norm_num) (by norm_num)
        · rcases le_or_gt s (3/4) with h5 | h5
          · exact cell (3/5) (3/4) (by norm_num) (by norm_num) (le_of_lt h4) h5
              (by norm_num) (by norm_num) (by norm_num)
          · rcases le_or_gt s (9/10) with h6 | h6
            · exact cell (3/4) (9/10) (by norm_num) (by norm_num) (le_of_lt h5) h6
                (by norm_num) (by norm_num) (by norm_num)
            · rcases le_or_gt s (21/20) with h7 | h7
              · exact cell (9/10) (21/20) (by norm_num) (by norm_num) (le_of_lt h6) h7
                  (by norm_num) (by norm_num) (by norm_num)
              · exact cell (21/20) (17/16) (by norm_num) (by norm_num) (le_of_lt h7) hs1
                  (by norm_num) (by norm_num) (by norm_num)

end Work.OffAxis.Tf72One
