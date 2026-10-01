import Submission.Work.ZeroFreeTables.OffAxis.G72Base
import Submission.Work.ZeroFreeTables.OffAxis.G72SigmaLipB
import Submission.Work.ZeroFreeTables.OffAxis.G72ExpBounds
import Submission.Work.ZeroFreeTables.OffAxis.G72Signs
import Submission.Work.ZeroFreeTables.OffAxis.G72GridCells

noncomputable section

namespace Work.ZeroFreeTables.OffAxis

open Work.ZeroFreeTables
open scoped BigOperators

/-! ## The grid lemma

Any `(s,σ)` within `3/40` of a grid centre is bounded, using the `s`- and `σ`-Lipschitz bounds. -/

lemma grid_cell_bound (s0 σ0 s σ : ℝ) (hs : 7/25 ≤ s) (hs1 : s ≤ 1)
    (hs0le : s0 ≤ 1) (hs0 : |s - s0| ≤ 3/40) (hσ0 : |σ - σ0| ≤ 3/40)
    (hcenter : Isub s0 σ0 ≤ -1/12) :
    Isub s σ ≤ 16/105 := by
  have hs0pos : 0 ≤ s0 := by
    have h := (abs_le.mp hs0).2
    linarith
  have h1 : |Isub s σ - Isub s σ0| ≤ (208/105) * |σ - σ0| := G72SigmaLip s σ σ0 (by linarith) hs1
  have h2 : |Isub s σ0 - Isub s0 σ0| ≤ (16/15) * |s - s0| :=
    abs_Isub_sub_le_s s s0 σ0 (by linarith) hs0pos hs1 hs0le
  have hstep : Isub s σ ≤ Isub s0 σ0 + (208/105)*(3/40) + (16/15)*(3/40) := by
    have h1' := (abs_le.mp h1).2
    have h2' := (abs_le.mp h2).2
    have h4 : (208/105) * |σ - σ0| ≤ (208/105)*(3/40) :=
      mul_le_mul_of_nonneg_left hσ0 (by norm_num)
    have h5 : (16/15) * |s - s0| ≤ (16/15)*(3/40) :=
      mul_le_mul_of_nonneg_left hs0 (by norm_num)
    linarith [h1', h2', h4, h5]
  linarith [hstep, hcenter]

/-- **The grid lemma**: for `7/25 ≤ s ≤ 73/100` and `51/20 ≤ σ ≤ 18/5`, `Isub s σ ≤ 16/105`. -/
theorem grid_main (s σ : ℝ) (hs : 7/25 ≤ s) (hs1 : s ≤ 73/100)
    (hσ : 51/20 ≤ σ) (hσ1 : σ ≤ 18/5) :
    Isub s σ ≤ 16/105 := by

  rcases le_or_gt s (43/100) with hsa | hsa
  · have hsa' : s ≤ (43:ℝ)/100 := hsa
    rcases le_or_gt σ (27/10) with hg0 | hg0
    · -- σ in [51/20, 27/10]
      refine grid_cell_bound (71/200) (21/8) s σ hs (by linarith) (by norm_num) ?_ ?_ ?_
      · rw [abs_le]; constructor <;> linarith
      · rw [abs_le]; constructor <;> linarith
      · exact gridCell_0_0 gridE_71_200 cos_pos_21_8 sin_neg_21_8
    · have hgj0 : (27/10 : ℝ) < σ := hg0
      rcases le_or_gt σ (57/20) with hg1 | hg1
      · -- σ in [27/10, 57/20]
        refine grid_cell_bound (71/200) (111/40) s σ hs (by linarith) (by norm_num) ?_ ?_ ?_
        · rw [abs_le]; constructor <;> linarith
        · rw [abs_le]; constructor <;> linarith
        · exact gridCell_0_1 gridE_71_200 cos_pos_111_40 sin_neg_111_40
      · have hgj1 : (57/20 : ℝ) < σ := hg1
        rcases le_or_gt σ (3) with hg2 | hg2
        · -- σ in [57/20, 3]
          refine grid_cell_bound (71/200) (117/40) s σ hs (by linarith) (by norm_num) ?_ ?_ ?_
          · rw [abs_le]; constructor <;> linarith
          · rw [abs_le]; constructor <;> linarith
          · exact gridCell_0_2 gridE_71_200 cos_pos_117_40 sin_neg_117_40
        · have hgj2 : (3 : ℝ) < σ := hg2
          rcases le_or_gt σ (63/20) with hg3 | hg3
          · -- σ in [3, 63/20]
            refine grid_cell_bound (71/200) (123/40) s σ hs (by linarith) (by norm_num) ?_ ?_ ?_
            · rw [abs_le]; constructor <;> linarith
            · rw [abs_le]; constructor <;> linarith
            · exact gridCell_0_3 gridE_71_200 cos_pos_123_40 sin_neg_123_40
          · have hgj3 : (63/20 : ℝ) < σ := hg3
            rcases le_or_gt σ (33/10) with hg4 | hg4
            · -- σ in [63/20, 33/10]
              refine grid_cell_bound (71/200) (129/40) s σ hs (by linarith) (by norm_num) ?_ ?_ ?_
              · rw [abs_le]; constructor <;> linarith
              · rw [abs_le]; constructor <;> linarith
              · exact gridCell_0_4 gridE_71_200 cos_pos_129_40 sin_pos_129_40
            · have hgj4 : (33/10 : ℝ) < σ := hg4
              rcases le_or_gt σ (69/20) with hg5 | hg5
              · -- σ in [33/10, 69/20]
                refine grid_cell_bound (71/200) (27/8) s σ hs (by linarith) (by norm_num) ?_ ?_ ?_
                · rw [abs_le]; constructor <;> linarith
                · rw [abs_le]; constructor <;> linarith
                · exact gridCell_0_5 gridE_71_200 cos_pos_27_8 sin_pos_27_8
              · have hgj5 : (69/20 : ℝ) < σ := hg5
                refine grid_cell_bound (71/200) (141/40) s σ hs (by linarith) (by norm_num) ?_ ?_ ?_
                · rw [abs_le]; constructor <;> linarith
                · rw [abs_le]; constructor <;> linarith
                · exact gridCell_0_6 gridE_71_200 cos_half_141_40 sin_half_141_40
  · have hsa' : (43:ℝ)/100 < s := hsa
    rcases le_or_gt s (29/50) with hsb | hsb
    · have hsb' : s ≤ (29:ℝ)/50 := hsb
      rcases le_or_gt σ (27/10) with hg0 | hg0
      · -- σ in [51/20, 27/10]
        refine grid_cell_bound (101/200) (21/8) s σ hs (by linarith) (by norm_num) ?_ ?_ ?_
        · rw [abs_le]; constructor <;> linarith
        · rw [abs_le]; constructor <;> linarith
        · exact gridCell_1_0 gridE_101_200 cos_pos_21_8 sin_neg_21_8
      · have hgj0 : (27/10 : ℝ) < σ := hg0
        rcases le_or_gt σ (57/20) with hg1 | hg1
        · -- σ in [27/10, 57/20]
          refine grid_cell_bound (101/200) (111/40) s σ hs (by linarith) (by norm_num) ?_ ?_ ?_
          · rw [abs_le]; constructor <;> linarith
          · rw [abs_le]; constructor <;> linarith
          · exact gridCell_1_1 gridE_101_200 cos_pos_111_40 sin_neg_111_40
        · have hgj1 : (57/20 : ℝ) < σ := hg1
          rcases le_or_gt σ (3) with hg2 | hg2
          · -- σ in [57/20, 3]
            refine grid_cell_bound (101/200) (117/40) s σ hs (by linarith) (by norm_num) ?_ ?_ ?_
            · rw [abs_le]; constructor <;> linarith
            · rw [abs_le]; constructor <;> linarith
            · exact gridCell_1_2 gridE_101_200 cos_pos_117_40 sin_neg_117_40
          · have hgj2 : (3 : ℝ) < σ := hg2
            rcases le_or_gt σ (63/20) with hg3 | hg3
            · -- σ in [3, 63/20]
              refine grid_cell_bound (101/200) (123/40) s σ hs (by linarith) (by norm_num) ?_ ?_ ?_
              · rw [abs_le]; constructor <;> linarith
              · rw [abs_le]; constructor <;> linarith
              · exact gridCell_1_3 gridE_101_200 cos_pos_123_40 sin_neg_123_40
            · have hgj3 : (63/20 : ℝ) < σ := hg3
              rcases le_or_gt σ (33/10) with hg4 | hg4
              · -- σ in [63/20, 33/10]
                refine grid_cell_bound (101/200) (129/40) s σ hs (by linarith) (by norm_num) ?_ ?_ ?_
                · rw [abs_le]; constructor <;> linarith
                · rw [abs_le]; constructor <;> linarith
                · exact gridCell_1_4 gridE_101_200 cos_pos_129_40 sin_pos_129_40
              · have hgj4 : (33/10 : ℝ) < σ := hg4
                rcases le_or_gt σ (69/20) with hg5 | hg5
                · -- σ in [33/10, 69/20]
                  refine grid_cell_bound (101/200) (27/8) s σ hs (by linarith) (by norm_num) ?_ ?_ ?_
                  · rw [abs_le]; constructor <;> linarith
                  · rw [abs_le]; constructor <;> linarith
                  · exact gridCell_1_5 gridE_101_200 cos_pos_27_8 sin_pos_27_8
                · have hgj5 : (69/20 : ℝ) < σ := hg5
                  refine grid_cell_bound (101/200) (141/40) s σ hs (by linarith) (by norm_num) ?_ ?_ ?_
                  · rw [abs_le]; constructor <;> linarith
                  · rw [abs_le]; constructor <;> linarith
                  · exact gridCell_1_6 gridE_101_200 cos_half_141_40 sin_half_141_40
    · have hsb' : (29:ℝ)/50 < s := hsb
      rcases le_or_gt σ (27/10) with hg0 | hg0
      · -- σ in [51/20, 27/10]
        refine grid_cell_bound (131/200) (21/8) s σ hs (by linarith) (by norm_num) ?_ ?_ ?_
        · rw [abs_le]; constructor <;> linarith
        · rw [abs_le]; constructor <;> linarith
        · exact gridCell_2_0 gridE_131_200 cos_pos_21_8 sin_neg_21_8
      · have hgj0 : (27/10 : ℝ) < σ := hg0
        rcases le_or_gt σ (57/20) with hg1 | hg1
        · -- σ in [27/10, 57/20]
          refine grid_cell_bound (131/200) (111/40) s σ hs (by linarith) (by norm_num) ?_ ?_ ?_
          · rw [abs_le]; constructor <;> linarith
          · rw [abs_le]; constructor <;> linarith
          · exact gridCell_2_1 gridE_131_200 cos_pos_111_40 sin_neg_111_40
        · have hgj1 : (57/20 : ℝ) < σ := hg1
          rcases le_or_gt σ (3) with hg2 | hg2
          · -- σ in [57/20, 3]
            refine grid_cell_bound (131/200) (117/40) s σ hs (by linarith) (by norm_num) ?_ ?_ ?_
            · rw [abs_le]; constructor <;> linarith
            · rw [abs_le]; constructor <;> linarith
            · exact gridCell_2_2 gridE_131_200 cos_pos_117_40 sin_neg_117_40
          · have hgj2 : (3 : ℝ) < σ := hg2
            rcases le_or_gt σ (63/20) with hg3 | hg3
            · -- σ in [3, 63/20]
              refine grid_cell_bound (131/200) (123/40) s σ hs (by linarith) (by norm_num) ?_ ?_ ?_
              · rw [abs_le]; constructor <;> linarith
              · rw [abs_le]; constructor <;> linarith
              · exact gridCell_2_3 gridE_131_200 cos_pos_123_40 sin_neg_123_40
            · have hgj3 : (63/20 : ℝ) < σ := hg3
              rcases le_or_gt σ (33/10) with hg4 | hg4
              · -- σ in [63/20, 33/10]
                refine grid_cell_bound (131/200) (129/40) s σ hs (by linarith) (by norm_num) ?_ ?_ ?_
                · rw [abs_le]; constructor <;> linarith
                · rw [abs_le]; constructor <;> linarith
                · exact gridCell_2_4 gridE_131_200 cos_pos_129_40 sin_pos_129_40
              · have hgj4 : (33/10 : ℝ) < σ := hg4
                rcases le_or_gt σ (69/20) with hg5 | hg5
                · -- σ in [33/10, 69/20]
                  refine grid_cell_bound (131/200) (27/8) s σ hs (by linarith) (by norm_num) ?_ ?_ ?_
                  · rw [abs_le]; constructor <;> linarith
                  · rw [abs_le]; constructor <;> linarith
                  · exact gridCell_2_5 gridE_131_200 cos_pos_27_8 sin_pos_27_8
                · have hgj5 : (69/20 : ℝ) < σ := hg5
                  refine grid_cell_bound (131/200) (141/40) s σ hs (by linarith) (by norm_num) ?_ ?_ ?_
                  · rw [abs_le]; constructor <;> linarith
                  · rw [abs_le]; constructor <;> linarith
                  · exact gridCell_2_6 gridE_131_200 cos_half_141_40 sin_half_141_40

end Work.ZeroFreeTables.OffAxis
end
