import Submission.Work.ZeroFreeTables.OffAxis.G72Base
import Submission.Work.ZeroFreeTables.OffAxis.G72ExpBounds
import Submission.Work.ZeroFreeTables.OffAxis.G72B2bB
import Submission.Work.ZeroFreeTables.OffAxis.G72SmallSB

noncomputable section

namespace Work.ZeroFreeTables.OffAxis

open Work.ZeroFreeTables
open scoped BigOperators

/-! ## The eight `F`-method cells (HB 10.8 for `σ ≤ 51/20`, and for `s ≥ 7/10` up to `σ = 18/5`)

Each cell instantiates `G72B2b` with a left endpoint `a` (so that `2 - e^{sy} ≤ 1 - ay - (ay)^2/2`),
a right endpoint `b = 1` or the cell's right end (for the monotonicity `Isub s 0 ≤ Isub b 0`), a
rational `Y ≥ log 2 / a`, and bounds `(G72 (-b)).re` by the closed form `G72_real_closed` together
with the exponential bound `expB2b_*`. -/


theorem B2cell_1 (s σ : ℝ) (hs : (7/25 : ℝ) ≤ s) (hs2 : s ≤ (3/10 : ℝ)) (hσ : 0 ≤ σ)
    (hσ2 : σ ≤ (51/20 : ℝ)) :
    Isub s σ ≤ 16/105 := by
  have hy0 : min 2 (Real.log 2 / s) ≤ (2:ℝ) := min_le_left _ _
  have hb2 := G72B2b s σ (7/25 : ℝ) (3/10 : ℝ) (2:ℝ) (by norm_num) (by norm_num) (by norm_num)
    hs hs2 (by norm_num) hy0 (by norm_num) hσ
  have hG : (G72 (-(((3/10 : ℝ)) : ℂ))).re - 16/9 ≤ (-1333/2025 : ℝ) := by
    rw [G72_real_closed ((3/10 : ℝ)) (by norm_num)]
    have he := expB2b_3_10
    have hcoef : (0:ℝ) ≤ 4*(1-((3/10 : ℝ)))^2/(((3/10 : ℝ)))^6 := by norm_num
    have hm := mul_le_mul_of_nonneg_right he hcoef
    linarith only [hm, he]
  have hC : (∫ y in (0:ℝ)..(2:ℝ), (1 - ((7/25 : ℝ))*y - (((7/25 : ℝ))*y)^2/2) * y^2 * g72 y) = (103952/421875 : ℝ) := by
    rw [integral_weight_g72]
    norm_num
  rw [hC] at hb2
  have hstep : Isub s σ ≤ (-1333/2025 : ℝ) + (σ^2/2) * (103952/421875 : ℝ) := by linarith only [hb2, hG]
  have hCnn : (0:ℝ) ≤ (103952/421875 : ℝ) := by norm_num
  have hσs : σ^2 ≤ ((51/20 : ℝ))^2 := by nlinarith only [hσ, hσ2]
  have hmono : (σ^2/2) * (103952/421875 : ℝ) ≤ (((51/20 : ℝ))^2/2) * (103952/421875 : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hσs hCnn
    linarith only [h, hσs]
  have hfin : (-1333/2025 : ℝ) + (((51/20 : ℝ))^2/2) * (103952/421875 : ℝ) ≤ 16/105 := by norm_num
  linarith only [hstep, hmono, hfin, hb2, hG, hσs]

theorem B2cell_2 (s σ : ℝ) (hs : (3/10 : ℝ) ≤ s) (hs2 : s ≤ (7/20 : ℝ)) (hσ : 0 ≤ σ)
    (hσ2 : σ ≤ (51/20 : ℝ)) :
    Isub s σ ≤ 16/105 := by
  have hy0 : min 2 (Real.log 2 / s) ≤ (2:ℝ) := min_le_left _ _
  have hb2 := G72B2b s σ (3/10 : ℝ) (7/20 : ℝ) (2:ℝ) (by norm_num) (by norm_num) (by norm_num)
    hs hs2 (by norm_num) hy0 (by norm_num) hσ
  have hG : (G72 (-(((7/20 : ℝ)) : ℂ))).re - 16/9 ≤ (-3596624/5294205 : ℝ) := by
    rw [G72_real_closed ((7/20 : ℝ)) (by norm_num)]
    have he := expB2b_7_20
    have hcoef : (0:ℝ) ≤ 4*(1-((7/20 : ℝ)))^2/(((7/20 : ℝ)))^6 := by norm_num
    have hm := mul_le_mul_of_nonneg_right he hcoef
    linarith only [hm, he]
  have hC : (∫ y in (0:ℝ)..(2:ℝ), (1 - ((3/10 : ℝ))*y - (((3/10 : ℝ))*y)^2/2) * y^2 * g72 y) = (1336/5625 : ℝ) := by
    rw [integral_weight_g72]
    norm_num
  rw [hC] at hb2
  have hstep : Isub s σ ≤ (-3596624/5294205 : ℝ) + (σ^2/2) * (1336/5625 : ℝ) := by linarith only [hb2, hG]
  have hCnn : (0:ℝ) ≤ (1336/5625 : ℝ) := by norm_num
  have hσs : σ^2 ≤ ((51/20 : ℝ))^2 := by nlinarith only [hσ, hσ2]
  have hmono : (σ^2/2) * (1336/5625 : ℝ) ≤ (((51/20 : ℝ))^2/2) * (1336/5625 : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hσs hCnn
    linarith only [h, hσs]
  have hfin : (-3596624/5294205 : ℝ) + (((51/20 : ℝ))^2/2) * (1336/5625 : ℝ) ≤ 16/105 := by norm_num
  linarith only [hstep, hmono, hfin, hb2, hG, hσs]

theorem B2cell_3 (s σ : ℝ) (hs : (7/20 : ℝ) ≤ s) (hs2 : s ≤ (1/2 : ℝ)) (hσ : 0 ≤ σ)
    (hσ2 : σ ≤ (51/20 : ℝ)) :
    Isub s σ ≤ 16/105 := by
  have hy0 : min 2 (Real.log 2 / s) ≤ ((1981:ℝ)/1000) := by
    refine le_trans (min_le_right _ _) ?_
    have hs0 : (0:ℝ) < s := by linarith only [hs]
    rw [div_le_iff₀ hs0]
    linarith only [Real.log_two_lt_d9, hs, hs0]
  have hb2 := G72B2b s σ (7/20 : ℝ) (1/2 : ℝ) ((1981:ℝ)/1000) (by norm_num) (by norm_num) (by norm_num)
    hs hs2 (by norm_num) hy0 (by norm_num) hσ
  have hG : (G72 (-(((1/2 : ℝ)) : ℂ))).re - 16/9 ≤ (-85462/140625 : ℝ) := by
    rw [G72_real_closed ((1/2 : ℝ)) (by norm_num)]
    have he := expB2b_1_2
    have hcoef : (0:ℝ) ≤ 4*(1-((1/2 : ℝ)))^2/(((1/2 : ℝ)))^6 := by norm_num
    have hm := mul_le_mul_of_nonneg_right he hcoef
    linarith only [hm, he]
  have hC : (∫ y in (0:ℝ)..((1981:ℝ)/1000), (1 - ((7/20 : ℝ))*y - (((7/20 : ℝ))*y)^2/2) * y^2 * g72 y) = (463615988257367192392167276982710241/2160000000000000000000000000000000000 : ℝ) := by
    rw [integral_weight_g72]
    norm_num
  rw [hC] at hb2
  have hstep : Isub s σ ≤ (-85462/140625 : ℝ) + (σ^2/2) * (463615988257367192392167276982710241/2160000000000000000000000000000000000 : ℝ) := by linarith only [hb2, hG]
  have hCnn : (0:ℝ) ≤ (463615988257367192392167276982710241/2160000000000000000000000000000000000 : ℝ) := by norm_num
  have hσs : σ^2 ≤ ((51/20 : ℝ))^2 := by nlinarith only [hσ, hσ2]
  have hmono : (σ^2/2) * (463615988257367192392167276982710241/2160000000000000000000000000000000000 : ℝ) ≤ (((51/20 : ℝ))^2/2) * (463615988257367192392167276982710241/2160000000000000000000000000000000000 : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hσs hCnn
    linarith only [h, hσs]
  have hfin : (-85462/140625 : ℝ) + (((51/20 : ℝ))^2/2) * (463615988257367192392167276982710241/2160000000000000000000000000000000000 : ℝ) ≤ 16/105 := by norm_num
  linarith only [hstep, hmono, hfin, hb2, hG, hσs]

theorem B2cell_4 (s σ : ℝ) (hs : (1/2 : ℝ) ≤ s) (hs2 : s ≤ (3/5 : ℝ)) (hσ : 0 ≤ σ)
    (hσ2 : σ ≤ (51/20 : ℝ)) :
    Isub s σ ≤ 16/105 := by
  have hy0 : min 2 (Real.log 2 / s) ≤ ((1387:ℝ)/1000) := by
    refine le_trans (min_le_right _ _) ?_
    have hs0 : (0:ℝ) < s := by linarith only [hs]
    rw [div_le_iff₀ hs0]
    linarith only [Real.log_two_lt_d9, hs, hs0]
  have hb2 := G72B2b s σ (1/2 : ℝ) (3/5 : ℝ) ((1387:ℝ)/1000) (by norm_num) (by norm_num) (by norm_num)
    hs hs2 (by norm_num) hy0 (by norm_num) hσ
  have hG : (G72 (-(((3/5 : ℝ)) : ℂ))).re - 16/9 ≤ (-2167/4050 : ℝ) := by
    rw [G72_real_closed ((3/5 : ℝ)) (by norm_num)]
    have he := expB2b_3_5
    have hcoef : (0:ℝ) ≤ 4*(1-((3/5 : ℝ)))^2/(((3/5 : ℝ)))^6 := by norm_num
    have hm := mul_le_mul_of_nonneg_right he hcoef
    linarith only [hm, he]
  have hC : (∫ y in (0:ℝ)..((1387:ℝ)/1000), (1 - ((1/2 : ℝ))*y - (((1/2 : ℝ))*y)^2/2) * y^2 * g72 y) = (21620297583529080273741704525160487/151200000000000000000000000000000000 : ℝ) := by
    rw [integral_weight_g72]
    norm_num
  rw [hC] at hb2
  have hstep : Isub s σ ≤ (-2167/4050 : ℝ) + (σ^2/2) * (21620297583529080273741704525160487/151200000000000000000000000000000000 : ℝ) := by linarith only [hb2, hG]
  have hCnn : (0:ℝ) ≤ (21620297583529080273741704525160487/151200000000000000000000000000000000 : ℝ) := by norm_num
  have hσs : σ^2 ≤ ((51/20 : ℝ))^2 := by nlinarith only [hσ, hσ2]
  have hmono : (σ^2/2) * (21620297583529080273741704525160487/151200000000000000000000000000000000 : ℝ) ≤ (((51/20 : ℝ))^2/2) * (21620297583529080273741704525160487/151200000000000000000000000000000000 : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hσs hCnn
    linarith only [h, hσs]
  have hfin : (-2167/4050 : ℝ) + (((51/20 : ℝ))^2/2) * (21620297583529080273741704525160487/151200000000000000000000000000000000 : ℝ) ≤ 16/105 := by norm_num
  linarith only [hstep, hmono, hfin, hb2, hG, hσs]

theorem B2cell_5 (s σ : ℝ) (hs : (3/5 : ℝ) ≤ s) (hs2 : s ≤ (7/10 : ℝ)) (hσ : 0 ≤ σ)
    (hσ2 : σ ≤ (51/20 : ℝ)) :
    Isub s σ ≤ 16/105 := by
  have hy0 : min 2 (Real.log 2 / s) ≤ ((289:ℝ)/250) := by
    refine le_trans (min_le_right _ _) ?_
    have hs0 : (0:ℝ) < s := by linarith only [hs]
    rw [div_le_iff₀ hs0]
    linarith only [Real.log_two_lt_d9, hs, hs0]
  have hb2 := G72B2b s σ (3/5 : ℝ) (7/10 : ℝ) ((289:ℝ)/250) (by norm_num) (by norm_num) (by norm_num)
    hs hs2 (by norm_num) hy0 (by norm_num) hσ
  have hG : (G72 (-(((7/10 : ℝ)) : ℂ))).re - 16/9 ≤ (-12118882/26471025 : ℝ) := by
    rw [G72_real_closed ((7/10 : ℝ)) (by norm_num)]
    have he := expB2b_7_10
    have hcoef : (0:ℝ) ≤ 4*(1-((7/10 : ℝ)))^2/(((7/10 : ℝ)))^6 := by norm_num
    have hm := mul_le_mul_of_nonneg_right he hcoef
    linarith only [hm, he]
  have hC : (∫ y in (0:ℝ)..((289:ℝ)/250), (1 - ((3/5 : ℝ))*y - (((3/5 : ℝ))*y)^2/2) * y^2 * g72 y) = (31146492300337988195533133839/300407409667968750000000000000 : ℝ) := by
    rw [integral_weight_g72]
    norm_num
  rw [hC] at hb2
  have hstep : Isub s σ ≤ (-12118882/26471025 : ℝ) + (σ^2/2) * (31146492300337988195533133839/300407409667968750000000000000 : ℝ) := by linarith only [hb2, hG]
  have hCnn : (0:ℝ) ≤ (31146492300337988195533133839/300407409667968750000000000000 : ℝ) := by norm_num
  have hσs : σ^2 ≤ ((51/20 : ℝ))^2 := by nlinarith only [hσ, hσ2]
  have hmono : (σ^2/2) * (31146492300337988195533133839/300407409667968750000000000000 : ℝ) ≤ (((51/20 : ℝ))^2/2) * (31146492300337988195533133839/300407409667968750000000000000 : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hσs hCnn
    linarith only [h, hσs]
  have hfin : (-12118882/26471025 : ℝ) + (((51/20 : ℝ))^2/2) * (31146492300337988195533133839/300407409667968750000000000000 : ℝ) ≤ 16/105 := by norm_num
  linarith only [hstep, hmono, hfin, hb2, hG, hσs]

theorem B2cell_6 (s σ : ℝ) (hs : (7/10 : ℝ) ≤ s) (hs2 : s ≤ (4/5 : ℝ)) (hσ : 0 ≤ σ)
    (hσ2 : σ ≤ (18/5 : ℝ)) :
    Isub s σ ≤ 16/105 := by
  have hy0 : min 2 (Real.log 2 / s) ≤ ((991:ℝ)/1000) := by
    refine le_trans (min_le_right _ _) ?_
    have hs0 : (0:ℝ) < s := by linarith only [hs]
    rw [div_le_iff₀ hs0]
    linarith only [Real.log_two_lt_d9, hs, hs0]
  have hb2 := G72B2b s σ (7/10 : ℝ) (4/5 : ℝ) ((991:ℝ)/1000) (by norm_num) (by norm_num) (by norm_num)
    hs hs2 (by norm_num) hy0 (by norm_num) hσ
  have hG : (G72 (-(((4/5 : ℝ)) : ℂ))).re - 16/9 ≤ (-549721/1474560 : ℝ) := by
    rw [G72_real_closed ((4/5 : ℝ)) (by norm_num)]
    have he := expB2b_4_5
    have hcoef : (0:ℝ) ≤ 4*(1-((4/5 : ℝ)))^2/(((4/5 : ℝ)))^6 := by norm_num
    have hm := mul_le_mul_of_nonneg_right he hcoef
    linarith only [hm, he]
  have hC : (∫ y in (0:ℝ)..((991:ℝ)/1000), (1 - ((7/10 : ℝ))*y - (((7/10 : ℝ))*y)^2/2) * y^2 * g72 y) = (40634331302403016119282186200830841/540000000000000000000000000000000000 : ℝ) := by
    rw [integral_weight_g72]
    norm_num
  rw [hC] at hb2
  have hstep : Isub s σ ≤ (-549721/1474560 : ℝ) + (σ^2/2) * (40634331302403016119282186200830841/540000000000000000000000000000000000 : ℝ) := by linarith only [hb2, hG]
  have hCnn : (0:ℝ) ≤ (40634331302403016119282186200830841/540000000000000000000000000000000000 : ℝ) := by norm_num
  have hσs : σ^2 ≤ ((18/5 : ℝ))^2 := by nlinarith only [hσ, hσ2]
  have hmono : (σ^2/2) * (40634331302403016119282186200830841/540000000000000000000000000000000000 : ℝ) ≤ (((18/5 : ℝ))^2/2) * (40634331302403016119282186200830841/540000000000000000000000000000000000 : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hσs hCnn
    linarith only [h, hσs]
  have hfin : (-549721/1474560 : ℝ) + (((18/5 : ℝ))^2/2) * (40634331302403016119282186200830841/540000000000000000000000000000000000 : ℝ) ≤ 16/105 := by norm_num
  linarith only [hstep, hmono, hfin, hb2, hG, hσs]

theorem B2cell_7 (s σ : ℝ) (hs : (4/5 : ℝ) ≤ s) (hs2 : s ≤ (9/10 : ℝ)) (hσ : 0 ≤ σ)
    (hσ2 : σ ≤ (18/5 : ℝ)) :
    Isub s σ ≤ 16/105 := by
  have hy0 : min 2 (Real.log 2 / s) ≤ ((867:ℝ)/1000) := by
    refine le_trans (min_le_right _ _) ?_
    have hs0 : (0:ℝ) < s := by linarith only [hs]
    rw [div_le_iff₀ hs0]
    linarith only [Real.log_two_lt_d9, hs, hs0]
  have hb2 := G72B2b s σ (4/5 : ℝ) (9/10 : ℝ) ((867:ℝ)/1000) (by norm_num) (by norm_num) (by norm_num)
    hs hs2 (by norm_num) hy0 (by norm_num) hσ
  have hG : (G72 (-(((9/10 : ℝ)) : ℂ))).re - 16/9 ≤ (-1238762/4428675 : ℝ) := by
    rw [G72_real_closed ((9/10 : ℝ)) (by norm_num)]
    have he := expB2b_9_10
    have hcoef : (0:ℝ) ≤ 4*(1-((9/10 : ℝ)))^2/(((9/10 : ℝ)))^6 := by norm_num
    have hm := mul_le_mul_of_nonneg_right he hcoef
    linarith only [hm, he]
  have hC : (∫ y in (0:ℝ)..((867:ℝ)/1000), (1 - ((4/5 : ℝ))*y - (((4/5 : ℝ))*y)^2/2) * y^2 * g72 y) = (121234073954742346329541462381131/2187500000000000000000000000000000 : ℝ) := by
    rw [integral_weight_g72]
    norm_num
  rw [hC] at hb2
  have hstep : Isub s σ ≤ (-1238762/4428675 : ℝ) + (σ^2/2) * (121234073954742346329541462381131/2187500000000000000000000000000000 : ℝ) := by linarith only [hb2, hG]
  have hCnn : (0:ℝ) ≤ (121234073954742346329541462381131/2187500000000000000000000000000000 : ℝ) := by norm_num
  have hσs : σ^2 ≤ ((18/5 : ℝ))^2 := by nlinarith only [hσ, hσ2]
  have hmono : (σ^2/2) * (121234073954742346329541462381131/2187500000000000000000000000000000 : ℝ) ≤ (((18/5 : ℝ))^2/2) * (121234073954742346329541462381131/2187500000000000000000000000000000 : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hσs hCnn
    linarith only [h, hσs]
  have hfin : (-1238762/4428675 : ℝ) + (((18/5 : ℝ))^2/2) * (121234073954742346329541462381131/2187500000000000000000000000000000 : ℝ) ≤ 16/105 := by norm_num
  linarith only [hstep, hmono, hfin, hb2, hG, hσs]

theorem B2cell_8 (s σ : ℝ) (hs : (9/10 : ℝ) ≤ s) (hs2 : s ≤ (1/1 : ℝ)) (hσ : 0 ≤ σ)
    (hσ2 : σ ≤ (18/5 : ℝ)) :
    Isub s σ ≤ 16/105 := by
  have hy0 : min 2 (Real.log 2 / s) ≤ ((771:ℝ)/1000) := by
    refine le_trans (min_le_right _ _) ?_
    have hs0 : (0:ℝ) < s := by linarith only [hs]
    rw [div_le_iff₀ hs0]
    linarith only [Real.log_two_lt_d9, hs, hs0]
  have hb2 := G72B2b s σ (9/10 : ℝ) (1/1 : ℝ) ((771:ℝ)/1000) (by norm_num) (by norm_num) (by norm_num)
    hs hs2 (by norm_num) hy0 (by norm_num) hσ
  have hG : (G72 (-(((1/1 : ℝ)) : ℂ))).re - 16/9 ≤ (-8/45 : ℝ) := by
    rw [G72_real_closed ((1/1 : ℝ)) (by norm_num)]
    have he := expB2b_1
    have hcoef : (0:ℝ) ≤ 4*(1-((1/1 : ℝ)))^2/(((1/1 : ℝ)))^6 := by norm_num
    have hm := mul_le_mul_of_nonneg_right he hcoef
    linarith only [hm]
  have hC : (∫ y in (0:ℝ)..((771:ℝ)/1000), (1 - ((9/10 : ℝ))*y - (((9/10 : ℝ))*y)^2/2) * y^2 * g72 y) = (5825112246831040230831958367809989/140000000000000000000000000000000000 : ℝ) := by
    rw [integral_weight_g72]
    norm_num
  rw [hC] at hb2
  have hstep : Isub s σ ≤ (-8/45 : ℝ) + (σ^2/2) * (5825112246831040230831958367809989/140000000000000000000000000000000000 : ℝ) := by linarith only [hb2, hG]
  have hCnn : (0:ℝ) ≤ (5825112246831040230831958367809989/140000000000000000000000000000000000 : ℝ) := by norm_num
  have hσs : σ^2 ≤ ((18/5 : ℝ))^2 := by nlinarith only [hσ, hσ2]
  have hmono : (σ^2/2) * (5825112246831040230831958367809989/140000000000000000000000000000000000 : ℝ) ≤ (((18/5 : ℝ))^2/2) * (5825112246831040230831958367809989/140000000000000000000000000000000000 : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hσs hCnn
    linarith only [h, hσs]
  have hfin : (-8/45 : ℝ) + (((18/5 : ℝ))^2/2) * (5825112246831040230831958367809989/140000000000000000000000000000000000 : ℝ) ≤ 16/105 := by norm_num
  linarith only [hstep, hmono, hfin, hb2, hG, hσs]

end Work.ZeroFreeTables.OffAxis
end
