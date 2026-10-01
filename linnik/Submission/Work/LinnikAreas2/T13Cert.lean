import Mathlib
import Submission.Work.LinnikAreas.Density4.T13.Basic
import Submission.Work.LinnikAreas.Density4.T13.Num1
import Submission.Work.LinnikAreas.Density4.T13.Num2
import Submission.Work.LinnikAreas.Density4.T13.Num3
import Submission.Work.LinnikAreas.Density4.T13.Num4
import Submission.Work.LinnikAreas2.T13SideDefs
import Submission.Work.LinnikAreas2.T13Side1
import Submission.Work.LinnikAreas2.T13Side2
import Submission.Work.LinnikAreas2.T13Side3
import Submission.Work.LinnikAreas2.T13Side4

open scoped BigOperators
noncomputable section
namespace Work.LinnikAreas2
open Work.LinnikAreas.Density4
open Work.LinnikAreas.Density4.T13

/-- The complete Table-13 certificate for a row: the test-function parameter `theta13 lam lam1`
lies in `(pi/2, pi)`, the two Lemma-12.1 side conditions hold at `eps = 0` (`sideCond`), and the
HB Lemma 12.1 bound is below `N0 + 1`. -/
def rowCert (lam lam1 : ℝ) (N0 : ℕ) : Prop :=
  Real.pi / 2 < theta13 lam lam1 ∧ theta13 lam lam1 < Real.pi ∧
    sideCond lam lam1 ∧ bnd13 lam lam1 < (N0 : ℝ) + 1

theorem rowCert_0 : rowCert ((8:ℝ)/10) ((348:ℝ)/1000) 8 := by
  refine ⟨?_, ?_, side_0, row_0⟩
  · rw [show theta13 ((8:ℝ)/10) ((348:ℝ)/1000) = ((1021:ℝ)/(500:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((8:ℝ)/10) ((348:ℝ)/1000) = ((1021:ℝ)/(500:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_1 : rowCert ((8:ℝ)/10) ((4:ℝ)/10) 8 := by
  refine ⟨?_, ?_, side_1, row_1⟩
  · rw [show theta13 ((8:ℝ)/10) ((4:ℝ)/10) = ((61:ℝ)/(30:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((8:ℝ)/10) ((4:ℝ)/10) = ((61:ℝ)/(30:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_2 : rowCert ((8:ℝ)/10) ((44:ℝ)/100) 8 := by
  refine ⟨?_, ?_, side_2, row_2⟩
  · rw [show theta13 ((8:ℝ)/10) ((44:ℝ)/100) = ((152:ℝ)/(75:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((8:ℝ)/10) ((44:ℝ)/100) = ((152:ℝ)/(75:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_3 : rowCert ((8:ℝ)/10) ((5:ℝ)/10) 7 := by
  refine ⟨?_, ?_, side_3, row_3⟩
  · rw [show theta13 ((8:ℝ)/10) ((5:ℝ)/10) = ((121:ℝ)/(60:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((8:ℝ)/10) ((5:ℝ)/10) = ((121:ℝ)/(60:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_4 : rowCert ((8:ℝ)/10) ((58:ℝ)/100) 7 := by
  refine ⟨?_, ?_, side_4, row_4⟩
  · rw [show theta13 ((8:ℝ)/10) ((58:ℝ)/100) = ((601:ℝ)/(300:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((8:ℝ)/10) ((58:ℝ)/100) = ((601:ℝ)/(300:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_5 : rowCert ((825:ℝ)/1000) ((348:ℝ)/1000) 9 := by
  refine ⟨?_, ?_, side_5, row_5⟩
  · rw [show theta13 ((825:ℝ)/1000) ((348:ℝ)/1000) = ((4109:ℝ)/(2000:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((825:ℝ)/1000) ((348:ℝ)/1000) = ((4109:ℝ)/(2000:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_6 : rowCert ((825:ℝ)/1000) ((4:ℝ)/10) 9 := by
  refine ⟨?_, ?_, side_6, row_6⟩
  · rw [show theta13 ((825:ℝ)/1000) ((4:ℝ)/10) = ((491:ℝ)/(240:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((825:ℝ)/1000) ((4:ℝ)/10) = ((491:ℝ)/(240:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_7 : rowCert ((825:ℝ)/1000) ((44:ℝ)/100) 8 := by
  refine ⟨?_, ?_, side_7, row_7⟩
  · rw [show theta13 ((825:ℝ)/1000) ((44:ℝ)/100) = ((2447:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((825:ℝ)/1000) ((44:ℝ)/100) = ((2447:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_8 : rowCert ((825:ℝ)/1000) ((5:ℝ)/10) 8 := by
  refine ⟨?_, ?_, side_8, row_8⟩
  · rw [show theta13 ((825:ℝ)/1000) ((5:ℝ)/10) = ((487:ℝ)/(240:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((825:ℝ)/1000) ((5:ℝ)/10) = ((487:ℝ)/(240:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_9 : rowCert ((825:ℝ)/1000) ((58:ℝ)/100) 8 := by
  refine ⟨?_, ?_, side_9, row_9⟩
  · rw [show theta13 ((825:ℝ)/1000) ((58:ℝ)/100) = ((2419:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((825:ℝ)/1000) ((58:ℝ)/100) = ((2419:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_10 : rowCert ((85:ℝ)/100) ((348:ℝ)/1000) 10 := by
  refine ⟨?_, ?_, side_10, row_10⟩
  · rw [show theta13 ((85:ℝ)/100) ((348:ℝ)/1000) = ((2067:ℝ)/(1000:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((85:ℝ)/100) ((348:ℝ)/1000) = ((2067:ℝ)/(1000:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_11 : rowCert ((85:ℝ)/100) ((4:ℝ)/10) 9 := by
  refine ⟨?_, ?_, side_11, row_11⟩
  · rw [show theta13 ((85:ℝ)/100) ((4:ℝ)/10) = ((247:ℝ)/(120:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((85:ℝ)/100) ((4:ℝ)/10) = ((247:ℝ)/(120:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_12 : rowCert ((85:ℝ)/100) ((44:ℝ)/100) 9 := by
  refine ⟨?_, ?_, side_12, row_12⟩
  · rw [show theta13 ((85:ℝ)/100) ((44:ℝ)/100) = ((1231:ℝ)/(600:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((85:ℝ)/100) ((44:ℝ)/100) = ((1231:ℝ)/(600:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_13 : rowCert ((85:ℝ)/100) ((5:ℝ)/10) 9 := by
  refine ⟨?_, ?_, side_13, row_13⟩
  · rw [show theta13 ((85:ℝ)/100) ((5:ℝ)/10) = ((49:ℝ)/(24:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((85:ℝ)/100) ((5:ℝ)/10) = ((49:ℝ)/(24:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_14 : rowCert ((85:ℝ)/100) ((58:ℝ)/100) 8 := by
  refine ⟨?_, ?_, side_14, row_14⟩
  · rw [show theta13 ((85:ℝ)/100) ((58:ℝ)/100) = ((1217:ℝ)/(600:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((85:ℝ)/100) ((58:ℝ)/100) = ((1217:ℝ)/(600:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_15 : rowCert ((875:ℝ)/1000) ((348:ℝ)/1000) 11 := by
  refine ⟨?_, ?_, side_15, row_15⟩
  · rw [show theta13 ((875:ℝ)/1000) ((348:ℝ)/1000) = ((4159:ℝ)/(2000:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((875:ℝ)/1000) ((348:ℝ)/1000) = ((4159:ℝ)/(2000:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_16 : rowCert ((875:ℝ)/1000) ((4:ℝ)/10) 10 := by
  refine ⟨?_, ?_, side_16, row_16⟩
  · rw [show theta13 ((875:ℝ)/1000) ((4:ℝ)/10) = ((497:ℝ)/(240:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((875:ℝ)/1000) ((4:ℝ)/10) = ((497:ℝ)/(240:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_17 : rowCert ((875:ℝ)/1000) ((44:ℝ)/100) 10 := by
  refine ⟨?_, ?_, side_17, row_17⟩
  · rw [show theta13 ((875:ℝ)/1000) ((44:ℝ)/100) = ((2477:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((875:ℝ)/1000) ((44:ℝ)/100) = ((2477:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_18 : rowCert ((875:ℝ)/1000) ((5:ℝ)/10) 9 := by
  refine ⟨?_, ?_, side_18, row_18⟩
  · rw [show theta13 ((875:ℝ)/1000) ((5:ℝ)/10) = ((493:ℝ)/(240:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((875:ℝ)/1000) ((5:ℝ)/10) = ((493:ℝ)/(240:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_19 : rowCert ((875:ℝ)/1000) ((58:ℝ)/100) 9 := by
  refine ⟨?_, ?_, side_19, row_19⟩
  · rw [show theta13 ((875:ℝ)/1000) ((58:ℝ)/100) = ((2449:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((875:ℝ)/1000) ((58:ℝ)/100) = ((2449:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_20 : rowCert ((9:ℝ)/10) ((348:ℝ)/1000) 12 := by
  refine ⟨?_, ?_, side_20, row_20⟩
  · rw [show theta13 ((9:ℝ)/10) ((348:ℝ)/1000) = ((523:ℝ)/(250:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((9:ℝ)/10) ((348:ℝ)/1000) = ((523:ℝ)/(250:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_21 : rowCert ((9:ℝ)/10) ((4:ℝ)/10) 11 := by
  refine ⟨?_, ?_, side_21, row_21⟩
  · rw [show theta13 ((9:ℝ)/10) ((4:ℝ)/10) = ((25:ℝ)/(12:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((9:ℝ)/10) ((4:ℝ)/10) = ((25:ℝ)/(12:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_22 : rowCert ((9:ℝ)/10) ((44:ℝ)/100) 11 := by
  refine ⟨?_, ?_, side_22, row_22⟩
  · rw [show theta13 ((9:ℝ)/10) ((44:ℝ)/100) = ((623:ℝ)/(300:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((9:ℝ)/10) ((44:ℝ)/100) = ((623:ℝ)/(300:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_23 : rowCert ((9:ℝ)/10) ((5:ℝ)/10) 10 := by
  refine ⟨?_, ?_, side_23, row_23⟩
  · rw [show theta13 ((9:ℝ)/10) ((5:ℝ)/10) = ((31:ℝ)/(15:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((9:ℝ)/10) ((5:ℝ)/10) = ((31:ℝ)/(15:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_24 : rowCert ((9:ℝ)/10) ((58:ℝ)/100) 10 := by
  refine ⟨?_, ?_, side_24, row_24⟩
  · rw [show theta13 ((9:ℝ)/10) ((58:ℝ)/100) = ((154:ℝ)/(75:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((9:ℝ)/10) ((58:ℝ)/100) = ((154:ℝ)/(75:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_25 : rowCert ((925:ℝ)/1000) ((348:ℝ)/1000) 13 := by
  refine ⟨?_, ?_, side_25, row_25⟩
  · rw [show theta13 ((925:ℝ)/1000) ((348:ℝ)/1000) = ((4209:ℝ)/(2000:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((925:ℝ)/1000) ((348:ℝ)/1000) = ((4209:ℝ)/(2000:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_26 : rowCert ((925:ℝ)/1000) ((4:ℝ)/10) 12 := by
  refine ⟨?_, ?_, side_26, row_26⟩
  · rw [show theta13 ((925:ℝ)/1000) ((4:ℝ)/10) = ((503:ℝ)/(240:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((925:ℝ)/1000) ((4:ℝ)/10) = ((503:ℝ)/(240:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_27 : rowCert ((925:ℝ)/1000) ((44:ℝ)/100) 12 := by
  refine ⟨?_, ?_, side_27, row_27⟩
  · rw [show theta13 ((925:ℝ)/1000) ((44:ℝ)/100) = ((2507:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((925:ℝ)/1000) ((44:ℝ)/100) = ((2507:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_28 : rowCert ((925:ℝ)/1000) ((5:ℝ)/10) 11 := by
  refine ⟨?_, ?_, side_28, row_28⟩
  · rw [show theta13 ((925:ℝ)/1000) ((5:ℝ)/10) = ((499:ℝ)/(240:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((925:ℝ)/1000) ((5:ℝ)/10) = ((499:ℝ)/(240:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_29 : rowCert ((925:ℝ)/1000) ((58:ℝ)/100) 11 := by
  refine ⟨?_, ?_, side_29, row_29⟩
  · rw [show theta13 ((925:ℝ)/1000) ((58:ℝ)/100) = ((2479:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((925:ℝ)/1000) ((58:ℝ)/100) = ((2479:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_30 : rowCert ((95:ℝ)/100) ((348:ℝ)/1000) 15 := by
  refine ⟨?_, ?_, side_30, row_30⟩
  · rw [show theta13 ((95:ℝ)/100) ((348:ℝ)/1000) = ((2117:ℝ)/(1000:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((95:ℝ)/100) ((348:ℝ)/1000) = ((2117:ℝ)/(1000:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_31 : rowCert ((95:ℝ)/100) ((4:ℝ)/10) 14 := by
  refine ⟨?_, ?_, side_31, row_31⟩
  · rw [show theta13 ((95:ℝ)/100) ((4:ℝ)/10) = ((253:ℝ)/(120:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((95:ℝ)/100) ((4:ℝ)/10) = ((253:ℝ)/(120:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_32 : rowCert ((95:ℝ)/100) ((44:ℝ)/100) 13 := by
  refine ⟨?_, ?_, side_32, row_32⟩
  · rw [show theta13 ((95:ℝ)/100) ((44:ℝ)/100) = ((1261:ℝ)/(600:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((95:ℝ)/100) ((44:ℝ)/100) = ((1261:ℝ)/(600:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_33 : rowCert ((95:ℝ)/100) ((5:ℝ)/10) 12 := by
  refine ⟨?_, ?_, side_33, row_33⟩
  · rw [show theta13 ((95:ℝ)/100) ((5:ℝ)/10) = ((251:ℝ)/(120:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((95:ℝ)/100) ((5:ℝ)/10) = ((251:ℝ)/(120:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_34 : rowCert ((95:ℝ)/100) ((58:ℝ)/100) 12 := by
  refine ⟨?_, ?_, side_34, row_34⟩
  · rw [show theta13 ((95:ℝ)/100) ((58:ℝ)/100) = ((1247:ℝ)/(600:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((95:ℝ)/100) ((58:ℝ)/100) = ((1247:ℝ)/(600:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_35 : rowCert ((975:ℝ)/1000) ((348:ℝ)/1000) 16 := by
  refine ⟨?_, ?_, side_35, row_35⟩
  · rw [show theta13 ((975:ℝ)/1000) ((348:ℝ)/1000) = ((4259:ℝ)/(2000:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((975:ℝ)/1000) ((348:ℝ)/1000) = ((4259:ℝ)/(2000:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_36 : rowCert ((975:ℝ)/1000) ((4:ℝ)/10) 15 := by
  refine ⟨?_, ?_, side_36, row_36⟩
  · rw [show theta13 ((975:ℝ)/1000) ((4:ℝ)/10) = ((509:ℝ)/(240:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((975:ℝ)/1000) ((4:ℝ)/10) = ((509:ℝ)/(240:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_37 : rowCert ((975:ℝ)/1000) ((44:ℝ)/100) 15 := by
  refine ⟨?_, ?_, side_37, row_37⟩
  · rw [show theta13 ((975:ℝ)/1000) ((44:ℝ)/100) = ((2537:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((975:ℝ)/1000) ((44:ℝ)/100) = ((2537:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_38 : rowCert ((975:ℝ)/1000) ((5:ℝ)/10) 14 := by
  refine ⟨?_, ?_, side_38, row_38⟩
  · rw [show theta13 ((975:ℝ)/1000) ((5:ℝ)/10) = ((101:ℝ)/(48:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((975:ℝ)/1000) ((5:ℝ)/10) = ((101:ℝ)/(48:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_39 : rowCert ((975:ℝ)/1000) ((58:ℝ)/100) 13 := by
  refine ⟨?_, ?_, side_39, row_39⟩
  · rw [show theta13 ((975:ℝ)/1000) ((58:ℝ)/100) = ((2509:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((975:ℝ)/1000) ((58:ℝ)/100) = ((2509:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_40 : rowCert (1) ((348:ℝ)/1000) 18 := by
  refine ⟨?_, ?_, side_40, row_40⟩
  · rw [show theta13 (1) ((348:ℝ)/1000) = ((1071:ℝ)/(500:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 (1) ((348:ℝ)/1000) = ((1071:ℝ)/(500:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_41 : rowCert (1) ((4:ℝ)/10) 17 := by
  refine ⟨?_, ?_, side_41, row_41⟩
  · rw [show theta13 (1) ((4:ℝ)/10) = ((32:ℝ)/(15:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 (1) ((4:ℝ)/10) = ((32:ℝ)/(15:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_42 : rowCert (1) ((44:ℝ)/100) 16 := by
  refine ⟨?_, ?_, side_42, row_42⟩
  · rw [show theta13 (1) ((44:ℝ)/100) = ((319:ℝ)/(150:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 (1) ((44:ℝ)/100) = ((319:ℝ)/(150:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_43 : rowCert (1) ((5:ℝ)/10) 15 := by
  refine ⟨?_, ?_, side_43, row_43⟩
  · rw [show theta13 (1) ((5:ℝ)/10) = ((127:ℝ)/(60:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 (1) ((5:ℝ)/10) = ((127:ℝ)/(60:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_44 : rowCert (1) ((58:ℝ)/100) 14 := by
  refine ⟨?_, ?_, side_44, row_44⟩
  · rw [show theta13 (1) ((58:ℝ)/100) = ((631:ℝ)/(300:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 (1) ((58:ℝ)/100) = ((631:ℝ)/(300:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_45 : rowCert ((1025:ℝ)/1000) ((348:ℝ)/1000) 21 := by
  refine ⟨?_, ?_, side_45, row_45⟩
  · rw [show theta13 ((1025:ℝ)/1000) ((348:ℝ)/1000) = ((4309:ℝ)/(2000:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((1025:ℝ)/1000) ((348:ℝ)/1000) = ((4309:ℝ)/(2000:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_46 : rowCert ((1025:ℝ)/1000) ((4:ℝ)/10) 19 := by
  refine ⟨?_, ?_, side_46, row_46⟩
  · rw [show theta13 ((1025:ℝ)/1000) ((4:ℝ)/10) = ((103:ℝ)/(48:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((1025:ℝ)/1000) ((4:ℝ)/10) = ((103:ℝ)/(48:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_47 : rowCert ((1025:ℝ)/1000) ((44:ℝ)/100) 18 := by
  refine ⟨?_, ?_, side_47, row_47⟩
  · rw [show theta13 ((1025:ℝ)/1000) ((44:ℝ)/100) = ((2567:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((1025:ℝ)/1000) ((44:ℝ)/100) = ((2567:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_48 : rowCert ((1025:ℝ)/1000) ((5:ℝ)/10) 17 := by
  refine ⟨?_, ?_, side_48, row_48⟩
  · rw [show theta13 ((1025:ℝ)/1000) ((5:ℝ)/10) = ((511:ℝ)/(240:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((1025:ℝ)/1000) ((5:ℝ)/10) = ((511:ℝ)/(240:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_49 : rowCert ((1025:ℝ)/1000) ((58:ℝ)/100) 15 := by
  refine ⟨?_, ?_, side_49, row_49⟩
  · rw [show theta13 ((1025:ℝ)/1000) ((58:ℝ)/100) = ((2539:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((1025:ℝ)/1000) ((58:ℝ)/100) = ((2539:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_50 : rowCert ((105:ℝ)/100) ((348:ℝ)/1000) 24 := by
  refine ⟨?_, ?_, side_50, row_50⟩
  · rw [show theta13 ((105:ℝ)/100) ((348:ℝ)/1000) = ((2167:ℝ)/(1000:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((105:ℝ)/100) ((348:ℝ)/1000) = ((2167:ℝ)/(1000:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_51 : rowCert ((105:ℝ)/100) ((4:ℝ)/10) 22 := by
  refine ⟨?_, ?_, side_51, row_51⟩
  · rw [show theta13 ((105:ℝ)/100) ((4:ℝ)/10) = ((259:ℝ)/(120:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((105:ℝ)/100) ((4:ℝ)/10) = ((259:ℝ)/(120:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_52 : rowCert ((105:ℝ)/100) ((44:ℝ)/100) 21 := by
  refine ⟨?_, ?_, side_52, row_52⟩
  · rw [show theta13 ((105:ℝ)/100) ((44:ℝ)/100) = ((1291:ℝ)/(600:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((105:ℝ)/100) ((44:ℝ)/100) = ((1291:ℝ)/(600:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_53 : rowCert ((105:ℝ)/100) ((5:ℝ)/10) 19 := by
  refine ⟨?_, ?_, side_53, row_53⟩
  · rw [show theta13 ((105:ℝ)/100) ((5:ℝ)/10) = ((257:ℝ)/(120:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((105:ℝ)/100) ((5:ℝ)/10) = ((257:ℝ)/(120:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_54 : rowCert ((105:ℝ)/100) ((58:ℝ)/100) 17 := by
  refine ⟨?_, ?_, side_54, row_54⟩
  · rw [show theta13 ((105:ℝ)/100) ((58:ℝ)/100) = ((1277:ℝ)/(600:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((105:ℝ)/100) ((58:ℝ)/100) = ((1277:ℝ)/(600:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_55 : rowCert ((1075:ℝ)/1000) ((348:ℝ)/1000) 28 := by
  refine ⟨?_, ?_, side_55, row_55⟩
  · rw [show theta13 ((1075:ℝ)/1000) ((348:ℝ)/1000) = ((4359:ℝ)/(2000:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((1075:ℝ)/1000) ((348:ℝ)/1000) = ((4359:ℝ)/(2000:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_56 : rowCert ((1075:ℝ)/1000) ((4:ℝ)/10) 26 := by
  refine ⟨?_, ?_, side_56, row_56⟩
  · rw [show theta13 ((1075:ℝ)/1000) ((4:ℝ)/10) = ((521:ℝ)/(240:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((1075:ℝ)/1000) ((4:ℝ)/10) = ((521:ℝ)/(240:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_57 : rowCert ((1075:ℝ)/1000) ((44:ℝ)/100) 24 := by
  refine ⟨?_, ?_, side_57, row_57⟩
  · rw [show theta13 ((1075:ℝ)/1000) ((44:ℝ)/100) = ((2597:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((1075:ℝ)/1000) ((44:ℝ)/100) = ((2597:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_58 : rowCert ((1075:ℝ)/1000) ((5:ℝ)/10) 22 := by
  refine ⟨?_, ?_, side_58, row_58⟩
  · rw [show theta13 ((1075:ℝ)/1000) ((5:ℝ)/10) = ((517:ℝ)/(240:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((1075:ℝ)/1000) ((5:ℝ)/10) = ((517:ℝ)/(240:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_59 : rowCert ((1075:ℝ)/1000) ((58:ℝ)/100) 19 := by
  refine ⟨?_, ?_, side_59, row_59⟩
  · rw [show theta13 ((1075:ℝ)/1000) ((58:ℝ)/100) = ((2569:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((1075:ℝ)/1000) ((58:ℝ)/100) = ((2569:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_60 : rowCert ((11:ℝ)/10) ((348:ℝ)/1000) 34 := by
  refine ⟨?_, ?_, side_60, row_60⟩
  · rw [show theta13 ((11:ℝ)/10) ((348:ℝ)/1000) = ((274:ℝ)/(125:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((11:ℝ)/10) ((348:ℝ)/1000) = ((274:ℝ)/(125:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_61 : rowCert ((11:ℝ)/10) ((4:ℝ)/10) 30 := by
  refine ⟨?_, ?_, side_61, row_61⟩
  · rw [show theta13 ((11:ℝ)/10) ((4:ℝ)/10) = ((131:ℝ)/(60:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((11:ℝ)/10) ((4:ℝ)/10) = ((131:ℝ)/(60:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_62 : rowCert ((11:ℝ)/10) ((44:ℝ)/100) 28 := by
  refine ⟨?_, ?_, side_62, row_62⟩
  · rw [show theta13 ((11:ℝ)/10) ((44:ℝ)/100) = ((653:ℝ)/(300:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((11:ℝ)/10) ((44:ℝ)/100) = ((653:ℝ)/(300:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_63 : rowCert ((11:ℝ)/10) ((5:ℝ)/10) 25 := by
  refine ⟨?_, ?_, side_63, row_63⟩
  · rw [show theta13 ((11:ℝ)/10) ((5:ℝ)/10) = ((13:ℝ)/(6:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((11:ℝ)/10) ((5:ℝ)/10) = ((13:ℝ)/(6:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_64 : rowCert ((11:ℝ)/10) ((58:ℝ)/100) 22 := by
  refine ⟨?_, ?_, side_64, row_64⟩
  · rw [show theta13 ((11:ℝ)/10) ((58:ℝ)/100) = ((323:ℝ)/(150:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((11:ℝ)/10) ((58:ℝ)/100) = ((323:ℝ)/(150:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_65 : rowCert ((1125:ℝ)/1000) ((348:ℝ)/1000) 42 := by
  refine ⟨?_, ?_, side_65, row_65⟩
  · rw [show theta13 ((1125:ℝ)/1000) ((348:ℝ)/1000) = ((4409:ℝ)/(2000:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((1125:ℝ)/1000) ((348:ℝ)/1000) = ((4409:ℝ)/(2000:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_66 : rowCert ((1125:ℝ)/1000) ((4:ℝ)/10) 36 := by
  refine ⟨?_, ?_, side_66, row_66⟩
  · rw [show theta13 ((1125:ℝ)/1000) ((4:ℝ)/10) = ((527:ℝ)/(240:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((1125:ℝ)/1000) ((4:ℝ)/10) = ((527:ℝ)/(240:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_67 : rowCert ((1125:ℝ)/1000) ((44:ℝ)/100) 33 := by
  refine ⟨?_, ?_, side_67, row_67⟩
  · rw [show theta13 ((1125:ℝ)/1000) ((44:ℝ)/100) = ((2627:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((1125:ℝ)/1000) ((44:ℝ)/100) = ((2627:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_68 : rowCert ((1125:ℝ)/1000) ((5:ℝ)/10) 29 := by
  refine ⟨?_, ?_, side_68, row_68⟩
  · rw [show theta13 ((1125:ℝ)/1000) ((5:ℝ)/10) = ((523:ℝ)/(240:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((1125:ℝ)/1000) ((5:ℝ)/10) = ((523:ℝ)/(240:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_69 : rowCert ((1125:ℝ)/1000) ((58:ℝ)/100) 25 := by
  refine ⟨?_, ?_, side_69, row_69⟩
  · rw [show theta13 ((1125:ℝ)/1000) ((58:ℝ)/100) = ((2599:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((1125:ℝ)/1000) ((58:ℝ)/100) = ((2599:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_70 : rowCert ((115:ℝ)/100) ((348:ℝ)/1000) 54 := by
  refine ⟨?_, ?_, side_70, row_70⟩
  · rw [show theta13 ((115:ℝ)/100) ((348:ℝ)/1000) = ((2217:ℝ)/(1000:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((115:ℝ)/100) ((348:ℝ)/1000) = ((2217:ℝ)/(1000:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_71 : rowCert ((115:ℝ)/100) ((4:ℝ)/10) 45 := by
  refine ⟨?_, ?_, side_71, row_71⟩
  · rw [show theta13 ((115:ℝ)/100) ((4:ℝ)/10) = ((53:ℝ)/(24:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((115:ℝ)/100) ((4:ℝ)/10) = ((53:ℝ)/(24:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_72 : rowCert ((115:ℝ)/100) ((44:ℝ)/100) 40 := by
  refine ⟨?_, ?_, side_72, row_72⟩
  · rw [show theta13 ((115:ℝ)/100) ((44:ℝ)/100) = ((1321:ℝ)/(600:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((115:ℝ)/100) ((44:ℝ)/100) = ((1321:ℝ)/(600:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_73 : rowCert ((115:ℝ)/100) ((5:ℝ)/10) 35 := by
  refine ⟨?_, ?_, side_73, row_73⟩
  · rw [show theta13 ((115:ℝ)/100) ((5:ℝ)/10) = ((263:ℝ)/(120:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((115:ℝ)/100) ((5:ℝ)/10) = ((263:ℝ)/(120:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_74 : rowCert ((115:ℝ)/100) ((58:ℝ)/100) 29 := by
  refine ⟨?_, ?_, side_74, row_74⟩
  · rw [show theta13 ((115:ℝ)/100) ((58:ℝ)/100) = ((1307:ℝ)/(600:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((115:ℝ)/100) ((58:ℝ)/100) = ((1307:ℝ)/(600:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_75 : rowCert ((1175:ℝ)/1000) ((348:ℝ)/1000) 73 := by
  refine ⟨?_, ?_, side_75, row_75⟩
  · rw [show theta13 ((1175:ℝ)/1000) ((348:ℝ)/1000) = ((4459:ℝ)/(2000:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((1175:ℝ)/1000) ((348:ℝ)/1000) = ((4459:ℝ)/(2000:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_76 : rowCert ((1175:ℝ)/1000) ((4:ℝ)/10) 58 := by
  refine ⟨?_, ?_, side_76, row_76⟩
  · rw [show theta13 ((1175:ℝ)/1000) ((4:ℝ)/10) = ((533:ℝ)/(240:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((1175:ℝ)/1000) ((4:ℝ)/10) = ((533:ℝ)/(240:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_77 : rowCert ((1175:ℝ)/1000) ((44:ℝ)/100) 51 := by
  refine ⟨?_, ?_, side_77, row_77⟩
  · rw [show theta13 ((1175:ℝ)/1000) ((44:ℝ)/100) = ((2657:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((1175:ℝ)/1000) ((44:ℝ)/100) = ((2657:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_78 : rowCert ((1175:ℝ)/1000) ((5:ℝ)/10) 42 := by
  refine ⟨?_, ?_, side_78, row_78⟩
  · rw [show theta13 ((1175:ℝ)/1000) ((5:ℝ)/10) = ((529:ℝ)/(240:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((1175:ℝ)/1000) ((5:ℝ)/10) = ((529:ℝ)/(240:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_79 : rowCert ((1175:ℝ)/1000) ((58:ℝ)/100) 35 := by
  refine ⟨?_, ?_, side_79, row_79⟩
  · rw [show theta13 ((1175:ℝ)/1000) ((58:ℝ)/100) = ((2629:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((1175:ℝ)/1000) ((58:ℝ)/100) = ((2629:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_80 : rowCert ((12:ℝ)/10) ((348:ℝ)/1000) 111 := by
  refine ⟨?_, ?_, side_80, row_80⟩
  · rw [show theta13 ((12:ℝ)/10) ((348:ℝ)/1000) = ((1121:ℝ)/(500:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((12:ℝ)/10) ((348:ℝ)/1000) = ((1121:ℝ)/(500:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_81 : rowCert ((12:ℝ)/10) ((4:ℝ)/10) 81 := by
  refine ⟨?_, ?_, side_81, row_81⟩
  · rw [show theta13 ((12:ℝ)/10) ((4:ℝ)/10) = ((67:ℝ)/(30:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((12:ℝ)/10) ((4:ℝ)/10) = ((67:ℝ)/(30:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_82 : rowCert ((12:ℝ)/10) ((44:ℝ)/100) 67 := by
  refine ⟨?_, ?_, side_82, row_82⟩
  · rw [show theta13 ((12:ℝ)/10) ((44:ℝ)/100) = ((167:ℝ)/(75:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((12:ℝ)/10) ((44:ℝ)/100) = ((167:ℝ)/(75:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_83 : rowCert ((12:ℝ)/10) ((5:ℝ)/10) 54 := by
  refine ⟨?_, ?_, side_83, row_83⟩
  · rw [show theta13 ((12:ℝ)/10) ((5:ℝ)/10) = ((133:ℝ)/(60:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((12:ℝ)/10) ((5:ℝ)/10) = ((133:ℝ)/(60:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_84 : rowCert ((12:ℝ)/10) ((58:ℝ)/100) 42 := by
  refine ⟨?_, ?_, side_84, row_84⟩
  · rw [show theta13 ((12:ℝ)/10) ((58:ℝ)/100) = ((661:ℝ)/(300:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((12:ℝ)/10) ((58:ℝ)/100) = ((661:ℝ)/(300:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_85 : rowCert ((1225:ℝ)/1000) ((348:ℝ)/1000) 218 := by
  refine ⟨?_, ?_, side_85, row_85⟩
  · rw [show theta13 ((1225:ℝ)/1000) ((348:ℝ)/1000) = ((4509:ℝ)/(2000:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((1225:ℝ)/1000) ((348:ℝ)/1000) = ((4509:ℝ)/(2000:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_86 : rowCert ((1225:ℝ)/1000) ((4:ℝ)/10) 127 := by
  refine ⟨?_, ?_, side_86, row_86⟩
  · rw [show theta13 ((1225:ℝ)/1000) ((4:ℝ)/10) = ((539:ℝ)/(240:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((1225:ℝ)/1000) ((4:ℝ)/10) = ((539:ℝ)/(240:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_87 : rowCert ((1225:ℝ)/1000) ((44:ℝ)/100) 97 := by
  refine ⟨?_, ?_, side_87, row_87⟩
  · rw [show theta13 ((1225:ℝ)/1000) ((44:ℝ)/100) = ((2687:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((1225:ℝ)/1000) ((44:ℝ)/100) = ((2687:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_88 : rowCert ((1225:ℝ)/1000) ((5:ℝ)/10) 71 := by
  refine ⟨?_, ?_, side_88, row_88⟩
  · rw [show theta13 ((1225:ℝ)/1000) ((5:ℝ)/10) = ((107:ℝ)/(48:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((1225:ℝ)/1000) ((5:ℝ)/10) = ((107:ℝ)/(48:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_89 : rowCert ((1225:ℝ)/1000) ((58:ℝ)/100) 53 := by
  refine ⟨?_, ?_, side_89, row_89⟩
  · rw [show theta13 ((1225:ℝ)/1000) ((58:ℝ)/100) = ((2659:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((1225:ℝ)/1000) ((58:ℝ)/100) = ((2659:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_90 : rowCert ((125:ℝ)/100) ((348:ℝ)/1000) 2583 := by
  refine ⟨?_, ?_, side_90, row_90⟩
  · rw [show theta13 ((125:ℝ)/100) ((348:ℝ)/1000) = ((2267:ℝ)/(1000:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((125:ℝ)/100) ((348:ℝ)/1000) = ((2267:ℝ)/(1000:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_91 : rowCert ((125:ℝ)/100) ((4:ℝ)/10) 279 := by
  refine ⟨?_, ?_, side_91, row_91⟩
  · rw [show theta13 ((125:ℝ)/100) ((4:ℝ)/10) = ((271:ℝ)/(120:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((125:ℝ)/100) ((4:ℝ)/10) = ((271:ℝ)/(120:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_92 : rowCert ((125:ℝ)/100) ((44:ℝ)/100) 166 := by
  refine ⟨?_, ?_, side_92, row_92⟩
  · rw [show theta13 ((125:ℝ)/100) ((44:ℝ)/100) = ((1351:ℝ)/(600:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((125:ℝ)/100) ((44:ℝ)/100) = ((1351:ℝ)/(600:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_93 : rowCert ((125:ℝ)/100) ((5:ℝ)/10) 104 := by
  refine ⟨?_, ?_, side_93, row_93⟩
  · rw [show theta13 ((125:ℝ)/100) ((5:ℝ)/10) = ((269:ℝ)/(120:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((125:ℝ)/100) ((5:ℝ)/10) = ((269:ℝ)/(120:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_94 : rowCert ((125:ℝ)/100) ((58:ℝ)/100) 70 := by
  refine ⟨?_, ?_, side_94, row_94⟩
  · rw [show theta13 ((125:ℝ)/100) ((58:ℝ)/100) = ((1337:ℝ)/(600:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((125:ℝ)/100) ((58:ℝ)/100) = ((1337:ℝ)/(600:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_95 : rowCert ((1275:ℝ)/1000) ((44:ℝ)/100) 520 := by
  refine ⟨?_, ?_, side_95, row_95⟩
  · rw [show theta13 ((1275:ℝ)/1000) ((44:ℝ)/100) = ((2717:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((1275:ℝ)/1000) ((44:ℝ)/100) = ((2717:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_96 : rowCert ((1275:ℝ)/1000) ((5:ℝ)/10) 184 := by
  refine ⟨?_, ?_, side_96, row_96⟩
  · rw [show theta13 ((1275:ℝ)/1000) ((5:ℝ)/10) = ((541:ℝ)/(240:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((1275:ℝ)/1000) ((5:ℝ)/10) = ((541:ℝ)/(240:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_97 : rowCert ((1275:ℝ)/1000) ((58:ℝ)/100) 100 := by
  refine ⟨?_, ?_, side_97, row_97⟩
  · rw [show theta13 ((1275:ℝ)/1000) ((58:ℝ)/100) = ((2689:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((1275:ℝ)/1000) ((58:ℝ)/100) = ((2689:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_98 : rowCert ((13:ℝ)/10) ((5:ℝ)/10) 667 := by
  refine ⟨?_, ?_, side_98, row_98⟩
  · rw [show theta13 ((13:ℝ)/10) ((5:ℝ)/10) = ((34:ℝ)/(15:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((13:ℝ)/10) ((5:ℝ)/10) = ((34:ℝ)/(15:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_99 : rowCert ((13:ℝ)/10) ((58:ℝ)/100) 167 := by
  refine ⟨?_, ?_, side_99, row_99⟩
  · rw [show theta13 ((13:ℝ)/10) ((58:ℝ)/100) = ((169:ℝ)/(75:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((13:ℝ)/10) ((58:ℝ)/100) = ((169:ℝ)/(75:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

theorem rowCert_100 : rowCert ((1325:ℝ)/1000) ((58:ℝ)/100) 460 := by
  refine ⟨?_, ?_, side_100, row_100⟩
  · rw [show theta13 ((1325:ℝ)/1000) ((58:ℝ)/100) = ((2719:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_lt_d20; linarith
  · rw [show theta13 ((1325:ℝ)/1000) ((58:ℝ)/100) = ((2719:ℝ)/(1200:ℝ)) by norm_num [theta13]]
    have h := Real.pi_gt_d20; linarith

end Work.LinnikAreas2
