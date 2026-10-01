/-
# ZeroFreeTables — HBTable7_cert85

Every one of the seventeen rows of Heath-Brown's Table 7 satisfies the certificate
`CertRow85` of **HB Lemma 8.5** (the five-term positivity), at `ε = 0`:

`F(-λ₂) - F(λ₁-λ₂) - F(0) + f(0)(3/8) < 0`  at `(λ₁, λ₂) = (b, c)`.

The certificates use the test function of HB Lemma 7.1 at `θ = π/4` — so that
`F = tfF l`, `f(0) = 2l(π-3)` — with the single parameter

* `l = 53/50 = 1.06` for the sixteen rows with `b < c` (margins `0.008 … 0.028`),
* `l = 93/100 = 0.93` for the diagonal row `(745/1000, 745/1000)`.

Each row is proved by the same three steps, through the reduction lemmas of
`Cert85Base` (which evaluate `tfF` at `-c`, `b-c`, `0` into `PhiS`/`PhiD`):

1. `apply CertRow85_of_lt` (resp. `CertRow85_of_eq` for the diagonal row) leaves a
   strict inequality in the atoms `Real.pi/2`, `(Real.pi/2-2)^2`, `Real.pi-3`,
   `Real.exp ((c/l) * (π/2))` and `Real.exp (((c-b)/l) * (π/2))`;
2. the constants are bounded by `pi_div_two_bounds`, `pi_sub_three_bounds`,
   `s_bounds`, and the two exponentials (whose arguments are the reduced fractions
   `c/l`, `(c-b)/l`, both in `(1, 2.7)`, so the arguments `· (π/2)` are `< 8`) by the
   two-sided Taylor bounds `exp_lower` / `exp_upper` of `T7Cert` at eight-decimal
   outer rationals;
3. `unfold PhiS PhiK PhiA PhiC PhiD; norm_num; linarith`.

The extraction of the row bounds from these certificates, and the upgrade of `ε = 0`
to the small positive `ε` required by the engine `lemma85pt_region`, are in
`HBTable7_rowHelpers`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HBTable7_defs85
import Submission.Work.ZeroFreeTables.T7Cert
import Submission.Work.ZeroFreeTables.Cert85Base

namespace Work.ZeroFreeTables

open scoped Real BigOperators

theorem T7R85_01 : CertRow85 (10/100) (276/100) (53/50) 0 := by
  apply CertRow85_of_lt (by norm_num) (by norm_num) (by norm_num)
  have h1 := pi_div_two_bounds.1
  have h2 := pi_div_two_bounds.2
  have h3 := pi_sub_three_bounds.1
  have h4 := pi_sub_three_bounds.2
  have h5 := s_bounds.1
  have h6 := s_bounds.2
  have hq1lo : (204499899/50000000 : ℝ) ≤ (138/53 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq1hi : (138/53 : ℝ) * (Real.pi/2) ≤ (408999799/100000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hEq1lo : (2986988551/50000000 : ℝ) ≤ Real.exp ((138/53 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (204499899/50000000 : ℝ) (2986988551/50000000 : ℝ) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq1lo)
  have hEq1hi : Real.exp ((138/53 : ℝ) * (Real.pi/2)) ≤ (5973977163/100000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq1hi)
      (exp_upper (408999799/100000000 : ℝ) (5973977163/100000000 : ℝ) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  have hq2lo : (78836193/20000000 : ℝ) ≤ (133/53 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq2hi : (133/53 : ℝ) * (Real.pi/2) ≤ (197090483/50000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hEq2lo : (5151173521/100000000 : ℝ) ≤ Real.exp ((133/53 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (78836193/20000000 : ℝ) (5151173521/100000000 : ℝ) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq2lo)
  have hEq2hi : Real.exp ((133/53 : ℝ) * (Real.pi/2)) ≤ (2575586787/50000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq2hi)
      (exp_upper (197090483/50000000 : ℝ) (2575586787/50000000 : ℝ) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  unfold PhiS PhiK PhiA PhiC PhiD
  norm_num
  linarith

theorem T7R85_02 : CertRow85 (12/100) (256/100) (53/50) 0 := by
  apply CertRow85_of_lt (by norm_num) (by norm_num) (by norm_num)
  have h1 := pi_div_two_bounds.1
  have h2 := pi_div_two_bounds.2
  have h3 := pi_sub_three_bounds.1
  have h4 := pi_sub_three_bounds.2
  have h5 := s_bounds.1
  have h6 := s_bounds.2
  have hq1lo : (379362131/100000000 : ℝ) ≤ (128/53 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq1hi : (128/53 : ℝ) * (Real.pi/2) ≤ (94840533/25000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hEq1lo : (888339139/20000000 : ℝ) ≤ Real.exp ((128/53 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (379362131/100000000 : ℝ) (888339139/20000000 : ℝ) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq1lo)
  have hEq1hi : Real.exp ((128/53 : ℝ) * (Real.pi/2)) ≤ (4441695741/100000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq1hi)
      (exp_upper (94840533/25000000 : ℝ) (4441695741/100000000 : ℝ) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  have hq2lo : (361579531/100000000 : ℝ) ≤ (122/53 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq2hi : (122/53 : ℝ) * (Real.pi/2) ≤ (90394883/25000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hEq2lo : (3718090451/100000000 : ℝ) ≤ Real.exp ((122/53 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (361579531/100000000 : ℝ) (3718090451/100000000 : ℝ) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq2lo)
  have hEq2hi : Real.exp ((122/53 : ℝ) * (Real.pi/2)) ≤ (3718090489/100000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq2hi)
      (exp_upper (90394883/25000000 : ℝ) (3718090489/100000000 : ℝ) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  unfold PhiS PhiK PhiA PhiC PhiD
  norm_num
  linarith

theorem T7R85_03 : CertRow85 (14/100) (239/100) (53/50) 0 := by
  apply CertRow85_of_lt (by norm_num) (by norm_num) (by norm_num)
  have h1 := pi_div_two_bounds.1
  have h2 := pi_div_two_bounds.2
  have h3 := pi_sub_three_bounds.1
  have h4 := pi_sub_three_bounds.2
  have h5 := s_bounds.1
  have h6 := s_bounds.2
  have hq1lo : (70834023/20000000 : ℝ) ≤ (239/106 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq1hi : (239/106 : ℝ) * (Real.pi/2) ≤ (88542529/25000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hEq1lo : (3452560249/100000000 : ℝ) ≤ Real.exp ((239/106 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (70834023/20000000 : ℝ) (3452560249/100000000 : ℝ) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq1lo)
  have hEq1hi : Real.exp ((239/106 : ℝ) * (Real.pi/2)) ≤ (863140071/25000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq1hi)
      (exp_upper (88542529/25000000 : ℝ) (863140071/25000000 : ℝ) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  have hq2lo : (83355937/25000000 : ℝ) ≤ (225/106 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq2hi : (225/106 : ℝ) * (Real.pi/2) ≤ (333423749/100000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hEq2lo : (561139621/20000000 : ℝ) ≤ Real.exp ((225/106 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (83355937/25000000 : ℝ) (561139621/20000000 : ℝ) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq2lo)
  have hEq2hi : Real.exp ((225/106 : ℝ) * (Real.pi/2)) ≤ (1402849067/50000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq2hi)
      (exp_upper (333423749/100000000 : ℝ) (1402849067/50000000 : ℝ) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  unfold PhiS PhiK PhiA PhiC PhiD
  norm_num
  linarith

theorem T7R85_04 : CertRow85 (16/100) (225/100) (53/50) 0 := by
  apply CertRow85_of_lt (by norm_num) (by norm_num) (by norm_num)
  have h1 := pi_div_two_bounds.1
  have h2 := pi_div_two_bounds.2
  have h3 := pi_sub_three_bounds.1
  have h4 := pi_sub_three_bounds.2
  have h5 := s_bounds.1
  have h6 := s_bounds.2
  have hq1lo : (83355937/25000000 : ℝ) ≤ (225/106 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq1hi : (225/106 : ℝ) * (Real.pi/2) ≤ (333423749/100000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hEq1lo : (561139621/20000000 : ℝ) ≤ Real.exp ((225/106 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (83355937/25000000 : ℝ) (561139621/20000000 : ℝ) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq1lo)
  have hEq1hi : Real.exp ((225/106 : ℝ) * (Real.pi/2)) ≤ (1402849067/50000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq1hi)
      (exp_upper (333423749/100000000 : ℝ) (1402849067/50000000 : ℝ) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  have hq2lo : (61942723/20000000 : ℝ) ≤ (209/106 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq2hi : (209/106 : ℝ) * (Real.pi/2) ≤ (19357101/6250000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hEq2lo : (1106723531/50000000 : ℝ) ≤ Real.exp ((209/106 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (61942723/20000000 : ℝ) (1106723531/50000000 : ℝ) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq2lo)
  have hEq2hi : Real.exp ((209/106 : ℝ) * (Real.pi/2)) ≤ (442689417/20000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq2hi)
      (exp_upper (19357101/6250000 : ℝ) (442689417/20000000 : ℝ) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  unfold PhiS PhiK PhiA PhiC PhiD
  norm_num
  linarith

theorem T7R85_05 : CertRow85 (18/100) (212/100) (53/50) 0 := by
  apply CertRow85_of_lt (by norm_num) (by norm_num) (by norm_num)
  have h1 := pi_div_two_bounds.1
  have h2 := pi_div_two_bounds.2
  have h3 := pi_sub_three_bounds.1
  have h4 := pi_sub_three_bounds.2
  have h5 := s_bounds.1
  have h6 := s_bounds.2
  have hq1lo : (62831853/20000000 : ℝ) ≤ (2/1 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq1hi : (2/1 : ℝ) * (Real.pi/2) ≤ (157079633/50000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hEq1lo : (1157034627/50000000 : ℝ) ≤ Real.exp ((2/1 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (62831853/20000000 : ℝ) (1157034627/50000000 : ℝ) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq1lo)
  have hEq1hi : Real.exp ((2/1 : ℝ) * (Real.pi/2)) ≤ (2314069279/100000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq1hi)
      (exp_upper (157079633/50000000 : ℝ) (2314069279/100000000 : ℝ) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  have hq2lo : (57497073/20000000 : ℝ) ≤ (97/53 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq2hi : (97/53 : ℝ) * (Real.pi/2) ≤ (143742683/50000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hEq2lo : (1772283019/100000000 : ℝ) ≤ Real.exp ((97/53 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (57497073/20000000 : ℝ) (1772283019/100000000 : ℝ) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq2lo)
  have hEq2hi : Real.exp ((97/53 : ℝ) * (Real.pi/2)) ≤ (886141519/50000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq2hi)
      (exp_upper (143742683/50000000 : ℝ) (886141519/50000000 : ℝ) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  unfold PhiS PhiK PhiA PhiC PhiD
  norm_num
  linarith

theorem T7R85_06 : CertRow85 (20/100) (201/100) (53/50) 0 := by
  apply CertRow85_of_lt (by norm_num) (by norm_num) (by norm_num)
  have h1 := pi_div_two_bounds.1
  have h2 := pi_div_two_bounds.2
  have h3 := pi_sub_three_bounds.1
  have h4 := pi_sub_three_bounds.2
  have h5 := s_bounds.1
  have h6 := s_bounds.2
  have hq1lo : (74464637/25000000 : ℝ) ≤ (201/106 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq1hi : (201/106 : ℝ) * (Real.pi/2) ≤ (297858549/100000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hEq1lo : (61437461/3125000 : ℝ) ≤ Real.exp ((201/106 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (74464637/25000000 : ℝ) (61437461/3125000 : ℝ) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq1lo)
  have hEq1hi : Real.exp ((201/106 : ℝ) * (Real.pi/2)) ≤ (491499693/25000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq1hi)
      (exp_upper (297858549/100000000 : ℝ) (491499693/25000000 : ℝ) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  have hq2lo : (134110441/50000000 : ℝ) ≤ (181/106 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq2hi : (181/106 : ℝ) * (Real.pi/2) ≤ (268220883/100000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hEq2lo : (730867237/50000000 : ℝ) ≤ Real.exp ((181/106 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (134110441/50000000 : ℝ) (730867237/50000000 : ℝ) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq2lo)
  have hEq2hi : Real.exp ((181/106 : ℝ) * (Real.pi/2)) ≤ (146173449/10000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq2hi)
      (exp_upper (268220883/100000000 : ℝ) (146173449/10000000 : ℝ) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  unfold PhiS PhiK PhiA PhiC PhiD
  norm_num
  linarith

theorem T7R85_07 : CertRow85 (25/100) (177/100) (53/50) 0 := by
  apply CertRow85_of_lt (by norm_num) (by norm_num) (by norm_num)
  have h1 := pi_div_two_bounds.1
  have h2 := pi_div_two_bounds.2
  have h3 := pi_sub_three_bounds.1
  have h4 := pi_sub_three_bounds.2
  have h5 := s_bounds.1
  have h6 := s_bounds.2
  have hq1lo : (65573337/25000000 : ℝ) ≤ (177/106 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq1hi : (177/106 : ℝ) * (Real.pi/2) ≤ (262293349/100000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hEq1lo : (1377607621/100000000 : ℝ) ≤ Real.exp ((177/106 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (65573337/25000000 : ℝ) (1377607621/100000000 : ℝ) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq1lo)
  have hEq1hi : Real.exp ((177/106 : ℝ) * (Real.pi/2)) ≤ (344401909/25000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq1hi)
      (exp_upper (262293349/100000000 : ℝ) (344401909/25000000 : ℝ) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  have hq2lo : (45049253/20000000 : ℝ) ≤ (76/53 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq2hi : (76/53 : ℝ) * (Real.pi/2) ≤ (112623133/50000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hEq2lo : (743057/78125 : ℝ) ≤ Real.exp ((76/53 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (45049253/20000000 : ℝ) (743057/78125 : ℝ) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq2lo)
  have hEq2hi : Real.exp ((76/53 : ℝ) * (Real.pi/2)) ≤ (95111297/10000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq2hi)
      (exp_upper (112623133/50000000 : ℝ) (95111297/10000000 : ℝ) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  unfold PhiS PhiK PhiA PhiC PhiD
  norm_num
  linarith

theorem T7R85_08 : CertRow85 (30/100) (158/100) (53/50) 0 := by
  apply CertRow85_of_lt (by norm_num) (by norm_num) (by norm_num)
  have h1 := pi_div_two_bounds.1
  have h2 := pi_div_two_bounds.2
  have h3 := pi_sub_three_bounds.1
  have h4 := pi_sub_three_bounds.2
  have h5 := s_bounds.1
  have h6 := s_bounds.2
  have hq1lo : (46827513/20000000 : ℝ) ≤ (79/53 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq1hi : (79/53 : ℝ) * (Real.pi/2) ≤ (117068783/50000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hEq1lo : (1039552733/100000000 : ℝ) ≤ Real.exp ((79/53 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (46827513/20000000 : ℝ) (1039552733/100000000 : ℝ) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq1lo)
  have hEq1hi : Real.exp ((79/53 : ℝ) * (Real.pi/2)) ≤ (207910549/20000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq1hi)
      (exp_upper (117068783/50000000 : ℝ) (207910549/20000000 : ℝ) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  have hq2lo : (37936213/20000000 : ℝ) ≤ (64/53 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq2hi : (64/53 : ℝ) * (Real.pi/2) ≤ (94840533/50000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hEq2lo : (26658419/4000000 : ℝ) ≤ Real.exp ((64/53 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (37936213/20000000 : ℝ) (26658419/4000000 : ℝ) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq2lo)
  have hEq2hi : Real.exp ((64/53 : ℝ) * (Real.pi/2)) ≤ (333230241/50000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq2hi)
      (exp_upper (94840533/50000000 : ℝ) (333230241/50000000 : ℝ) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  unfold PhiS PhiK PhiA PhiC PhiD
  norm_num
  linarith

theorem T7R85_09 : CertRow85 (35/100) (142/100) (53/50) 0 := by
  apply CertRow85_of_lt (by norm_num) (by norm_num) (by norm_num)
  have h1 := pi_div_two_bounds.1
  have h2 := pi_div_two_bounds.2
  have h3 := pi_sub_three_bounds.1
  have h4 := pi_sub_three_bounds.2
  have h5 := s_bounds.1
  have h6 := s_bounds.2
  have hq1lo : (26303429/12500000 : ℝ) ≤ (71/53 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq1hi : (71/53 : ℝ) * (Real.pi/2) ≤ (210427433/100000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hEq1lo : (820114943/100000000 : ℝ) ≤ Real.exp ((71/53 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (26303429/12500000 : ℝ) (820114943/100000000 : ℝ) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq1lo)
  have hEq1hi : Real.exp ((71/53 : ℝ) * (Real.pi/2)) ≤ (820114953/100000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq1hi)
      (exp_upper (210427433/100000000 : ℝ) (820114953/100000000 : ℝ) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  have hq2lo : (39640379/25000000 : ℝ) ≤ (107/106 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq2hi : (107/106 : ℝ) * (Real.pi/2) ≤ (158561517/100000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hEq2lo : (61028673/12500000 : ℝ) ≤ Real.exp ((107/106 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (39640379/25000000 : ℝ) (61028673/12500000 : ℝ) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq2lo)
  have hEq2hi : Real.exp ((107/106 : ℝ) * (Real.pi/2)) ≤ (48822939/10000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq2hi)
      (exp_upper (158561517/100000000 : ℝ) (48822939/10000000 : ℝ) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  unfold PhiS PhiK PhiA PhiC PhiD
  norm_num
  linarith

theorem T7R85_10 : CertRow85 (40/100) (129/100) (53/50) 0 := by
  apply CertRow85_of_lt (by norm_num) (by norm_num) (by norm_num)
  have h1 := pi_div_two_bounds.1
  have h2 := pi_div_two_bounds.2
  have h3 := pi_sub_three_bounds.1
  have h4 := pi_sub_three_bounds.2
  have h5 := s_bounds.1
  have h6 := s_bounds.2
  have hq1lo : (191162949/100000000 : ℝ) ≤ (129/106 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq1hi : (129/106 : ℝ) * (Real.pi/2) ≤ (3823259/2000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hEq1lo : (135282037/20000000 : ℝ) ≤ Real.exp ((129/106 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (191162949/100000000 : ℝ) (135282037/20000000 : ℝ) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq1lo)
  have hEq1hi : Real.exp ((129/106 : ℝ) * (Real.pi/2)) ≤ (676410193/100000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq1hi)
      (exp_upper (3823259/2000000 : ℝ) (676410193/100000000 : ℝ) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  have hq2lo : (515186/390625 : ℝ) ≤ (89/106 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq2hi : (89/106 : ℝ) * (Real.pi/2) ≤ (131887617/100000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hEq2lo : (373921673/100000000 : ℝ) ≤ Real.exp ((89/106 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (515186/390625 : ℝ) (373921673/100000000 : ℝ) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq2lo)
  have hEq2hi : Real.exp ((89/106 : ℝ) * (Real.pi/2)) ≤ (186960839/50000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq2hi)
      (exp_upper (131887617/100000000 : ℝ) (186960839/50000000 : ℝ) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  unfold PhiS PhiK PhiA PhiC PhiD
  norm_num
  linarith

theorem T7R85_11 : CertRow85 (45/100) (118/100) (53/50) 0 := by
  apply CertRow85_of_lt (by norm_num) (by norm_num) (by norm_num)
  have h1 := pi_div_two_bounds.1
  have h2 := pi_div_two_bounds.2
  have h3 := pi_sub_three_bounds.1
  have h4 := pi_sub_three_bounds.2
  have h5 := s_bounds.1
  have h6 := s_bounds.2
  have hq1lo : (21857779/12500000 : ℝ) ≤ (59/53 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq1hi : (59/53 : ℝ) * (Real.pi/2) ≤ (174862233/100000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hEq1lo : (574668013/100000000 : ℝ) ≤ Real.exp ((59/53 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (21857779/12500000 : ℝ) (574668013/100000000 : ℝ) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq1lo)
  have hEq1hi : Real.exp ((59/53 : ℝ) * (Real.pi/2)) ≤ (28733401/5000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq1hi)
      (exp_upper (174862233/100000000 : ℝ) (28733401/5000000 : ℝ) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  have hq2lo : (54088741/50000000 : ℝ) ≤ (73/106 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq2hi : (73/106 : ℝ) * (Real.pi/2) ≤ (108177483/100000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hEq2lo : (147495523/50000000 : ℝ) ≤ Real.exp ((73/106 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (54088741/50000000 : ℝ) (147495523/50000000 : ℝ) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq2lo)
  have hEq2hi : Real.exp ((73/106 : ℝ) * (Real.pi/2)) ≤ (5899821/2000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq2hi)
      (exp_upper (108177483/100000000 : ℝ) (5899821/2000000 : ℝ) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  unfold PhiS PhiK PhiA PhiC PhiD
  norm_num
  linarith

theorem T7R85_12 : CertRow85 (50/100) (108/100) (53/50) 0 := by
  apply CertRow85_of_lt (by norm_num) (by norm_num) (by norm_num)
  have h1 := pi_div_two_bounds.1
  have h2 := pi_div_two_bounds.2
  have h3 := pi_sub_three_bounds.1
  have h4 := pi_sub_three_bounds.2
  have h5 := s_bounds.1
  have h6 := s_bounds.2
  have hq1lo : (160043399/100000000 : ℝ) ≤ (54/53 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq1hi : (54/53 : ℝ) * (Real.pi/2) ≤ (800217/500000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hEq1lo : (99103649/20000000 : ℝ) ≤ Real.exp ((54/53 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (160043399/100000000 : ℝ) (99103649/20000000 : ℝ) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq1lo)
  have hEq1hi : Real.exp ((54/53 : ℝ) * (Real.pi/2)) ≤ (495518251/100000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq1hi)
      (exp_upper (800217/500000 : ℝ) (495518251/100000000 : ℝ) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  have hq2lo : (5371827/6250000 : ℝ) ≤ (29/53 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq2hi : (29/53 : ℝ) * (Real.pi/2) ≤ (85949233/100000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hEq2lo : (118098063/50000000 : ℝ) ≤ Real.exp ((29/53 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (5371827/6250000 : ℝ) (118098063/50000000 : ℝ) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq2lo)
  have hEq2hi : Real.exp ((29/53 : ℝ) * (Real.pi/2)) ≤ (23619613/10000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq2hi)
      (exp_upper (85949233/100000000 : ℝ) (23619613/10000000 : ℝ) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  unfold PhiS PhiK PhiA PhiC PhiD
  norm_num
  linarith

theorem T7R85_13 : CertRow85 (55/100) (100/100) (53/50) 0 := by
  apply CertRow85_of_lt (by norm_num) (by norm_num) (by norm_num)
  have h1 := pi_div_two_bounds.1
  have h2 := pi_div_two_bounds.2
  have h3 := pi_sub_three_bounds.1
  have h4 := pi_sub_three_bounds.2
  have h5 := s_bounds.1
  have h6 := s_bounds.2
  have hq1lo : (37047083/25000000 : ℝ) ≤ (50/53 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq1hi : (50/53 : ℝ) * (Real.pi/2) ≤ (148188333/100000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hEq1lo : (440122679/100000000 : ℝ) ≤ Real.exp ((50/53 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (37047083/25000000 : ℝ) (440122679/100000000 : ℝ) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq1lo)
  have hEq1hi : Real.exp ((50/53 : ℝ) * (Real.pi/2)) ≤ (88024537/20000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq1hi)
      (exp_upper (148188333/100000000 : ℝ) (88024537/20000000 : ℝ) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  have hq2lo : (66684749/100000000 : ℝ) ≤ (45/106 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq2hi : (45/106 : ℝ) * (Real.pi/2) ≤ (266739/400000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hEq2lo : (97404313/50000000 : ℝ) ≤ Real.exp ((45/106 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (66684749/100000000 : ℝ) (97404313/50000000 : ℝ) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq2lo)
  have hEq2hi : Real.exp ((45/106 : ℝ) * (Real.pi/2)) ≤ (194808629/100000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq2hi)
      (exp_upper (266739/400000 : ℝ) (194808629/100000000 : ℝ) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  unfold PhiS PhiK PhiA PhiC PhiD
  norm_num
  linarith

theorem T7R85_14 : CertRow85 (60/100) (92/100) (53/50) 0 := by
  apply CertRow85_of_lt (by norm_num) (by norm_num) (by norm_num)
  have h1 := pi_div_two_bounds.1
  have h2 := pi_div_two_bounds.2
  have h3 := pi_sub_three_bounds.1
  have h4 := pi_sub_three_bounds.2
  have h5 := s_bounds.1
  have h6 := s_bounds.2
  have hq1lo : (68166633/50000000 : ℝ) ≤ (46/53 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq1hi : (46/53 : ℝ) * (Real.pi/2) ≤ (136333267/100000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hEq1lo : (78183993/20000000 : ℝ) ≤ Real.exp ((46/53 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (68166633/50000000 : ℝ) (78183993/20000000 : ℝ) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq1lo)
  have hEq1hi : Real.exp ((46/53 : ℝ) * (Real.pi/2)) ≤ (390919969/100000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq1hi)
      (exp_upper (136333267/100000000 : ℝ) (390919969/100000000 : ℝ) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  have hq2lo : (23710133/50000000 : ℝ) ≤ (16/53 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq2hi : (16/53 : ℝ) * (Real.pi/2) ≤ (47420267/100000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hEq2lo : (160673257/100000000 : ℝ) ≤ Real.exp ((16/53 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (23710133/50000000 : ℝ) (160673257/100000000 : ℝ) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq2lo)
  have hEq2hi : Real.exp ((16/53 : ℝ) * (Real.pi/2)) ≤ (8033663/5000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq2hi)
      (exp_upper (47420267/100000000 : ℝ) (8033663/5000000 : ℝ) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  unfold PhiS PhiK PhiA PhiC PhiD
  norm_num
  linarith

theorem T7R85_15 : CertRow85 (65/100) (85/100) (53/50) 0 := by
  apply CertRow85_of_lt (by norm_num) (by norm_num) (by norm_num)
  have h1 := pi_div_two_bounds.1
  have h2 := pi_div_two_bounds.2
  have h3 := pi_sub_three_bounds.1
  have h4 := pi_sub_three_bounds.2
  have h5 := s_bounds.1
  have h6 := s_bounds.2
  have hq1lo : (62980041/50000000 : ℝ) ≤ (85/106 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq1hi : (85/106 : ℝ) * (Real.pi/2) ≤ (125960083/100000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hEq1lo : (352401449/100000000 : ℝ) ≤ Real.exp ((85/106 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (62980041/50000000 : ℝ) (352401449/100000000 : ℝ) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq1lo)
  have hEq1hi : Real.exp ((85/106 : ℝ) * (Real.pi/2)) ≤ (352401453/100000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq1hi)
      (exp_upper (125960083/100000000 : ℝ) (352401453/100000000 : ℝ) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  have hq2lo : (14818833/50000000 : ℝ) ≤ (10/53 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq2hi : (10/53 : ℝ) * (Real.pi/2) ≤ (29637667/100000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hEq2lo : (67248833/50000000 : ℝ) ≤ Real.exp ((10/53 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (14818833/50000000 : ℝ) (67248833/50000000 : ℝ) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq2lo)
  have hEq2hi : Real.exp ((10/53 : ℝ) * (Real.pi/2)) ≤ (33624417/25000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq2hi)
      (exp_upper (29637667/100000000 : ℝ) (33624417/25000000 : ℝ) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  unfold PhiS PhiK PhiA PhiC PhiD
  norm_num
  linarith

theorem T7R85_16 : CertRow85 (70/100) (79/100) (53/50) 0 := by
  apply CertRow85_of_lt (by norm_num) (by norm_num) (by norm_num)
  have h1 := pi_div_two_bounds.1
  have h2 := pi_div_two_bounds.2
  have h3 := pi_sub_three_bounds.1
  have h4 := pi_sub_three_bounds.2
  have h5 := s_bounds.1
  have h6 := s_bounds.2
  have hq1lo : (58534391/50000000 : ℝ) ≤ (79/106 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq1hi : (79/106 : ℝ) * (Real.pi/2) ≤ (117068783/100000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hEq1lo : (64484191/20000000 : ℝ) ≤ Real.exp ((79/106 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (58534391/50000000 : ℝ) (64484191/20000000 : ℝ) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq1lo)
  have hEq1hi : Real.exp ((79/106 : ℝ) * (Real.pi/2)) ≤ (322420959/100000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq1hi)
      (exp_upper (117068783/100000000 : ℝ) (322420959/100000000 : ℝ) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  have hq2lo : (13336949/100000000 : ℝ) ≤ (9/106 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq2hi : (9/106 : ℝ) * (Real.pi/2) ≤ (266739/2000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hEq2lo : (28566803/25000000 : ℝ) ≤ Real.exp ((9/106 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (13336949/100000000 : ℝ) (28566803/25000000 : ℝ) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq2lo)
  have hEq2hi : Real.exp ((9/106 : ℝ) * (Real.pi/2)) ≤ (57133607/50000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq2hi)
      (exp_upper (266739/2000000 : ℝ) (57133607/50000000 : ℝ) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  unfold PhiS PhiK PhiA PhiC PhiD
  norm_num
  linarith

theorem T7R85_17 : CertRow85 (745/1000) (745/1000) (93/100) 0 := by
  apply CertRow85_of_eq (by norm_num) (by norm_num)
  have h1 := pi_div_two_bounds.1
  have h2 := pi_div_two_bounds.2
  have h3 := pi_sub_three_bounds.1
  have h4 := pi_sub_three_bounds.2
  have h5 := s_bounds.1
  have h6 := s_bounds.2
  have hq1lo : (3932269/3125000 : ℝ) ≤ (149/186 : ℝ) * (Real.pi/2) := by
    nlinarith [Real.pi_gt_d20]
  have hq1hi : (149/186 : ℝ) * (Real.pi/2) ≤ (125832609/100000000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hEq1lo : (70390503/20000000 : ℝ) ≤ Real.exp ((149/186 : ℝ) * (Real.pi/2)) :=
    le_trans (exp_lower (3932269/3125000 : ℝ) (70390503/20000000 : ℝ) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ]))
      (Real.exp_le_exp.mpr hq1lo)
  have hEq1hi : Real.exp ((149/186 : ℝ) * (Real.pi/2)) ≤ (351952519/100000000 : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hq1hi)
      (exp_upper (125832609/100000000 : ℝ) (351952519/100000000 : ℝ) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ]))
  unfold PhiS PhiK PhiA PhiC PhiD
  norm_num
  linarith

theorem HBTable7_cert85 : ∀ p ∈ Work.ZeroFreeTables.tableR Work.ZeroFreeTables.hbTable7,
    ∃ lam : ℝ, Work.ZeroFreeTables.CertRow85 p.1 p.2 lam 0 := by
  intro p hp
  simp only [tableR, hbTable7, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with ⟨a, ha, rfl⟩
  rcases ha with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨(53/50 : ℝ), ?_⟩
    convert T7R85_01 using 1 <;> norm_num
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨(53/50 : ℝ), ?_⟩
    convert T7R85_02 using 1 <;> norm_num
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨(53/50 : ℝ), ?_⟩
    convert T7R85_03 using 1 <;> norm_num
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨(53/50 : ℝ), ?_⟩
    convert T7R85_04 using 1 <;> norm_num
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨(53/50 : ℝ), ?_⟩
    convert T7R85_05 using 1 <;> norm_num
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨(53/50 : ℝ), ?_⟩
    convert T7R85_06 using 1 <;> norm_num
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨(53/50 : ℝ), ?_⟩
    convert T7R85_07 using 1 <;> norm_num
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨(53/50 : ℝ), ?_⟩
    convert T7R85_08 using 1 <;> norm_num
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨(53/50 : ℝ), ?_⟩
    convert T7R85_09 using 1 <;> norm_num
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨(53/50 : ℝ), ?_⟩
    convert T7R85_10 using 1 <;> norm_num
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨(53/50 : ℝ), ?_⟩
    convert T7R85_11 using 1 <;> norm_num
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨(53/50 : ℝ), ?_⟩
    convert T7R85_12 using 1 <;> norm_num
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨(53/50 : ℝ), ?_⟩
    convert T7R85_13 using 1 <;> norm_num
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨(53/50 : ℝ), ?_⟩
    convert T7R85_14 using 1 <;> norm_num
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨(53/50 : ℝ), ?_⟩
    convert T7R85_15 using 1 <;> norm_num
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨(53/50 : ℝ), ?_⟩
    convert T7R85_16 using 1 <;> norm_num
  · subst h
    simp only [Prod.fst, Prod.snd, Prod.mk.eta]
    refine ⟨(93/100 : ℝ), ?_⟩
    convert T7R85_17 using 1 <;> norm_num

end Work.ZeroFreeTables
