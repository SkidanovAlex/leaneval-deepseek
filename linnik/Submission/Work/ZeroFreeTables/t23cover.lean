/-
# ZeroFreeTables — t23cover

`Work.ZeroFreeTables.RowCover`: the row data of HB Tables 2/3 cover the two ranges of
`HBTable2and3` (see `t23Defs`).  Both conjuncts are finite covering statements: the range is cut
into consecutive windows and one row is used per window; the transcendental comparisons
`k·log(1/c) ≤ v` are discharged by the numeric lemmas of `t23coverAux` (the module comment
there records the two chains, i.e. which row covers which window).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.t23Defs
import Submission.Work.ZeroFreeTables.t23coverAux

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

/-! ## The numeric comparisons of the first chain

`2 log (1/c) ≤ v` for the left endpoint `c` of a window and the value `v` of the row used in
it. -/

lemma num1_1 : 2 * Real.log (1 / ((0.0068 : ℝ))) ≤ ((10.0 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_2 : 2 * Real.log (1 / ((0.0102 : ℝ))) ≤ ((9.24 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_3 : 2 * Real.log (1 / ((0.0145 : ℝ))) ≤ ((8.5 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_4 : 2 * Real.log (1 / ((0.02 : ℝ))) ≤ ((7.867 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_5 : 2 * Real.log (1 / ((0.026 : ℝ))) ≤ ((7303/1000 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_6 : 2 * Real.log (1 / ((2649/100000 : ℝ))) ≤ ((7.262 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_7 : 2 * Real.log (1 / ((0.035 : ℝ))) ≤ ((6.728 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_8 : 2 * Real.log (1 / ((0.044 : ℝ))) ≤ ((6.259 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_9 : 2 * Real.log (1 / ((0.054 : ℝ))) ≤ ((5.849 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_10 : 2 * Real.log (1 / ((0.064 : ℝ))) ≤ ((5501/1000 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_11 : 2 * Real.log (1 / ((3211/50000 : ℝ))) ≤ ((5.491 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_12 : 2 * Real.log (1 / ((0.075 : ℝ))) ≤ ((648/125 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_13 : 2 * Real.log (1 / ((7503/100000 : ℝ))) ≤ ((5.18 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_14 : 2 * Real.log (1 / ((0.086 : ℝ))) ≤ ((4.909 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_15 : 2 * Real.log (1 / ((0.097 : ℝ))) ≤ ((4.674 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_16 : 2 * Real.log (1 / ((0.107 : ℝ))) ≤ ((4473/1000 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_17 : 2 * Real.log (1 / ((2141/20000 : ℝ))) ≤ ((4.469 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_18 : 2 * Real.log (1 / ((0.117 : ℝ))) ≤ ((859/200 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_19 : 2 * Real.log (1 / ((11701/100000 : ℝ))) ≤ ((4.291 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_20 : 2 * Real.log (1 / ((0.126 : ℝ))) ≤ ((2073/500 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_21 : 2 * Real.log (1 / ((3161/25000 : ℝ))) ≤ ((4.136 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_22 : 2 * Real.log (1 / ((0.135 : ℝ))) ≤ ((501/125 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_23 : 2 * Real.log (1 / ((13527/100000 : ℝ))) ≤ ((4.001 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_24 : 2 * Real.log (1 / ((0.144 : ℝ))) ≤ ((3.883 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_25 : 2 * Real.log (1 / ((0.151 : ℝ))) ≤ ((473/125 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_26 : 2 * Real.log (1 / ((3777/25000 : ℝ))) ≤ ((3.78 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_27 : 2 * Real.log (1 / ((0.158 : ℝ))) ≤ ((1847/500 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_28 : 2 * Real.log (1 / ((15803/100000 : ℝ))) ≤ ((3.69 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_29 : 2 * Real.log (1 / ((0.164 : ℝ))) ≤ ((3619/1000 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_30 : 2 * Real.log (1 / ((411/2500 : ℝ))) ≤ ((3.611 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_31 : 2 * Real.log (1 / ((0.17 : ℝ))) ≤ ((3547/1000 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_32 : 2 * Real.log (1 / ((17017/100000 : ℝ))) ≤ ((3.542 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_33 : 2 * Real.log (1 / ((0.175 : ℝ))) ≤ ((3489/1000 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_34 : 2 * Real.log (1 / ((2193/12500 : ℝ))) ≤ ((3.481 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_35 : 2 * Real.log (1 / ((0.18 : ℝ))) ≤ ((3433/1000 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_36 : 2 * Real.log (1 / ((3603/20000 : ℝ))) ≤ ((3.428 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_37 : 2 * Real.log (1 / ((0.184 : ℝ))) ≤ ((3389/1000 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_38 : 2 * Real.log (1 / ((9217/50000 : ℝ))) ≤ ((3.382 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_39 : 2 * Real.log (1 / ((0.188 : ℝ))) ≤ ((1673/500 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_40 : 2 * Real.log (1 / ((588/3125 : ℝ))) ≤ ((3.341 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_41 : 2 * Real.log (1 / ((0.192 : ℝ))) ≤ ((3.305 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_42 : 2 * Real.log (1 / ((0.195 : ℝ))) ≤ ((3.273 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num1_43 : 2 * Real.log (1 / ((0.198 : ℝ))) ≤ ((3.244 : ℝ)) := by
  refine two_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

/-! ## The windows of the first chain -/

lemma win1_0 {x : ℝ} : min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((10.9 : ℝ)) := by
  exact le_trans (min_le_left _ _) (four_exp_one_le (by norm_num))

lemma win1_1 {x : ℝ} (h1 : ((0.0068 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((10.0 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((0.0068 : ℝ))) (by norm_num) h1 num1_1)

lemma win1_2 {x : ℝ} (h1 : ((0.0102 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((9.24 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((0.0102 : ℝ))) (by norm_num) h1 num1_2)

lemma win1_3 {x : ℝ} (h1 : ((0.0145 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((8.5 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((0.0145 : ℝ))) (by norm_num) h1 num1_3)

lemma win1_4 {x : ℝ} (h1 : ((0.02 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((7.867 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((0.02 : ℝ))) (by norm_num) h1 num1_4)

lemma win1_5 {x : ℝ} (h1 : ((0.026 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((7303/1000 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((0.026 : ℝ))) (by norm_num) h1 num1_5)

lemma win1_6 {x : ℝ} (h1 : ((2649/100000 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((7.262 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((2649/100000 : ℝ))) (by norm_num) h1 num1_6)

lemma win1_7 {x : ℝ} (h1 : ((0.035 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((6.728 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((0.035 : ℝ))) (by norm_num) h1 num1_7)

lemma win1_8 {x : ℝ} (h1 : ((0.044 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((6.259 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((0.044 : ℝ))) (by norm_num) h1 num1_8)

lemma win1_9 {x : ℝ} (h1 : ((0.054 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((5.849 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((0.054 : ℝ))) (by norm_num) h1 num1_9)

lemma win1_10 {x : ℝ} (h1 : ((0.064 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((5501/1000 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((0.064 : ℝ))) (by norm_num) h1 num1_10)

lemma win1_11 {x : ℝ} (h1 : ((3211/50000 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((5.491 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((3211/50000 : ℝ))) (by norm_num) h1 num1_11)

lemma win1_12 {x : ℝ} (h1 : ((0.075 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((648/125 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((0.075 : ℝ))) (by norm_num) h1 num1_12)

lemma win1_13 {x : ℝ} (h1 : ((7503/100000 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((5.18 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((7503/100000 : ℝ))) (by norm_num) h1 num1_13)

lemma win1_14 {x : ℝ} (h1 : ((0.086 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((4.909 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((0.086 : ℝ))) (by norm_num) h1 num1_14)

lemma win1_15 {x : ℝ} (h1 : ((0.097 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((4.674 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((0.097 : ℝ))) (by norm_num) h1 num1_15)

lemma win1_16 {x : ℝ} (h1 : ((0.107 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((4473/1000 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((0.107 : ℝ))) (by norm_num) h1 num1_16)

lemma win1_17 {x : ℝ} (h1 : ((2141/20000 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((4.469 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((2141/20000 : ℝ))) (by norm_num) h1 num1_17)

lemma win1_18 {x : ℝ} (h1 : ((0.117 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((859/200 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((0.117 : ℝ))) (by norm_num) h1 num1_18)

lemma win1_19 {x : ℝ} (h1 : ((11701/100000 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((4.291 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((11701/100000 : ℝ))) (by norm_num) h1 num1_19)

lemma win1_20 {x : ℝ} (h1 : ((0.126 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((2073/500 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((0.126 : ℝ))) (by norm_num) h1 num1_20)

lemma win1_21 {x : ℝ} (h1 : ((3161/25000 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((4.136 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((3161/25000 : ℝ))) (by norm_num) h1 num1_21)

lemma win1_22 {x : ℝ} (h1 : ((0.135 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((501/125 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((0.135 : ℝ))) (by norm_num) h1 num1_22)

lemma win1_23 {x : ℝ} (h1 : ((13527/100000 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((4.001 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((13527/100000 : ℝ))) (by norm_num) h1 num1_23)

lemma win1_24 {x : ℝ} (h1 : ((0.144 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((3.883 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((0.144 : ℝ))) (by norm_num) h1 num1_24)

lemma win1_25 {x : ℝ} (h1 : ((0.151 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((473/125 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((0.151 : ℝ))) (by norm_num) h1 num1_25)

lemma win1_26 {x : ℝ} (h1 : ((3777/25000 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((3.78 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((3777/25000 : ℝ))) (by norm_num) h1 num1_26)

lemma win1_27 {x : ℝ} (h1 : ((0.158 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((1847/500 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((0.158 : ℝ))) (by norm_num) h1 num1_27)

lemma win1_28 {x : ℝ} (h1 : ((15803/100000 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((3.69 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((15803/100000 : ℝ))) (by norm_num) h1 num1_28)

lemma win1_29 {x : ℝ} (h1 : ((0.164 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((3619/1000 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((0.164 : ℝ))) (by norm_num) h1 num1_29)

lemma win1_30 {x : ℝ} (h1 : ((411/2500 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((3.611 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((411/2500 : ℝ))) (by norm_num) h1 num1_30)

lemma win1_31 {x : ℝ} (h1 : ((0.17 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((3547/1000 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((0.17 : ℝ))) (by norm_num) h1 num1_31)

lemma win1_32 {x : ℝ} (h1 : ((17017/100000 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((3.542 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((17017/100000 : ℝ))) (by norm_num) h1 num1_32)

lemma win1_33 {x : ℝ} (h1 : ((0.175 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((3489/1000 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((0.175 : ℝ))) (by norm_num) h1 num1_33)

lemma win1_34 {x : ℝ} (h1 : ((2193/12500 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((3.481 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((2193/12500 : ℝ))) (by norm_num) h1 num1_34)

lemma win1_35 {x : ℝ} (h1 : ((0.18 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((3433/1000 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((0.18 : ℝ))) (by norm_num) h1 num1_35)

lemma win1_36 {x : ℝ} (h1 : ((3603/20000 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((3.428 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((3603/20000 : ℝ))) (by norm_num) h1 num1_36)

lemma win1_37 {x : ℝ} (h1 : ((0.184 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((3389/1000 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((0.184 : ℝ))) (by norm_num) h1 num1_37)

lemma win1_38 {x : ℝ} (h1 : ((9217/50000 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((3.382 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((9217/50000 : ℝ))) (by norm_num) h1 num1_38)

lemma win1_39 {x : ℝ} (h1 : ((0.188 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((1673/500 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((0.188 : ℝ))) (by norm_num) h1 num1_39)

lemma win1_40 {x : ℝ} (h1 : ((588/3125 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((3.341 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((588/3125 : ℝ))) (by norm_num) h1 num1_40)

lemma win1_41 {x : ℝ} (h1 : ((0.192 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((3.305 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((0.192 : ℝ))) (by norm_num) h1 num1_41)

lemma win1_42 {x : ℝ} (h1 : ((0.195 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((3.273 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((0.195 : ℝ))) (by norm_num) h1 num1_42)

lemma win1_43 {x : ℝ} (h1 : ((0.198 : ℝ)) ≤ x) :
    min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ ((3.244 : ℝ)) := by
  exact le_trans (min_le_right _ _) (cover_min_log (c := ((0.198 : ℝ))) (by norm_num) h1 num1_43)

/-! ## The numeric comparisons of the second chain

`(3/2) log (1/c) ≤ v` for the left endpoint `c` of a window and the value `v` of the row used in
it. -/

lemma num2_1 : (3 / 2) * Real.log (1 / ((1 / 1000 : ℝ))) ≤ ((10.9 : ℝ)) := by
  refine three_halves_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num2_2 : (3 / 2) * Real.log (1 / ((0.0068 : ℝ))) ≤ ((7.867 : ℝ)) := by
  refine three_halves_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num2_3 : (3 / 2) * Real.log (1 / ((0.026 : ℝ))) ≤ ((5.491 : ℝ)) := by
  refine three_halves_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num2_4 : (3 / 2) * Real.log (1 / ((0.075 : ℝ))) ≤ ((4.001 : ℝ)) := by
  refine three_halves_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num2_5 : (3 / 2) * Real.log (1 / ((0.144 : ℝ))) ≤ ((3.244 : ℝ)) := by
  refine three_halves_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num2_6 : (3 / 2) * Real.log (1 / ((1 / 5 : ℝ))) ≤ ((273/100 : ℝ)) := by
  refine three_halves_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num2_7 : (3 / 2) * Real.log (1 / ((1 / 4 : ℝ))) ≤ ((233/100 : ℝ)) := by
  refine three_halves_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num2_8 : (3 / 2) * Real.log (1 / ((3 / 10 : ℝ))) ≤ ((199/100 : ℝ)) := by
  refine three_halves_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

lemma num2_9 : (3 / 2) * Real.log (1 / ((7 / 20 : ℝ))) ≤ ((169/100 : ℝ)) := by
  refine three_halves_log_inv_le (by norm_num) (by norm_num) ?_
  norm_num [Finset.sum_range_succ]

/-! ## The windows of the second chain

The five first rows lie in `t23rows`, the last four in `rowG`; every row has
`v ≥ 1.69 > 1294/1000`, so the constant part of the `max` is a `norm_num` fact. -/

lemma win2_1 {x : ℝ} (h1 : ((1 / 1000 : ℝ)) ≤ x) :
    max ((3 / 2) * Real.log (1 / x)) (1294 / 1000) ≤ ((10.9 : ℝ)) := by
  rw [max_le_iff]
  exact ⟨cover_max_log (c := ((1 / 1000 : ℝ))) (by norm_num) h1 num2_1, by norm_num⟩

lemma win2_2 {x : ℝ} (h1 : ((0.0068 : ℝ)) ≤ x) :
    max ((3 / 2) * Real.log (1 / x)) (1294 / 1000) ≤ ((7.867 : ℝ)) := by
  rw [max_le_iff]
  exact ⟨cover_max_log (c := ((0.0068 : ℝ))) (by norm_num) h1 num2_2, by norm_num⟩

lemma win2_3 {x : ℝ} (h1 : ((0.026 : ℝ)) ≤ x) :
    max ((3 / 2) * Real.log (1 / x)) (1294 / 1000) ≤ ((5.491 : ℝ)) := by
  rw [max_le_iff]
  exact ⟨cover_max_log (c := ((0.026 : ℝ))) (by norm_num) h1 num2_3, by norm_num⟩

lemma win2_4 {x : ℝ} (h1 : ((0.075 : ℝ)) ≤ x) :
    max ((3 / 2) * Real.log (1 / x)) (1294 / 1000) ≤ ((4.001 : ℝ)) := by
  rw [max_le_iff]
  exact ⟨cover_max_log (c := ((0.075 : ℝ))) (by norm_num) h1 num2_4, by norm_num⟩

lemma win2_5 {x : ℝ} (h1 : ((0.144 : ℝ)) ≤ x) :
    max ((3 / 2) * Real.log (1 / x)) (1294 / 1000) ≤ ((3.244 : ℝ)) := by
  rw [max_le_iff]
  exact ⟨cover_max_log (c := ((0.144 : ℝ))) (by norm_num) h1 num2_5, by norm_num⟩

lemma win2_6 {x : ℝ} (h1 : ((1 / 5 : ℝ)) ≤ x) :
    max ((3 / 2) * Real.log (1 / x)) (1294 / 1000) ≤ ((273/100 : ℝ)) := by
  rw [max_le_iff]
  exact ⟨cover_max_log (c := ((1 / 5 : ℝ))) (by norm_num) h1 num2_6, by norm_num⟩

lemma win2_7 {x : ℝ} (h1 : ((1 / 4 : ℝ)) ≤ x) :
    max ((3 / 2) * Real.log (1 / x)) (1294 / 1000) ≤ ((233/100 : ℝ)) := by
  rw [max_le_iff]
  exact ⟨cover_max_log (c := ((1 / 4 : ℝ))) (by norm_num) h1 num2_7, by norm_num⟩

lemma win2_8 {x : ℝ} (h1 : ((3 / 10 : ℝ)) ≤ x) :
    max ((3 / 2) * Real.log (1 / x)) (1294 / 1000) ≤ ((199/100 : ℝ)) := by
  rw [max_le_iff]
  exact ⟨cover_max_log (c := ((3 / 10 : ℝ))) (by norm_num) h1 num2_8, by norm_num⟩

lemma win2_9 {x : ℝ} (h1 : ((7 / 20 : ℝ)) ≤ x) :
    max ((3 / 2) * Real.log (1 / x)) (1294 / 1000) ≤ ((169/100 : ℝ)) := by
  rw [max_le_iff]
  exact ⟨cover_max_log (c := ((7 / 20 : ℝ))) (by norm_num) h1 num2_9, by norm_num⟩

/-! ## The first conjunct -/

theorem t23conj1 : ∀ x : ℝ, 0 < x → x ≤ 1 / 5 →
    ∃ p ∈ t23rows, x ≤ p.2.1 ∧ min (4 * Real.exp 1) (2 * Real.log (1 / x)) ≤ p.2.2 := by
  intro x hx0 hx5
  by_cases h0 : (x ≤ ((0.0068 : ℝ)))
  · exact ⟨((113/40 : ℝ), (0.0068 : ℝ), (10.9 : ℝ)), mem_t23_of_mem_rowE (by norm_num [rowE]), h0, win1_0⟩
  · simp only [not_le] at h0
    by_cases h1 : (x ≤ ((0.0102 : ℝ)))
    · exact ⟨((139/50 : ℝ), (0.0102 : ℝ), (10.0 : ℝ)), mem_t23_of_mem_rowE (by norm_num [rowE]), h1, win1_1 h0.le⟩
    · simp only [not_le] at h1
      by_cases h2 : (x ≤ ((0.0145 : ℝ)))
      · exact ⟨((549/200 : ℝ), (0.0145 : ℝ), (9.24 : ℝ)), mem_t23_of_mem_rowE (by norm_num [rowE]), h2, win1_2 h1.le⟩
      · simp only [not_le] at h2
        by_cases h3 : (x ≤ ((0.02 : ℝ)))
        · exact ⟨((2.7 : ℝ), (0.02 : ℝ), (8.5 : ℝ)), mem_t23_of_mem_rowE (by norm_num [rowE]), h3, win1_3 h2.le⟩
        · simp only [not_le] at h3
          by_cases h4 : (x ≤ ((0.026 : ℝ)))
          · exact ⟨((2.7 : ℝ), (0.026 : ℝ), (7.867 : ℝ)), mem_t23_of_mem_rowE (by norm_num [rowE]), h4, win1_4 h3.le⟩
          · simp only [not_le] at h4
            by_cases h5 : (x ≤ ((2649/100000 : ℝ)))
            · exact ⟨((27/10 : ℝ), (2649/100000 : ℝ), (7303/1000 : ℝ)), mem_t23_of_mem_rowF (by norm_num [rowF]), h5, win1_5 h4.le⟩
            · simp only [not_le] at h5
              by_cases h6 : (x ≤ ((0.035 : ℝ)))
              · exact ⟨((2.65 : ℝ), (0.035 : ℝ), (7.262 : ℝ)), mem_t23_of_mem_rowD (by norm_num [rowD]), h6, win1_6 h5.le⟩
              · simp only [not_le] at h6
                by_cases h7 : (x ≤ ((0.044 : ℝ)))
                · exact ⟨((2.6 : ℝ), (0.044 : ℝ), (6.728 : ℝ)), mem_t23_of_mem_rowD (by norm_num [rowD]), h7, win1_7 h6.le⟩
                · simp only [not_le] at h7
                  by_cases h8 : (x ≤ ((0.054 : ℝ)))
                  · exact ⟨((2.6 : ℝ), (0.054 : ℝ), (6.259 : ℝ)), mem_t23_of_mem_rowD (by norm_num [rowD]), h8, win1_8 h7.le⟩
                  · simp only [not_le] at h8
                    by_cases h9 : (x ≤ ((0.064 : ℝ)))
                    · exact ⟨((2.55 : ℝ), (0.064 : ℝ), (5.849 : ℝ)), mem_t23_of_mem_rowD (by norm_num [rowD]), h9, win1_9 h8.le⟩
                    · simp only [not_le] at h9
                      by_cases h10 : (x ≤ ((3211/50000 : ℝ)))
                      · exact ⟨((51/20 : ℝ), (3211/50000 : ℝ), (5501/1000 : ℝ)), mem_t23_of_mem_rowF (by norm_num [rowF]), h10, win1_10 h9.le⟩
                      · simp only [not_le] at h10
                        by_cases h11 : (x ≤ ((0.075 : ℝ)))
                        · exact ⟨((2.55 : ℝ), (0.075 : ℝ), (5.491 : ℝ)), mem_t23_of_mem_rowD (by norm_num [rowD]), h11, win1_11 h10.le⟩
                        · simp only [not_le] at h11
                          by_cases h12 : (x ≤ ((7503/100000 : ℝ)))
                          · exact ⟨((51/20 : ℝ), (7503/100000 : ℝ), (648/125 : ℝ)), mem_t23_of_mem_rowF (by norm_num [rowF]), h12, win1_12 h11.le⟩
                          · simp only [not_le] at h12
                            by_cases h13 : (x ≤ ((0.086 : ℝ)))
                            · exact ⟨((2.5 : ℝ), (0.086 : ℝ), (5.18 : ℝ)), mem_t23_of_mem_rowD (by norm_num [rowD]), h13, win1_13 h12.le⟩
                            · simp only [not_le] at h13
                              by_cases h14 : (x ≤ ((0.097 : ℝ)))
                              · exact ⟨((2.5 : ℝ), (0.097 : ℝ), (4.909 : ℝ)), mem_t23_of_mem_rowC (by norm_num [rowC]), h14, win1_14 h13.le⟩
                              · simp only [not_le] at h14
                                by_cases h15 : (x ≤ ((0.107 : ℝ)))
                                · exact ⟨((2.45 : ℝ), (0.107 : ℝ), (4.674 : ℝ)), mem_t23_of_mem_rowC (by norm_num [rowC]), h15, win1_15 h14.le⟩
                                · simp only [not_le] at h15
                                  by_cases h16 : (x ≤ ((2141/20000 : ℝ)))
                                  · exact ⟨((49/20 : ℝ), (2141/20000 : ℝ), (4473/1000 : ℝ)), mem_t23_of_mem_rowF (by norm_num [rowF]), h16, win1_16 h15.le⟩
                                  · simp only [not_le] at h16
                                    by_cases h17 : (x ≤ ((0.117 : ℝ)))
                                    · exact ⟨((2.45 : ℝ), (0.117 : ℝ), (4.469 : ℝ)), mem_t23_of_mem_rowC (by norm_num [rowC]), h17, win1_17 h16.le⟩
                                    · simp only [not_le] at h17
                                      by_cases h18 : (x ≤ ((11701/100000 : ℝ)))
                                      · exact ⟨((49/20 : ℝ), (11701/100000 : ℝ), (859/200 : ℝ)), mem_t23_of_mem_rowF (by norm_num [rowF]), h18, win1_18 h17.le⟩
                                      · simp only [not_le] at h18
                                        by_cases h19 : (x ≤ ((0.126 : ℝ)))
                                        · exact ⟨((2.4 : ℝ), (0.126 : ℝ), (4.291 : ℝ)), mem_t23_of_mem_rowC (by norm_num [rowC]), h19, win1_19 h18.le⟩
                                        · simp only [not_le] at h19
                                          by_cases h20 : (x ≤ ((3161/25000 : ℝ)))
                                          · exact ⟨((12/5 : ℝ), (3161/25000 : ℝ), (2073/500 : ℝ)), mem_t23_of_mem_rowF (by norm_num [rowF]), h20, win1_20 h19.le⟩
                                          · simp only [not_le] at h20
                                            by_cases h21 : (x ≤ ((0.135 : ℝ)))
                                            · exact ⟨((2.4 : ℝ), (0.135 : ℝ), (4.136 : ℝ)), mem_t23_of_mem_rowC (by norm_num [rowC]), h21, win1_21 h20.le⟩
                                            · simp only [not_le] at h21
                                              by_cases h22 : (x ≤ ((13527/100000 : ℝ)))
                                              · exact ⟨((12/5 : ℝ), (13527/100000 : ℝ), (501/125 : ℝ)), mem_t23_of_mem_rowF (by norm_num [rowF]), h22, win1_22 h21.le⟩
                                              · simp only [not_le] at h22
                                                by_cases h23 : (x ≤ ((0.144 : ℝ)))
                                                · exact ⟨((2.4 : ℝ), (0.144 : ℝ), (4.001 : ℝ)), mem_t23_of_mem_rowC (by norm_num [rowC]), h23, win1_23 h22.le⟩
                                                · simp only [not_le] at h23
                                                  by_cases h24 : (x ≤ ((0.151 : ℝ)))
                                                  · exact ⟨((2.4 : ℝ), (0.151 : ℝ), (3.883 : ℝ)), mem_t23_of_mem_rowB (by norm_num [rowB]), h24, win1_24 h23.le⟩
                                                  · simp only [not_le] at h24
                                                    by_cases h25 : (x ≤ ((3777/25000 : ℝ)))
                                                    · exact ⟨((12/5 : ℝ), (3777/25000 : ℝ), (473/125 : ℝ)), mem_t23_of_mem_rowF (by norm_num [rowF]), h25, win1_25 h24.le⟩
                                                    · simp only [not_le] at h25
                                                      by_cases h26 : (x ≤ ((0.158 : ℝ)))
                                                      · exact ⟨((2.35 : ℝ), (0.158 : ℝ), (3.78 : ℝ)), mem_t23_of_mem_rowB (by norm_num [rowB]), h26, win1_26 h25.le⟩
                                                      · simp only [not_le] at h26
                                                        by_cases h27 : (x ≤ ((15803/100000 : ℝ)))
                                                        · exact ⟨((47/20 : ℝ), (15803/100000 : ℝ), (1847/500 : ℝ)), mem_t23_of_mem_rowF (by norm_num [rowF]), h27, win1_27 h26.le⟩
                                                        · simp only [not_le] at h27
                                                          by_cases h28 : (x ≤ ((0.164 : ℝ)))
                                                          · exact ⟨((2.35 : ℝ), (0.164 : ℝ), (3.69 : ℝ)), mem_t23_of_mem_rowB (by norm_num [rowB]), h28, win1_28 h27.le⟩
                                                          · simp only [not_le] at h28
                                                            by_cases h29 : (x ≤ ((411/2500 : ℝ)))
                                                            · exact ⟨((47/20 : ℝ), (411/2500 : ℝ), (3619/1000 : ℝ)), mem_t23_of_mem_rowF (by norm_num [rowF]), h29, win1_29 h28.le⟩
                                                            · simp only [not_le] at h29
                                                              by_cases h30 : (x ≤ ((0.17 : ℝ)))
                                                              · exact ⟨((2.35 : ℝ), (0.17 : ℝ), (3.611 : ℝ)), mem_t23_of_mem_rowB (by norm_num [rowB]), h30, win1_30 h29.le⟩
                                                              · simp only [not_le] at h30
                                                                by_cases h31 : (x ≤ ((17017/100000 : ℝ)))
                                                                · exact ⟨((47/20 : ℝ), (17017/100000 : ℝ), (3547/1000 : ℝ)), mem_t23_of_mem_rowF (by norm_num [rowF]), h31, win1_31 h30.le⟩
                                                                · simp only [not_le] at h31
                                                                  by_cases h32 : (x ≤ ((0.175 : ℝ)))
                                                                  · exact ⟨((2.35 : ℝ), (0.175 : ℝ), (3.542 : ℝ)), mem_t23_of_mem_rowB (by norm_num [rowB]), h32, win1_32 h31.le⟩
                                                                  · simp only [not_le] at h32
                                                                    by_cases h33 : (x ≤ ((2193/12500 : ℝ)))
                                                                    · exact ⟨((47/20 : ℝ), (2193/12500 : ℝ), (3489/1000 : ℝ)), mem_t23_of_mem_rowF (by norm_num [rowF]), h33, win1_33 h32.le⟩
                                                                    · simp only [not_le] at h33
                                                                      by_cases h34 : (x ≤ ((0.18 : ℝ)))
                                                                      · exact ⟨((2.35 : ℝ), (0.18 : ℝ), (3.481 : ℝ)), mem_t23_of_mem_rowB (by norm_num [rowB]), h34, win1_34 h33.le⟩
                                                                      · simp only [not_le] at h34
                                                                        by_cases h35 : (x ≤ ((3603/20000 : ℝ)))
                                                                        · exact ⟨((47/20 : ℝ), (3603/20000 : ℝ), (3433/1000 : ℝ)), mem_t23_of_mem_rowF (by norm_num [rowF]), h35, win1_35 h34.le⟩
                                                                        · simp only [not_le] at h35
                                                                          by_cases h36 : (x ≤ ((0.184 : ℝ)))
                                                                          · exact ⟨((2.3 : ℝ), (0.184 : ℝ), (3.428 : ℝ)), mem_t23_of_mem_rowA (by norm_num [rowA]), h36, win1_36 h35.le⟩
                                                                          · simp only [not_le] at h36
                                                                            by_cases h37 : (x ≤ ((9217/50000 : ℝ)))
                                                                            · exact ⟨((23/10 : ℝ), (9217/50000 : ℝ), (3389/1000 : ℝ)), mem_t23_of_mem_rowF (by norm_num [rowF]), h37, win1_37 h36.le⟩
                                                                            · simp only [not_le] at h37
                                                                              by_cases h38 : (x ≤ ((0.188 : ℝ)))
                                                                              · exact ⟨((2.3 : ℝ), (0.188 : ℝ), (3.382 : ℝ)), mem_t23_of_mem_rowA (by norm_num [rowA]), h38, win1_38 h37.le⟩
                                                                              · simp only [not_le] at h38
                                                                                by_cases h39 : (x ≤ ((588/3125 : ℝ)))
                                                                                · exact ⟨((23/10 : ℝ), (588/3125 : ℝ), (1673/500 : ℝ)), mem_t23_of_mem_rowF (by norm_num [rowF]), h39, win1_39 h38.le⟩
                                                                                · simp only [not_le] at h39
                                                                                  by_cases h40 : (x ≤ ((0.192 : ℝ)))
                                                                                  · exact ⟨((2.3 : ℝ), (0.192 : ℝ), (3.341 : ℝ)), mem_t23_of_mem_rowA (by norm_num [rowA]), h40, win1_40 h39.le⟩
                                                                                  · simp only [not_le] at h40
                                                                                    by_cases h41 : (x ≤ ((0.195 : ℝ)))
                                                                                    · exact ⟨((2.3 : ℝ), (0.195 : ℝ), (3.305 : ℝ)), mem_t23_of_mem_rowA (by norm_num [rowA]), h41, win1_41 h40.le⟩
                                                                                    · simp only [not_le] at h41
                                                                                      by_cases h42 : (x ≤ ((0.198 : ℝ)))
                                                                                      · exact ⟨((2.3 : ℝ), (0.198 : ℝ), (3.273 : ℝ)), mem_t23_of_mem_rowA (by norm_num [rowA]), h42, win1_42 h41.le⟩
                                                                                      · simp only [not_le] at h42
                                                                                        · exact ⟨((2.3 : ℝ), (0.2 : ℝ), (3.244 : ℝ)), mem_t23_of_mem_rowA (by norm_num [rowA]), le_trans hx5 (by norm_num), win1_43 h42.le⟩

/-! ## The second conjunct -/

theorem t23conj2 : ∀ x : ℝ, 1 / 1000 ≤ x → x ≤ 2 / 5 →
    (∃ p ∈ t23rows, x ≤ p.2.1 ∧ max ((3 / 2) * Real.log (1 / x)) (1294 / 1000) ≤ p.2.2)
    ∨ (∃ p ∈ rowG, x ≤ p.2.1 ∧ max ((3 / 2) * Real.log (1 / x)) (1294 / 1000) ≤ p.2.2) := by
  intro x h1000 hx5
  by_cases hx2 : (x ≤ 1 / 5)
  · left
    by_cases h1 : (x ≤ ((0.0068 : ℝ)))
    · exact ⟨((113/40 : ℝ), (0.0068 : ℝ), (10.9 : ℝ)), mem_t23_of_mem_rowE (by norm_num [rowE]), h1, win2_1 h1000⟩
    · simp only [not_le] at h1
      by_cases h2 : (x ≤ ((0.026 : ℝ)))
      · exact ⟨((2.7 : ℝ), (0.026 : ℝ), (7.867 : ℝ)), mem_t23_of_mem_rowE (by norm_num [rowE]), h2, win2_2 h1.le⟩
      · simp only [not_le] at h2
        by_cases h3 : (x ≤ ((0.075 : ℝ)))
        · exact ⟨((2.55 : ℝ), (0.075 : ℝ), (5.491 : ℝ)), mem_t23_of_mem_rowD (by norm_num [rowD]), h3, win2_3 h2.le⟩
        · simp only [not_le] at h3
          by_cases h4 : (x ≤ ((0.144 : ℝ)))
          · exact ⟨((2.4 : ℝ), (0.144 : ℝ), (4.001 : ℝ)), mem_t23_of_mem_rowC (by norm_num [rowC]), h4, win2_4 h3.le⟩
          · simp only [not_le] at h4
            exact ⟨((2.3 : ℝ), (0.2 : ℝ), (3.244 : ℝ)), mem_t23_of_mem_rowA (by norm_num [rowA]), le_trans hx2 (by norm_num), win2_5 h4.le⟩
  · simp only [not_le] at hx2
    right
    by_cases h5 : (x ≤ ((1/4 : ℝ)))
    · exact ⟨((9/4 : ℝ), (1/4 : ℝ), (273/100 : ℝ)), by norm_num [rowG], h5, win2_6 hx2.le⟩
    · simp only [not_le] at h5
      by_cases h6 : (x ≤ ((3/10 : ℝ)))
      · exact ⟨((43/20 : ℝ), (3/10 : ℝ), (233/100 : ℝ)), by norm_num [rowG], h6, win2_7 h5.le⟩
      · simp only [not_le] at h6
        by_cases h7 : (x ≤ ((7/20 : ℝ)))
        · exact ⟨((21/10 : ℝ), (7/20 : ℝ), (199/100 : ℝ)), by norm_num [rowG], h7, win2_8 h6.le⟩
        · simp only [not_le] at h7
          exact ⟨((41/20 : ℝ), (2/5 : ℝ), (169/100 : ℝ)), by norm_num [rowG], hx5, win2_9 h7.le⟩

theorem t23cover : Work.ZeroFreeTables.RowCover := ⟨t23conj1, t23conj2⟩

end Work.ZeroFreeTables
