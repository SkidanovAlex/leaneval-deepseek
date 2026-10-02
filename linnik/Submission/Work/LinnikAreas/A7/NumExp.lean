import Mathlib
import Submission.Work.LinnikAreas.A7.ValueLemmas

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.A7

open Work.LinnikContract

lemma exF_a_1017_1000 : Real.exp (-(((49:ℝ)/10) * ((1017:ℝ)/(1000)))) ≤ ((342571:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 21) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_107_125 : Real.exp (-(((49:ℝ)/10) * ((107:ℝ)/(125)))) ≤ ((1507979:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_1093_1000 : Real.exp (-(((49:ℝ)/10) * ((1093:ℝ)/(1000)))) ≤ ((472117:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 21) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_11_10 : Real.exp (-(((49:ℝ)/10) * ((11:ℝ)/(10)))) ≤ ((228099:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 21) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_11_25 : Real.exp (-(((49:ℝ)/10) * ((11:ℝ)/(25)))) ≤ ((2315747:ℝ)/(20000000)) := by
  apply exp_neg_le_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_122_125 : Real.exp (-(((49:ℝ)/10) * ((122:ℝ)/(125)))) ≤ ((209397:ℝ)/(25000000)) := by
  apply exp_neg_le_rat (n := 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_1249_1000 : Real.exp (-(((49:ℝ)/10) * ((1249:ℝ)/(1000)))) ≤ ((13739:ℝ)/(6250000)) := by
  apply exp_neg_le_rat (n := 22) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_127_100 : Real.exp (-(((49:ℝ)/10) * ((127:ℝ)/(100)))) ≤ ((198329:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 22) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_12_25 : Real.exp (-(((49:ℝ)/10) * ((12:ℝ)/(25)))) ≤ ((4758931:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_139_200 : Real.exp (-(((49:ℝ)/10) * ((139:ℝ)/(200)))) ≤ ((3319023:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 18) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_13_25 : Real.exp (-(((49:ℝ)/10) * ((13:ℝ)/(25)))) ≤ ((7823799:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_141_100 : Real.exp (-(((49:ℝ)/10) * ((141:ℝ)/(100)))) ≤ ((24969:ℝ)/(25000000)) := by
  apply exp_neg_le_rat (n := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_143_125 : Real.exp (-(((49:ℝ)/10) * ((143:ℝ)/(125)))) ≤ ((183861:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 21) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_14_25 : Real.exp (-(((49:ℝ)/10) * ((14:ℝ)/(25)))) ≤ ((6431259:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_163_200 : Real.exp (-(((49:ℝ)/10) * ((163:ℝ)/(200)))) ≤ ((460877:ℝ)/(25000000)) := by
  apply exp_neg_le_rat (n := 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_171_200 : Real.exp (-(((49:ℝ)/10) * ((171:ℝ)/(200)))) ≤ ((757693:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 22) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_173_200 : Real.exp (-(((49:ℝ)/10) * ((173:ℝ)/(200)))) ≤ ((721461:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 21) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_187_250 : Real.exp (-(((49:ℝ)/10) * ((187:ℝ)/(250)))) ≤ ((1279953:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 18) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_19_20 : Real.exp (-(((49:ℝ)/10) * ((19:ℝ)/(20)))) ≤ ((29731:ℝ)/(3125000)) := by
  apply exp_neg_le_rat (n := 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_19_50 : Real.exp (-(((49:ℝ)/10) * ((19:ℝ)/(50)))) ≤ ((97101:ℝ)/(625000)) := by
  apply exp_neg_le_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_1_1 : Real.exp (-(((49:ℝ)/10) * ((1:ℝ)/(1)))) ≤ ((744659:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_1_2 : Real.exp (-(((49:ℝ)/10) * ((1:ℝ)/(2)))) ≤ ((8629359:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_1_4 : Real.exp (-(((49:ℝ)/10) * ((1:ℝ)/(4)))) ≤ ((29375771:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_1_5 : Real.exp (-(((49:ℝ)/10) * ((1:ℝ)/(5)))) ≤ ((3753111:ℝ)/(10000000)) := by
  apply exp_neg_le_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_207_250 : Real.exp (-(((49:ℝ)/10) * ((207:ℝ)/(250)))) ≤ ((1729739:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_211_250 : Real.exp (-(((49:ℝ)/10) * ((211:ℝ)/(250)))) ≤ ((1599307:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_21_20 : Real.exp (-(((49:ℝ)/10) * ((21:ℝ)/(20)))) ≤ ((9107:ℝ)/(1562500)) := by
  apply exp_neg_le_rat (n := 21) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_21_50 : Real.exp (-(((49:ℝ)/10) * ((21:ℝ)/(50)))) ≤ ((6385457:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_223_250 : Real.exp (-(((49:ℝ)/10) * ((223:ℝ)/(250)))) ≤ ((1264113:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_239_200 : Real.exp (-(((49:ℝ)/10) * ((239:ℝ)/(200)))) ≤ ((286411:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 22) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_23_20 : Real.exp (-(((49:ℝ)/10) * ((23:ℝ)/(20)))) ≤ ((89267:ℝ)/(25000000)) := by
  apply exp_neg_le_rat (n := 22) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_23_50 : Real.exp (-(((49:ℝ)/10) * ((23:ℝ)/(50)))) ≤ ((10497847:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_27_50 : Real.exp (-(((49:ℝ)/10) * ((27:ℝ)/(50)))) ≤ ((7093439:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_29_50 : Real.exp (-(((49:ℝ)/10) * ((29:ℝ)/(50)))) ≤ ((2915447:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_2_5 : Real.exp (-(((49:ℝ)/10) * ((2:ℝ)/(5)))) ≤ ((14085843:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_327_250 : Real.exp (-(((49:ℝ)/10) * ((327:ℝ)/(250)))) ≤ ((32927:ℝ)/(20000000)) := by
  apply exp_neg_le_rat (n := 22) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_379_500 : Real.exp (-(((49:ℝ)/10) * ((379:ℝ)/(500)))) ≤ ((1218747:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 18) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_37_40 : Real.exp (-(((49:ℝ)/10) * ((37:ℝ)/(40)))) ≤ ((67211:ℝ)/(6250000)) := by
  apply exp_neg_le_rat (n := 21) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_39_40 : Real.exp (-(((49:ℝ)/10) * ((39:ℝ)/(40)))) ≤ ((420851:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_3_10 : Real.exp (-(((49:ℝ)/10) * ((3:ℝ)/(10)))) ≤ ((22992549:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_3_5 : Real.exp (-(((49:ℝ)/10) * ((3:ℝ)/(5)))) ≤ ((5286573:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 18) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_401_500 : Real.exp (-(((49:ℝ)/10) * ((401:ℝ)/(500)))) ≤ ((1964761:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_41_40 : Real.exp (-(((49:ℝ)/10) * ((41:ℝ)/(40)))) ≤ ((164701:ℝ)/(25000000)) := by
  apply exp_neg_le_rat (n := 21) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_437_500 : Real.exp (-(((49:ℝ)/10) * ((437:ℝ)/(500)))) ≤ ((21573:ℝ)/(1562500)) := by
  apply exp_neg_le_rat (n := 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_43_40 : Real.exp (-(((49:ℝ)/10) * ((43:ℝ)/(40)))) ≤ ((515649:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 21) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_443_500 : Real.exp (-(((49:ℝ)/10) * ((443:ℝ)/(500)))) ≤ ((1301829:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 22) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_451_500 : Real.exp (-(((49:ℝ)/10) * ((451:ℝ)/(500)))) ≤ ((75229:ℝ)/(6250000)) := by
  apply exp_neg_le_rat (n := 21) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_453_500 : Real.exp (-(((49:ℝ)/10) * ((453:ℝ)/(500)))) ≤ ((590151:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_47_40 : Real.exp (-(((49:ℝ)/10) * ((47:ℝ)/(40)))) ≤ ((3159:ℝ)/(1000000)) := by
  apply exp_neg_le_rat (n := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_47_50 : Real.exp (-(((49:ℝ)/10) * ((47:ℝ)/(50)))) ≤ ((999171:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_49_40 : Real.exp (-(((49:ℝ)/10) * ((49:ℝ)/(40)))) ≤ ((247257:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 22) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_507_500 : Real.exp (-(((49:ℝ)/10) * ((507:ℝ)/(500)))) ≤ ((86911:ℝ)/(12500000)) := by
  apply exp_neg_le_rat (n := 21) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_51_40 : Real.exp (-(((49:ℝ)/10) * ((51:ℝ)/(40)))) ≤ ((193529:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 22) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_527_500 : Real.exp (-(((49:ℝ)/10) * ((527:ℝ)/(500)))) ≤ ((114307:ℝ)/(20000000)) := by
  apply exp_neg_le_rat (n := 22) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_549_500 : Real.exp (-(((49:ℝ)/10) * ((549:ℝ)/(500)))) ≤ ((460691:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 21) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_567_500 : Real.exp (-(((49:ℝ)/10) * ((567:ℝ)/(500)))) ≤ ((386189:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 21) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_59_50 : Real.exp (-(((49:ℝ)/10) * ((59:ℝ)/(50)))) ≤ ((61651:ℝ)/(20000000)) := by
  apply exp_neg_le_rat (n := 22) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_5_4 : Real.exp (-(((49:ℝ)/10) * ((5:ℝ)/(4)))) ≤ ((7:ℝ)/(3200)) := by
  apply exp_neg_le_rat (n := 22) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_6_5 : Real.exp (-(((49:ℝ)/10) * ((6:ℝ)/(5)))) ≤ ((279479:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 22) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_701_1000 : Real.exp (-(((49:ℝ)/10) * ((701:ℝ)/(1000)))) ≤ ((201429:ℝ)/(6250000)) := by
  apply exp_neg_le_rat (n := 18) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_779_1000 : Real.exp (-(((49:ℝ)/10) * ((779:ℝ)/(1000)))) ≤ ((2199149:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_79_100 : Real.exp (-(((49:ℝ)/10) * ((79:ℝ)/(100)))) ≤ ((2083753:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 18) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_79_50 : Real.exp (-(((49:ℝ)/10) * ((79:ℝ)/(50)))) ≤ ((43421:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_7_8 : Real.exp (-(((49:ℝ)/10) * ((7:ℝ)/(8)))) ≤ ((343481:ℝ)/(25000000)) := by
  apply exp_neg_le_rat (n := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_841_1000 : Real.exp (-(((49:ℝ)/10) * ((841:ℝ)/(1000)))) ≤ ((1622991:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_87_100 : Real.exp (-(((49:ℝ)/10) * ((87:ℝ)/(100)))) ≤ ((44:ℝ)/(3125)) := by
  apply exp_neg_le_rat (n := 21) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_87_250 : Real.exp (-(((49:ℝ)/10) * ((87:ℝ)/(250)))) ≤ ((4543401:ℝ)/(25000000)) := by
  apply exp_neg_le_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_921_1000 : Real.exp (-(((49:ℝ)/10) * ((921:ℝ)/(1000)))) ≤ ((548331:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_951_1000 : Real.exp (-(((49:ℝ)/10) * ((951:ℝ)/(1000)))) ≤ ((946741:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 21) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_96_125 : Real.exp (-(((49:ℝ)/10) * ((96:ℝ)/(125)))) ≤ ((290117:ℝ)/(12500000)) := by
  apply exp_neg_le_rat (n := 18) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_983_1000 : Real.exp (-(((49:ℝ)/10) * ((983:ℝ)/(1000)))) ≤ ((404673:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_9_10 : Real.exp (-(((49:ℝ)/10) * ((9:ℝ)/(10)))) ≤ ((607759:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_9_25 : Real.exp (-(((49:ℝ)/10) * ((9:ℝ)/(25)))) ≤ ((8567903:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_9_5 : Real.exp (-(((49:ℝ)/10) * ((9:ℝ)/(5)))) ≤ ((591:ℝ)/(4000000)) := by
  apply exp_neg_le_rat (n := 26) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_a_9_8 : Real.exp (-(((49:ℝ)/10) * ((9:ℝ)/(8)))) ≤ ((403601:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 21) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_1017_1000 : Real.exp (-(((3:ℝ)/5) * ((1017:ℝ)/(1000)))) ≤ ((54324221:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_107_125 : Real.exp (-(((3:ℝ)/5) * ((107:ℝ)/(125)))) ≤ ((59833769:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_1093_1000 : Real.exp (-(((3:ℝ)/5) * ((1093:ℝ)/(1000)))) ≤ ((12975667:ℝ)/(25000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_11_10 : Real.exp (-(((3:ℝ)/5) * ((11:ℝ)/(10)))) ≤ ((25842567:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_11_25 : Real.exp (-(((3:ℝ)/5) * ((11:ℝ)/(25)))) ≤ ((38398677:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_122_125 : Real.exp (-(((3:ℝ)/5) * ((122:ℝ)/(125)))) ≤ ((5567717:ℝ)/(10000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_1249_1000 : Real.exp (-(((3:ℝ)/5) * ((1249:ℝ)/(1000)))) ≤ ((23632503:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_127_100 : Real.exp (-(((3:ℝ)/5) * ((127:ℝ)/(100)))) ≤ ((46673203:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_12_25 : Real.exp (-(((3:ℝ)/5) * ((12:ℝ)/(25)))) ≤ ((468601:ℝ)/(625000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_139_200 : Real.exp (-(((3:ℝ)/5) * ((139:ℝ)/(200)))) ≤ ((16475523:ℝ)/(25000000)) := by
  apply exp_neg_le_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_13_25 : Real.exp (-(((3:ℝ)/5) * ((13:ℝ)/(25)))) ≤ ((73198153:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_141_100 : Real.exp (-(((3:ℝ)/5) * ((141:ℝ)/(100)))) ≤ ((21456401:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_143_125 : Real.exp (-(((3:ℝ)/5) * ((143:ℝ)/(125)))) ≤ ((100677:ℝ)/(200000)) := by
  apply exp_neg_le_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_14_25 : Real.exp (-(((3:ℝ)/5) * ((14:ℝ)/(25)))) ≤ ((71462311:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_163_200 : Real.exp (-(((3:ℝ)/5) * ((163:ℝ)/(200)))) ≤ ((61323933:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_171_200 : Real.exp (-(((3:ℝ)/5) * ((171:ℝ)/(200)))) ≤ ((748371:ℝ)/(1250000)) := by
  apply exp_neg_le_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_173_200 : Real.exp (-(((3:ℝ)/5) * ((173:ℝ)/(200)))) ≤ ((59511537:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_187_250 : Real.exp (-(((3:ℝ)/5) * ((187:ℝ)/(250)))) ≤ ((63839377:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_19_20 : Real.exp (-(((3:ℝ)/5) * ((19:ℝ)/(20)))) ≤ ((1767267:ℝ)/(3125000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_19_50 : Real.exp (-(((3:ℝ)/5) * ((19:ℝ)/(50)))) ≤ ((39806213:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_1_1 : Real.exp (-(((3:ℝ)/5) * ((1:ℝ)/(1)))) ≤ ((13720291:ℝ)/(25000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_1_2 : Real.exp (-(((3:ℝ)/5) * ((1:ℝ)/(2)))) ≤ ((74081823:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_1_4 : Real.exp (-(((3:ℝ)/5) * ((1:ℝ)/(4)))) ≤ ((43035399:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_1_5 : Real.exp (-(((3:ℝ)/5) * ((1:ℝ)/(5)))) ≤ ((22173011:ℝ)/(25000000)) := by
  apply exp_neg_le_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_207_250 : Real.exp (-(((3:ℝ)/5) * ((207:ℝ)/(250)))) ≤ ((60847467:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_211_250 : Real.exp (-(((3:ℝ)/5) * ((211:ℝ)/(250)))) ≤ ((30133063:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_21_20 : Real.exp (-(((3:ℝ)/5) * ((21:ℝ)/(20)))) ≤ ((53259181:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_21_50 : Real.exp (-(((3:ℝ)/5) * ((21:ℝ)/(50)))) ≤ ((38862237:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_223_250 : Real.exp (-(((3:ℝ)/5) * ((223:ℝ)/(250)))) ≤ ((58555217:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_239_200 : Real.exp (-(((3:ℝ)/5) * ((239:ℝ)/(200)))) ≤ ((48821471:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_23_20 : Real.exp (-(((3:ℝ)/5) * ((23:ℝ)/(20)))) ≤ ((50157607:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_23_50 : Real.exp (-(((3:ℝ)/5) * ((23:ℝ)/(50)))) ≤ ((37940647:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_27_50 : Real.exp (-(((3:ℝ)/5) * ((27:ℝ)/(50)))) ≤ ((2893001:ℝ)/(4000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_29_50 : Real.exp (-(((3:ℝ)/5) * ((29:ℝ)/(50)))) ≤ ((2206559:ℝ)/(3125000)) := by
  apply exp_neg_le_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_2_5 : Real.exp (-(((3:ℝ)/5) * ((2:ℝ)/(5)))) ≤ ((78662787:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_327_250 : Real.exp (-(((3:ℝ)/5) * ((327:ℝ)/(250)))) ≤ ((22810547:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_379_500 : Real.exp (-(((3:ℝ)/5) * ((379:ℝ)/(500)))) ≤ ((3966093:ℝ)/(6250000)) := by
  apply exp_neg_le_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_37_40 : Real.exp (-(((3:ℝ)/5) * ((37:ℝ)/(40)))) ≤ ((57407227:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_39_40 : Real.exp (-(((3:ℝ)/5) * ((39:ℝ)/(40)))) ≤ ((55710587:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_3_10 : Real.exp (-(((3:ℝ)/5) * ((3:ℝ)/(10)))) ≤ ((41763511:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_3_5 : Real.exp (-(((3:ℝ)/5) * ((3:ℝ)/(5)))) ≤ ((69767633:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_401_500 : Real.exp (-(((3:ℝ)/5) * ((401:ℝ)/(500)))) ≤ ((6180413:ℝ)/(10000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_41_40 : Real.exp (-(((3:ℝ)/5) * ((41:ℝ)/(40)))) ≤ ((5406409:ℝ)/(10000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_437_500 : Real.exp (-(((3:ℝ)/5) * ((437:ℝ)/(500)))) ≤ ((59191041:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_43_40 : Real.exp (-(((3:ℝ)/5) * ((43:ℝ)/(40)))) ≤ ((10493251:ℝ)/(20000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_443_500 : Real.exp (-(((3:ℝ)/5) * ((443:ℝ)/(500)))) ≤ ((14691599:ℝ)/(25000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_451_500 : Real.exp (-(((3:ℝ)/5) * ((451:ℝ)/(500)))) ≤ ((29102469:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_453_500 : Real.exp (-(((3:ℝ)/5) * ((453:ℝ)/(500)))) ≤ ((29032707:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_47_40 : Real.exp (-(((3:ℝ)/5) * ((47:ℝ)/(40)))) ≤ ((24705429:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_47_50 : Real.exp (-(((3:ℝ)/5) * ((47:ℝ)/(50)))) ≤ ((711161:ℝ)/(1250000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_49_40 : Real.exp (-(((3:ℝ)/5) * ((49:ℝ)/(40)))) ≤ ((23975273:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_507_500 : Real.exp (-(((3:ℝ)/5) * ((507:ℝ)/(500)))) ≤ ((54422093:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_51_40 : Real.exp (-(((3:ℝ)/5) * ((51:ℝ)/(40)))) ≤ ((23266697:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_527_500 : Real.exp (-(((3:ℝ)/5) * ((527:ℝ)/(500)))) ≤ ((6641439:ℝ)/(12500000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_549_500 : Real.exp (-(((3:ℝ)/5) * ((549:ℝ)/(500)))) ≤ ((51747193:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_567_500 : Real.exp (-(((3:ℝ)/5) * ((567:ℝ)/(500)))) ≤ ((50641439:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_59_50 : Real.exp (-(((3:ℝ)/5) * ((59:ℝ)/(50)))) ≤ ((49262847:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_5_4 : Real.exp (-(((3:ℝ)/5) * ((5:ℝ)/(4)))) ≤ ((2952291:ℝ)/(6250000)) := by
  apply exp_neg_le_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_6_5 : Real.exp (-(((3:ℝ)/5) * ((6:ℝ)/(5)))) ≤ ((24337613:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_701_1000 : Real.exp (-(((3:ℝ)/5) * ((701:ℝ)/(1000)))) ≤ ((65665271:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_779_1000 : Real.exp (-(((3:ℝ)/5) * ((779:ℝ)/(1000)))) ≤ ((62662939:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_79_100 : Real.exp (-(((3:ℝ)/5) * ((79:ℝ)/(100)))) ≤ ((31125363:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_79_50 : Real.exp (-(((3:ℝ)/5) * ((79:ℝ)/(50)))) ≤ ((4843941:ℝ)/(12500000)) := by
  apply exp_neg_le_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_7_8 : Real.exp (-(((3:ℝ)/5) * ((7:ℝ)/(8)))) ≤ ((59155537:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_841_1000 : Real.exp (-(((3:ℝ)/5) * ((841:ℝ)/(1000)))) ≤ ((60374703:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_87_100 : Real.exp (-(((3:ℝ)/5) * ((87:ℝ)/(100)))) ≤ ((5933327:ℝ)/(10000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_87_250 : Real.exp (-(((3:ℝ)/5) * ((87:ℝ)/(250)))) ≤ ((40577877:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_921_1000 : Real.exp (-(((3:ℝ)/5) * ((921:ℝ)/(1000)))) ≤ ((57545169:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_951_1000 : Real.exp (-(((3:ℝ)/5) * ((951:ℝ)/(1000)))) ≤ ((56518623:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_96_125 : Real.exp (-(((3:ℝ)/5) * ((96:ℝ)/(125)))) ≤ ((63077883:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_983_1000 : Real.exp (-(((3:ℝ)/5) * ((983:ℝ)/(1000)))) ≤ ((55443817:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_9_10 : Real.exp (-(((3:ℝ)/5) * ((9:ℝ)/(10)))) ≤ ((29137413:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_9_25 : Real.exp (-(((3:ℝ)/5) * ((9:ℝ)/(25)))) ≤ ((80573531:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_9_5 : Real.exp (-(((3:ℝ)/5) * ((9:ℝ)/(5)))) ≤ ((33959553:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_b_9_8 : Real.exp (-(((3:ℝ)/5) * ((9:ℝ)/(8)))) ≤ ((50915643:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_1017_1000 : Real.exp (-(((3:ℝ)/10) * ((1017:ℝ)/(1000)))) ≤ ((73704967:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_107_125 : Real.exp (-(((3:ℝ)/10) * ((107:ℝ)/(125)))) ≤ ((77352291:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_1093_1000 : Real.exp (-(((3:ℝ)/10) * ((1093:ℝ)/(1000)))) ≤ ((36021753:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_11_10 : Real.exp (-(((3:ℝ)/10) * ((11:ℝ)/(10)))) ≤ ((35946187:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_11_25 : Real.exp (-(((3:ℝ)/10) * ((11:ℝ)/(25)))) ≤ ((876341:ℝ)/(1000000)) := by
  apply exp_neg_le_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_122_125 : Real.exp (-(((3:ℝ)/10) * ((122:ℝ)/(125)))) ≤ ((74617137:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_1249_1000 : Real.exp (-(((3:ℝ)/10) * ((1249:ℝ)/(1000)))) ≤ ((1374991:ℝ)/(2000000)) := by
  apply exp_neg_le_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_127_100 : Real.exp (-(((3:ℝ)/10) * ((127:ℝ)/(100)))) ≤ ((68317789:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_12_25 : Real.exp (-(((3:ℝ)/10) * ((12:ℝ)/(25)))) ≤ ((3463551:ℝ)/(4000000)) := by
  apply exp_neg_le_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_139_200 : Real.exp (-(((3:ℝ)/10) * ((139:ℝ)/(200)))) ≤ ((10147513:ℝ)/(12500000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_13_25 : Real.exp (-(((3:ℝ)/10) * ((13:ℝ)/(25)))) ≤ ((1069449:ℝ)/(1250000)) := by
  apply exp_neg_le_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_141_100 : Real.exp (-(((3:ℝ)/10) * ((141:ℝ)/(100)))) ≤ ((8188483:ℝ)/(12500000)) := by
  apply exp_neg_le_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_143_125 : Real.exp (-(((3:ℝ)/10) * ((143:ℝ)/(125)))) ≤ ((7094963:ℝ)/(10000000)) := by
  apply exp_neg_le_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_14_25 : Real.exp (-(((3:ℝ)/10) * ((14:ℝ)/(25)))) ≤ ((10566923:ℝ)/(12500000)) := by
  apply exp_neg_le_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_163_200 : Real.exp (-(((3:ℝ)/10) * ((163:ℝ)/(200)))) ≤ ((78309599:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_171_200 : Real.exp (-(((3:ℝ)/10) * ((171:ℝ)/(200)))) ≤ ((154751:ℝ)/(200000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_173_200 : Real.exp (-(((3:ℝ)/10) * ((173:ℝ)/(200)))) ≤ ((77143721:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_187_250 : Real.exp (-(((3:ℝ)/10) * ((187:ℝ)/(250)))) ≤ ((19974887:ℝ)/(25000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_19_20 : Real.exp (-(((3:ℝ)/10) * ((19:ℝ)/(20)))) ≤ ((37600713:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_19_50 : Real.exp (-(((3:ℝ)/10) * ((19:ℝ)/(50)))) ≤ ((22306449:ℝ)/(25000000)) := by
  apply exp_neg_le_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_1_1 : Real.exp (-(((3:ℝ)/10) * ((1:ℝ)/(1)))) ≤ ((74081823:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_1_2 : Real.exp (-(((3:ℝ)/10) * ((1:ℝ)/(2)))) ≤ ((43035399:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_1_4 : Real.exp (-(((3:ℝ)/10) * ((1:ℝ)/(4)))) ≤ ((92774349:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_1_5 : Real.exp (-(((3:ℝ)/10) * ((1:ℝ)/(5)))) ≤ ((47088227:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_207_250 : Real.exp (-(((3:ℝ)/10) * ((207:ℝ)/(250)))) ≤ ((78004787:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_211_250 : Real.exp (-(((3:ℝ)/10) * ((211:ℝ)/(250)))) ≤ ((77631261:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_21_20 : Real.exp (-(((3:ℝ)/10) * ((21:ℝ)/(20)))) ≤ ((9122361:ℝ)/(12500000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_21_50 : Real.exp (-(((3:ℝ)/10) * ((21:ℝ)/(50)))) ≤ ((17632297:ℝ)/(20000000)) := by
  apply exp_neg_le_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_223_250 : Real.exp (-(((3:ℝ)/10) * ((223:ℝ)/(250)))) ≤ ((76521381:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_239_200 : Real.exp (-(((3:ℝ)/10) * ((239:ℝ)/(200)))) ≤ ((69872363:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_23_20 : Real.exp (-(((3:ℝ)/10) * ((23:ℝ)/(20)))) ≤ ((17705509:ℝ)/(25000000)) := by
  apply exp_neg_le_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_23_50 : Real.exp (-(((3:ℝ)/10) * ((23:ℝ)/(50)))) ≤ ((8710987:ℝ)/(10000000)) := by
  apply exp_neg_le_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_27_50 : Real.exp (-(((3:ℝ)/10) * ((27:ℝ)/(50)))) ≤ ((85044121:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_29_50 : Real.exp (-(((3:ℝ)/10) * ((29:ℝ)/(50)))) ≤ ((8402969:ℝ)/(10000000)) := by
  apply exp_neg_le_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_2_5 : Real.exp (-(((3:ℝ)/10) * ((2:ℝ)/(5)))) ≤ ((22173011:ℝ)/(25000000)) := by
  apply exp_neg_le_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_327_250 : Real.exp (-(((3:ℝ)/10) * ((327:ℝ)/(250)))) ≤ ((67543389:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_379_500 : Real.exp (-(((3:ℝ)/10) * ((379:ℝ)/(500)))) ≤ ((4978763:ℝ)/(6250000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_37_40 : Real.exp (-(((3:ℝ)/10) * ((37:ℝ)/(40)))) ≤ ((75767557:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_39_40 : Real.exp (-(((3:ℝ)/10) * ((39:ℝ)/(40)))) ≤ ((2985581:ℝ)/(4000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_3_10 : Real.exp (-(((3:ℝ)/10) * ((3:ℝ)/(10)))) ≤ ((91393119:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_3_5 : Real.exp (-(((3:ℝ)/10) * ((3:ℝ)/(5)))) ≤ ((41763511:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_401_500 : Real.exp (-(((3:ℝ)/10) * ((401:ℝ)/(500)))) ≤ ((78615603:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_41_40 : Real.exp (-(((3:ℝ)/10) * ((41:ℝ)/(40)))) ≤ ((73528287:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_437_500 : Real.exp (-(((3:ℝ)/10) * ((437:ℝ)/(500)))) ≤ ((38467857:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_43_40 : Real.exp (-(((3:ℝ)/10) * ((43:ℝ)/(40)))) ≤ ((36216797:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_443_500 : Real.exp (-(((3:ℝ)/10) * ((443:ℝ)/(500)))) ≤ ((19164811:ℝ)/(25000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_451_500 : Real.exp (-(((3:ℝ)/10) * ((451:ℝ)/(500)))) ≤ ((76292161:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_453_500 : Real.exp (-(((3:ℝ)/10) * ((453:ℝ)/(500)))) ≤ ((15240133:ℝ)/(20000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_47_40 : Real.exp (-(((3:ℝ)/10) * ((47:ℝ)/(40)))) ≤ ((70292857:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_47_50 : Real.exp (-(((3:ℝ)/10) * ((47:ℝ)/(50)))) ≤ ((75427369:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_49_40 : Real.exp (-(((3:ℝ)/10) * ((49:ℝ)/(40)))) ≤ ((69246333:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_507_500 : Real.exp (-(((3:ℝ)/10) * ((507:ℝ)/(500)))) ≤ ((73771331:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_51_40 : Real.exp (-(((3:ℝ)/10) * ((51:ℝ)/(40)))) ≤ ((6821539:ℝ)/(10000000)) := by
  apply exp_neg_le_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_527_500 : Real.exp (-(((3:ℝ)/10) * ((527:ℝ)/(500)))) ≤ ((36445683:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_549_500 : Real.exp (-(((3:ℝ)/10) * ((549:ℝ)/(500)))) ≤ ((35967761:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_567_500 : Real.exp (-(((3:ℝ)/10) * ((567:ℝ)/(500)))) ≤ ((71162799:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_59_50 : Real.exp (-(((3:ℝ)/10) * ((59:ℝ)/(50)))) ≤ ((70187497:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_5_4 : Real.exp (-(((3:ℝ)/10) * ((5:ℝ)/(4)))) ≤ ((2147779:ℝ)/(3125000)) := by
  apply exp_neg_le_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_6_5 : Real.exp (-(((3:ℝ)/10) * ((6:ℝ)/(5)))) ≤ ((69767633:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_701_1000 : Real.exp (-(((3:ℝ)/10) * ((701:ℝ)/(1000)))) ≤ ((81034111:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_779_1000 : Real.exp (-(((3:ℝ)/10) * ((779:ℝ)/(1000)))) ≤ ((79159927:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_79_100 : Real.exp (-(((3:ℝ)/10) * ((79:ℝ)/(100)))) ≤ ((78899129:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_79_50 : Real.exp (-(((3:ℝ)/10) * ((79:ℝ)/(50)))) ≤ ((31125363:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_7_8 : Real.exp (-(((3:ℝ)/10) * ((7:ℝ)/(8)))) ≤ ((76912637:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_841_1000 : Real.exp (-(((3:ℝ)/10) * ((841:ℝ)/(1000)))) ≤ ((1942529:ℝ)/(2500000)) := by
  apply exp_neg_le_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_87_100 : Real.exp (-(((3:ℝ)/10) * ((87:ℝ)/(100)))) ≤ ((19257023:ℝ)/(25000000)) := by
  apply exp_neg_le_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_87_250 : Real.exp (-(((3:ℝ)/10) * ((87:ℝ)/(250)))) ≤ ((11260811:ℝ)/(12500000)) := by
  apply exp_neg_le_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_921_1000 : Real.exp (-(((3:ℝ)/10) * ((921:ℝ)/(1000)))) ≤ ((75858533:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_951_1000 : Real.exp (-(((3:ℝ)/10) * ((951:ℝ)/(1000)))) ≤ ((75178869:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_96_125 : Real.exp (-(((3:ℝ)/10) * ((96:ℝ)/(125)))) ≤ ((39710793:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_983_1000 : Real.exp (-(((3:ℝ)/10) * ((983:ℝ)/(1000)))) ≤ ((14892121:ℝ)/(20000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_9_10 : Real.exp (-(((3:ℝ)/10) * ((9:ℝ)/(10)))) ≤ ((1526759:ℝ)/(2000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_9_25 : Real.exp (-(((3:ℝ)/10) * ((9:ℝ)/(25)))) ≤ ((2244069:ℝ)/(2500000)) := by
  apply exp_neg_le_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_9_5 : Real.exp (-(((3:ℝ)/10) * ((9:ℝ)/(5)))) ≤ ((29137413:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_c_9_8 : Real.exp (-(((3:ℝ)/10) * ((9:ℝ)/(8)))) ≤ ((35677599:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_1017_1000 : Real.exp (-(((73:ℝ)/30) * ((1017:ℝ)/(1000)))) ≤ ((336753:ℝ)/(4000000)) := by
  apply exp_neg_le_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_107_125 : Real.exp (-(((73:ℝ)/30) * ((107:ℝ)/(125)))) ≤ ((12456429:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_1093_1000 : Real.exp (-(((73:ℝ)/30) * ((1093:ℝ)/(1000)))) ≤ ((1749347:ℝ)/(25000000)) := by
  apply exp_neg_le_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_11_10 : Real.exp (-(((73:ℝ)/30) * ((11:ℝ)/(10)))) ≤ ((859901:ℝ)/(12500000)) := by
  apply exp_neg_le_rat (n := 18) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_11_25 : Real.exp (-(((73:ℝ)/30) * ((11:ℝ)/(25)))) ≤ ((34277993:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_122_125 : Real.exp (-(((73:ℝ)/30) * ((122:ℝ)/(125)))) ≤ ((930207:ℝ)/(10000000)) := by
  apply exp_neg_le_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_1249_1000 : Real.exp (-(((73:ℝ)/30) * ((1249:ℝ)/(1000)))) ≤ ((2393579:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 18) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_127_100 : Real.exp (-(((73:ℝ)/30) * ((127:ℝ)/(100)))) ≤ ((4548679:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_12_25 : Real.exp (-(((73:ℝ)/30) * ((12:ℝ)/(25)))) ≤ ((3109883:ℝ)/(10000000)) := by
  apply exp_neg_le_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_139_200 : Real.exp (-(((73:ℝ)/30) * ((139:ℝ)/(200)))) ≤ ((9215219:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_13_25 : Real.exp (-(((73:ℝ)/30) * ((13:ℝ)/(25)))) ≤ ((7053631:ℝ)/(25000000)) := by
  apply exp_neg_le_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_141_100 : Real.exp (-(((73:ℝ)/30) * ((141:ℝ)/(100)))) ≤ ((1617729:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 18) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_143_125 : Real.exp (-(((73:ℝ)/30) * ((143:ℝ)/(125)))) ≤ ((6180733:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_14_25 : Real.exp (-(((73:ℝ)/30) * ((14:ℝ)/(25)))) ≤ ((12798863:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_163_200 : Real.exp (-(((73:ℝ)/30) * ((163:ℝ)/(200)))) ≤ ((13763271:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_171_200 : Real.exp (-(((73:ℝ)/30) * ((171:ℝ)/(200)))) ≤ ((12486777:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_173_200 : Real.exp (-(((73:ℝ)/30) * ((173:ℝ)/(200)))) ≤ ((12186599:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_187_250 : Real.exp (-(((73:ℝ)/30) * ((187:ℝ)/(250)))) ≤ ((3240083:ℝ)/(20000000)) := by
  apply exp_neg_le_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_19_20 : Real.exp (-(((73:ℝ)/30) * ((19:ℝ)/(20)))) ≤ ((2477399:ℝ)/(25000000)) := by
  apply exp_neg_le_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_19_50 : Real.exp (-(((73:ℝ)/30) * ((19:ℝ)/(50)))) ≤ ((19833181:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_1_1 : Real.exp (-(((73:ℝ)/30) * ((1:ℝ)/(1)))) ≤ ((8774387:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_1_2 : Real.exp (-(((73:ℝ)/30) * ((1:ℝ)/(2)))) ≤ ((29621591:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_1_4 : Real.exp (-(((73:ℝ)/30) * ((1:ℝ)/(4)))) ≤ ((54425721:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_1_5 : Real.exp (-(((73:ℝ)/30) * ((1:ℝ)/(5)))) ≤ ((61467189:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_207_250 : Real.exp (-(((73:ℝ)/30) * ((207:ℝ)/(250)))) ≤ ((3333677:ℝ)/(25000000)) := by
  apply exp_neg_le_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_211_250 : Real.exp (-(((73:ℝ)/30) * ((211:ℝ)/(250)))) ≤ ((12825519:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_21_20 : Real.exp (-(((73:ℝ)/30) * ((21:ℝ)/(20)))) ≤ ((971153:ℝ)/(12500000)) := by
  apply exp_neg_le_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_21_50 : Real.exp (-(((73:ℝ)/30) * ((21:ℝ)/(50)))) ≤ ((4498431:ℝ)/(12500000)) := by
  apply exp_neg_le_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_223_250 : Real.exp (-(((73:ℝ)/30) * ((223:ℝ)/(250)))) ≤ ((5705837:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_239_200 : Real.exp (-(((73:ℝ)/30) * ((239:ℝ)/(200)))) ≤ ((5459389:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 18) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_23_20 : Real.exp (-(((73:ℝ)/30) * ((23:ℝ)/(20)))) ≤ ((121823:ℝ)/(2000000)) := by
  apply exp_neg_le_rat (n := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_23_50 : Real.exp (-(((73:ℝ)/30) * ((23:ℝ)/(50)))) ≤ ((32649739:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_27_50 : Real.exp (-(((73:ℝ)/30) * ((27:ℝ)/(50)))) ≤ ((13437147:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_29_50 : Real.exp (-(((73:ℝ)/30) * ((29:ℝ)/(50)))) ≤ ((12190899:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_2_5 : Real.exp (-(((73:ℝ)/30) * ((2:ℝ)/(5)))) ≤ ((18891077:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_327_250 : Real.exp (-(((73:ℝ)/30) * ((327:ℝ)/(250)))) ≤ ((2073469:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 18) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_379_500 : Real.exp (-(((73:ℝ)/30) * ((379:ℝ)/(500)))) ≤ ((15810963:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_37_40 : Real.exp (-(((73:ℝ)/30) * ((37:ℝ)/(40)))) ≤ ((10531143:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_39_40 : Real.exp (-(((73:ℝ)/30) * ((39:ℝ)/(40)))) ≤ ((2331183:ℝ)/(25000000)) := by
  apply exp_neg_le_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_3_10 : Real.exp (-(((73:ℝ)/30) * ((3:ℝ)/(10)))) ≤ ((481909:ℝ)/(1000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_3_5 : Real.exp (-(((73:ℝ)/30) * ((3:ℝ)/(5)))) ≤ ((5805907:ℝ)/(25000000)) := by
  apply exp_neg_le_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_401_500 : Real.exp (-(((73:ℝ)/30) * ((401:ℝ)/(500)))) ≤ ((14205609:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_41_40 : Real.exp (-(((73:ℝ)/30) * ((41:ℝ)/(40)))) ≤ ((8256523:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_437_500 : Real.exp (-(((73:ℝ)/30) * ((437:ℝ)/(500)))) ≤ ((5961307:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_43_40 : Real.exp (-(((73:ℝ)/30) * ((43:ℝ)/(40)))) ≤ ((1462137:ℝ)/(20000000)) := by
  apply exp_neg_le_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_443_500 : Real.exp (-(((73:ℝ)/30) * ((443:ℝ)/(500)))) ≤ ((11579507:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_451_500 : Real.exp (-(((73:ℝ)/30) * ((451:ℝ)/(500)))) ≤ ((5568671:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_453_500 : Real.exp (-(((73:ℝ)/30) * ((453:ℝ)/(500)))) ≤ ((1378683:ℝ)/(12500000)) := by
  apply exp_neg_le_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_47_40 : Real.exp (-(((73:ℝ)/30) * ((47:ℝ)/(40)))) ≤ ((5731651:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_47_50 : Real.exp (-(((73:ℝ)/30) * ((47:ℝ)/(50)))) ≤ ((10153687:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_49_40 : Real.exp (-(((73:ℝ)/30) * ((49:ℝ)/(40)))) ≤ ((5075053:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_507_500 : Real.exp (-(((73:ℝ)/30) * ((507:ℝ)/(500)))) ≤ ((8480507:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_51_40 : Real.exp (-(((73:ℝ)/30) * ((51:ℝ)/(40)))) ≤ ((4493673:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_527_500 : Real.exp (-(((73:ℝ)/30) * ((527:ℝ)/(500)))) ≤ ((769397:ℝ)/(10000000)) := by
  apply exp_neg_le_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_549_500 : Real.exp (-(((73:ℝ)/30) * ((549:ℝ)/(500)))) ≤ ((6912769:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_567_500 : Real.exp (-(((73:ℝ)/30) * ((567:ℝ)/(500)))) ≤ ((395811:ℝ)/(6250000)) := by
  apply exp_neg_le_rat (n := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_59_50 : Real.exp (-(((73:ℝ)/30) * ((59:ℝ)/(50)))) ≤ ((2831169:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 18) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_5_4 : Real.exp (-(((73:ℝ)/30) * ((5:ℝ)/(4)))) ≤ ((1193881:ℝ)/(25000000)) := by
  apply exp_neg_le_rat (n := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_6_5 : Real.exp (-(((73:ℝ)/30) * ((6:ℝ)/(5)))) ≤ ((5393369:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_701_1000 : Real.exp (-(((73:ℝ)/30) * ((701:ℝ)/(1000)))) ≤ ((18163309:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_779_1000 : Real.exp (-(((73:ℝ)/30) * ((779:ℝ)/(1000)))) ≤ ((7511659:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_79_100 : Real.exp (-(((73:ℝ)/30) * ((79:ℝ)/(100)))) ≤ ((457079:ℝ)/(3125000)) := by
  apply exp_neg_le_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_79_50 : Real.exp (-(((73:ℝ)/30) * ((79:ℝ)/(50)))) ≤ ((1069677:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 18) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_7_8 : Real.exp (-(((73:ℝ)/30) * ((7:ℝ)/(8)))) ≤ ((11893637:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_841_1000 : Real.exp (-(((73:ℝ)/30) * ((841:ℝ)/(1000)))) ≤ ((201867:ℝ)/(1562500)) := by
  apply exp_neg_le_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_87_100 : Real.exp (-(((73:ℝ)/30) * ((87:ℝ)/(100)))) ≤ ((12039227:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_87_250 : Real.exp (-(((73:ℝ)/30) * ((87:ℝ)/(250)))) ≤ ((21439243:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_921_1000 : Real.exp (-(((73:ℝ)/30) * ((921:ℝ)/(1000)))) ≤ ((10634147:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_951_1000 : Real.exp (-(((73:ℝ)/30) * ((951:ℝ)/(1000)))) ≤ ((1235689:ℝ)/(12500000)) := by
  apply exp_neg_le_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_96_125 : Real.exp (-(((73:ℝ)/30) * ((96:ℝ)/(125)))) ≤ ((15430873:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_983_1000 : Real.exp (-(((73:ℝ)/30) * ((983:ℝ)/(1000)))) ≤ ((4572483:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_9_10 : Real.exp (-(((73:ℝ)/30) * ((9:ℝ)/(10)))) ≤ ((447667:ℝ)/(4000000)) := by
  apply exp_neg_le_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_9_25 : Real.exp (-(((73:ℝ)/30) * ((9:ℝ)/(25)))) ≤ ((41644537:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_9_5 : Real.exp (-(((73:ℝ)/30) * ((9:ℝ)/(5)))) ≤ ((156567:ℝ)/(12500000)) := by
  apply exp_neg_le_rat (n := 21) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_d_9_8 : Real.exp (-(((73:ℝ)/30) * ((9:ℝ)/(8)))) ≤ ((3236599:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_1017_1000 : Real.exp (-(((41:ℝ)/30) * ((1017:ℝ)/(1000)))) ≤ ((12455011:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_107_125 : Real.exp (-(((41:ℝ)/30) * ((107:ℝ)/(125)))) ≤ ((31040833:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_1093_1000 : Real.exp (-(((41:ℝ)/30) * ((1093:ℝ)/(1000)))) ≤ ((4490507:ℝ)/(20000000)) := by
  apply exp_neg_le_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_11_10 : Real.exp (-(((41:ℝ)/30) * ((11:ℝ)/(10)))) ≤ ((5559691:ℝ)/(25000000)) := by
  apply exp_neg_le_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_11_25 : Real.exp (-(((41:ℝ)/30) * ((11:ℝ)/(25)))) ≤ ((27404019:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_122_125 : Real.exp (-(((41:ℝ)/30) * ((122:ℝ)/(125)))) ≤ ((1317283:ℝ)/(5000000)) := by
  apply exp_neg_le_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_1249_1000 : Real.exp (-(((41:ℝ)/30) * ((1249:ℝ)/(1000)))) ≤ ((9070763:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_127_100 : Real.exp (-(((41:ℝ)/30) * ((127:ℝ)/(100)))) ≤ ((2203533:ℝ)/(12500000)) := by
  apply exp_neg_le_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_12_25 : Real.exp (-(((41:ℝ)/30) * ((12:ℝ)/(25)))) ≤ ((51892289:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_139_200 : Real.exp (-(((41:ℝ)/30) * ((139:ℝ)/(200)))) ≤ ((38680549:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_13_25 : Real.exp (-(((41:ℝ)/30) * ((13:ℝ)/(25)))) ≤ ((9826331:ℝ)/(20000000)) := by
  apply exp_neg_le_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_141_100 : Real.exp (-(((41:ℝ)/30) * ((141:ℝ)/(100)))) ≤ ((1455843:ℝ)/(10000000)) := by
  apply exp_neg_le_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_143_125 : Real.exp (-(((41:ℝ)/30) * ((143:ℝ)/(125)))) ≤ ((20940887:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_14_25 : Real.exp (-(((41:ℝ)/30) * ((14:ℝ)/(25)))) ≤ ((9303577:ℝ)/(20000000)) := by
  apply exp_neg_le_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_163_200 : Real.exp (-(((41:ℝ)/30) * ((163:ℝ)/(200)))) ≤ ((32829807:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_171_200 : Real.exp (-(((41:ℝ)/30) * ((171:ℝ)/(200)))) ≤ ((6216657:ℝ)/(20000000)) := by
  apply exp_neg_le_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_173_200 : Real.exp (-(((41:ℝ)/30) * ((173:ℝ)/(200)))) ≤ ((30661369:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_187_250 : Real.exp (-(((41:ℝ)/30) * ((187:ℝ)/(250)))) ≤ ((8994463:ℝ)/(25000000)) := by
  apply exp_neg_le_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_19_20 : Real.exp (-(((41:ℝ)/30) * ((19:ℝ)/(20)))) ≤ ((341233:ℝ)/(1250000)) := by
  apply exp_neg_le_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_19_50 : Real.exp (-(((41:ℝ)/30) * ((19:ℝ)/(50)))) ≤ ((59491703:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_1_1 : Real.exp (-(((41:ℝ)/30) * ((1:ℝ)/(1)))) ≤ ((1274777:ℝ)/(5000000)) := by
  apply exp_neg_le_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_1_2 : Real.exp (-(((41:ℝ)/30) * ((1:ℝ)/(2)))) ≤ ((50493109:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_1_4 : Real.exp (-(((41:ℝ)/30) * ((1:ℝ)/(4)))) ≤ ((71058503:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_1_5 : Real.exp (-(((41:ℝ)/30) * ((1:ℝ)/(5)))) ≤ ((38041957:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_207_250 : Real.exp (-(((41:ℝ)/30) * ((207:ℝ)/(250)))) ≤ ((16125841:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_211_250 : Real.exp (-(((41:ℝ)/30) * ((211:ℝ)/(250)))) ≤ ((315541:ℝ)/(1000000)) := by
  apply exp_neg_le_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_21_20 : Real.exp (-(((41:ℝ)/30) * ((21:ℝ)/(20)))) ≤ ((23811537:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_21_50 : Real.exp (-(((41:ℝ)/30) * ((21:ℝ)/(50)))) ≤ ((28163393:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_223_250 : Real.exp (-(((41:ℝ)/30) * ((223:ℝ)/(250)))) ≤ ((5910117:ℝ)/(20000000)) := by
  apply exp_neg_le_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_239_200 : Real.exp (-(((41:ℝ)/30) * ((239:ℝ)/(200)))) ≤ ((4882753:ℝ)/(25000000)) := by
  apply exp_neg_le_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_23_20 : Real.exp (-(((41:ℝ)/30) * ((23:ℝ)/(20)))) ≤ ((20769873:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_23_50 : Real.exp (-(((41:ℝ)/30) * ((23:ℝ)/(50)))) ≤ ((166657:ℝ)/(312500)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_27_50 : Real.exp (-(((41:ℝ)/30) * ((27:ℝ)/(50)))) ≤ ((4780691:ℝ)/(10000000)) := by
  apply exp_neg_le_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_29_50 : Real.exp (-(((41:ℝ)/30) * ((29:ℝ)/(50)))) ≤ ((176811:ℝ)/(390625)) := by
  apply exp_neg_le_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_2_5 : Real.exp (-(((41:ℝ)/30) * ((2:ℝ)/(5)))) ≤ ((57887619:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_327_250 : Real.exp (-(((41:ℝ)/30) * ((327:ℝ)/(250)))) ≤ ((2092017:ℝ)/(12500000)) := by
  apply exp_neg_le_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_379_500 : Real.exp (-(((41:ℝ)/30) * ((379:ℝ)/(500)))) ≤ ((70979:ℝ)/(200000)) := by
  apply exp_neg_le_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_37_40 : Real.exp (-(((41:ℝ)/30) * ((37:ℝ)/(40)))) ≤ ((1412373:ℝ)/(5000000)) := by
  apply exp_neg_le_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_39_40 : Real.exp (-(((41:ℝ)/30) * ((39:ℝ)/(40)))) ≤ ((2638169:ℝ)/(10000000)) := by
  apply exp_neg_le_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_3_10 : Real.exp (-(((41:ℝ)/30) * ((3:ℝ)/(10)))) ≤ ((33182513:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_3_5 : Real.exp (-(((41:ℝ)/30) * ((3:ℝ)/(5)))) ≤ ((22021583:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_401_500 : Real.exp (-(((41:ℝ)/30) * ((401:ℝ)/(500)))) ≤ ((4177287:ℝ)/(12500000)) := by
  apply exp_neg_le_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_41_40 : Real.exp (-(((41:ℝ)/30) * ((41:ℝ)/(40)))) ≤ ((6159789:ℝ)/(25000000)) := by
  apply exp_neg_le_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_437_500 : Real.exp (-(((41:ℝ)/30) * ((437:ℝ)/(500)))) ≤ ((1892909:ℝ)/(6250000)) := by
  apply exp_neg_le_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_43_40 : Real.exp (-(((41:ℝ)/30) * ((43:ℝ)/(40)))) ≤ ((23011717:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_443_500 : Real.exp (-(((41:ℝ)/30) * ((443:ℝ)/(500)))) ≤ ((3724237:ℝ)/(12500000)) := by
  apply exp_neg_le_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_451_500 : Real.exp (-(((41:ℝ)/30) * ((451:ℝ)/(500)))) ≤ ((14574737:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_453_500 : Real.exp (-(((41:ℝ)/30) * ((453:ℝ)/(500)))) ≤ ((14495279:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_47_40 : Real.exp (-(((41:ℝ)/30) * ((47:ℝ)/(40)))) ≤ ((10036111:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_47_50 : Real.exp (-(((41:ℝ)/30) * ((47:ℝ)/(50)))) ≤ ((13837141:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_49_40 : Real.exp (-(((41:ℝ)/30) * ((49:ℝ)/(40)))) ≤ ((9373217:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_507_500 : Real.exp (-(((41:ℝ)/30) * ((507:ℝ)/(500)))) ≤ ((25012363:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_51_40 : Real.exp (-(((41:ℝ)/30) * ((51:ℝ)/(40)))) ≤ ((3501643:ℝ)/(20000000)) := by
  apply exp_neg_le_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_527_500 : Real.exp (-(((41:ℝ)/30) * ((527:ℝ)/(500)))) ≤ ((11840861:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_549_500 : Real.exp (-(((41:ℝ)/30) * ((549:ℝ)/(500)))) ≤ ((22299633:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_567_500 : Real.exp (-(((41:ℝ)/30) * ((567:ℝ)/(500)))) ≤ ((21229043:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_59_50 : Real.exp (-(((41:ℝ)/30) * ((59:ℝ)/(50)))) ≤ ((1993553:ℝ)/(10000000)) := by
  apply exp_neg_le_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_5_4 : Real.exp (-(((41:ℝ)/30) * ((5:ℝ)/(4)))) ≤ ((18116749:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_6_5 : Real.exp (-(((41:ℝ)/30) * ((6:ℝ)/(5)))) ≤ ((3879601:ℝ)/(20000000)) := by
  apply exp_neg_le_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_701_1000 : Real.exp (-(((41:ℝ)/30) * ((701:ℝ)/(1000)))) ≤ ((7672933:ℝ)/(20000000)) := by
  apply exp_neg_le_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_779_1000 : Real.exp (-(((41:ℝ)/30) * ((779:ℝ)/(1000)))) ≤ ((8621357:ℝ)/(25000000)) := by
  apply exp_neg_le_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_79_100 : Real.exp (-(((41:ℝ)/30) * ((79:ℝ)/(100)))) ≤ ((271767:ℝ)/(800000)) := by
  apply exp_neg_le_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_79_50 : Real.exp (-(((41:ℝ)/30) * ((79:ℝ)/(50)))) ≤ ((2885051:ℝ)/(25000000)) := by
  apply exp_neg_le_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_7_8 : Real.exp (-(((41:ℝ)/30) * ((7:ℝ)/(8)))) ≤ ((30245181:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_841_1000 : Real.exp (-(((41:ℝ)/30) * ((841:ℝ)/(1000)))) ≤ ((31683737:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_87_100 : Real.exp (-(((41:ℝ)/30) * ((87:ℝ)/(100)))) ≤ ((7613141:ℝ)/(25000000)) := by
  apply exp_neg_le_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_87_250 : Real.exp (-(((41:ℝ)/30) * ((87:ℝ)/(250)))) ≤ ((15537801:ℝ)/(25000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_921_1000 : Real.exp (-(((41:ℝ)/30) * ((921:ℝ)/(1000)))) ≤ ((14201151:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_951_1000 : Real.exp (-(((41:ℝ)/30) * ((951:ℝ)/(1000)))) ≤ ((27261357:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_96_125 : Real.exp (-(((41:ℝ)/30) * ((96:ℝ)/(125)))) ≤ ((1093993:ℝ)/(3125000)) := by
  apply exp_neg_le_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_983_1000 : Real.exp (-(((41:ℝ)/30) * ((983:ℝ)/(1000)))) ≤ ((26094821:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_9_10 : Real.exp (-(((41:ℝ)/30) * ((9:ℝ)/(10)))) ≤ ((14614629:ℝ)/(50000000)) := by
  apply exp_neg_le_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_9_25 : Real.exp (-(((41:ℝ)/30) * ((9:ℝ)/(25)))) ≤ ((61140237:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_9_5 : Real.exp (-(((41:ℝ)/30) * ((9:ℝ)/(5)))) ≤ ((1067937:ℝ)/(12500000)) := by
  apply exp_neg_le_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exF_e_9_8 : Real.exp (-(((41:ℝ)/30) * ((9:ℝ)/(8)))) ≤ ((21491773:ℝ)/(100000000)) := by
  apply exp_neg_le_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_1017_1000 : ((685141:ℝ)/(100000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((1017:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_107_125 : ((753989:ℝ)/(50000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((107:ℝ)/(125)))) := by
  apply exp_neg_ge_rat (n := 18) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_1093_1000 : ((118029:ℝ)/(25000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((1093:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_11_10 : ((456197:ℝ)/(100000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((11:ℝ)/(10)))) := by
  apply exp_neg_ge_rat (n := 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_11_25 : ((5789367:ℝ)/(50000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((11:ℝ)/(25)))) := by
  apply exp_neg_ge_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_122_125 : ((837587:ℝ)/(100000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((122:ℝ)/(125)))) := by
  apply exp_neg_ge_rat (n := 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_1249_1000 : ((219823:ℝ)/(100000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((1249:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 21) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_127_100 : ((24791:ℝ)/(12500000)) ≤ Real.exp (-(((49:ℝ)/10) * ((127:ℝ)/(100)))) := by
  apply exp_neg_ge_rat (n := 21) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_12_25 : ((9517861:ℝ)/(100000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((12:ℝ)/(25)))) := by
  apply exp_neg_ge_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_139_200 : ((1659511:ℝ)/(50000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((139:ℝ)/(200)))) := by
  apply exp_neg_ge_rat (n := 18) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_13_25 : ((3911899:ℝ)/(50000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((13:ℝ)/(25)))) := by
  apply exp_neg_ge_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_141_100 : ((799:ℝ)/(800000)) ≤ Real.exp (-(((49:ℝ)/10) * ((141:ℝ)/(100)))) := by
  apply exp_neg_ge_rat (n := 21) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_143_125 : ((367721:ℝ)/(100000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((143:ℝ)/(125)))) := by
  apply exp_neg_ge_rat (n := 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_14_25 : ((3215629:ℝ)/(50000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((14:ℝ)/(25)))) := by
  apply exp_neg_ge_rat (n := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_163_200 : ((1843507:ℝ)/(100000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((163:ℝ)/(200)))) := by
  apply exp_neg_ge_rat (n := 18) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_171_200 : ((303077:ℝ)/(20000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((171:ℝ)/(200)))) := by
  apply exp_neg_ge_rat (n := 18) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_173_200 : ((1442921:ℝ)/(100000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((173:ℝ)/(200)))) := by
  apply exp_neg_ge_rat (n := 18) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_187_250 : ((511981:ℝ)/(20000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((187:ℝ)/(250)))) := by
  apply exp_neg_ge_rat (n := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_19_20 : ((951391:ℝ)/(100000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((19:ℝ)/(20)))) := by
  apply exp_neg_ge_rat (n := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_19_50 : ((15536159:ℝ)/(100000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((19:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_1_1 : ((372329:ℝ)/(50000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((1:ℝ)/(1)))) := by
  apply exp_neg_ge_rat (n := 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_1_2 : ((4314679:ℝ)/(50000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((1:ℝ)/(2)))) := by
  apply exp_neg_ge_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_1_4 : ((2937577:ℝ)/(10000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((1:ℝ)/(4)))) := by
  apply exp_neg_ge_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_1_5 : ((37531109:ℝ)/(100000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((1:ℝ)/(5)))) := by
  apply exp_neg_ge_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_207_250 : ((864869:ℝ)/(50000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((207:ℝ)/(250)))) := by
  apply exp_neg_ge_rat (n := 18) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_211_250 : ((799653:ℝ)/(50000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((211:ℝ)/(250)))) := by
  apply exp_neg_ge_rat (n := 18) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_21_20 : ((582847:ℝ)/(100000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((21:ℝ)/(20)))) := by
  apply exp_neg_ge_rat (n := 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_21_50 : ((12770913:ℝ)/(100000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((21:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_223_250 : ((79007:ℝ)/(6250000)) ≤ Real.exp (-(((49:ℝ)/10) * ((223:ℝ)/(250)))) := by
  apply exp_neg_ge_rat (n := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_239_200 : ((28641:ℝ)/(10000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((239:ℝ)/(200)))) := by
  apply exp_neg_ge_rat (n := 21) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_23_20 : ((357067:ℝ)/(100000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((23:ℝ)/(20)))) := by
  apply exp_neg_ge_rat (n := 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_23_50 : ((5248923:ℝ)/(50000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((23:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_27_50 : ((3546719:ℝ)/(50000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((27:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_29_50 : ((5830893:ℝ)/(100000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((29:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_2_5 : ((7042921:ℝ)/(50000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((2:ℝ)/(5)))) := by
  apply exp_neg_ge_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_327_250 : ((82317:ℝ)/(50000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((327:ℝ)/(250)))) := by
  apply exp_neg_ge_rat (n := 22) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_379_500 : ((2437493:ℝ)/(100000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((379:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 18) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_37_40 : ((8603:ℝ)/(800000)) ≤ Real.exp (-(((49:ℝ)/10) * ((37:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_39_40 : ((841701:ℝ)/(100000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((39:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_3_10 : ((5748137:ℝ)/(25000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((3:ℝ)/(10)))) := by
  apply exp_neg_ge_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_3_5 : ((1321643:ℝ)/(25000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((3:ℝ)/(5)))) := by
  apply exp_neg_ge_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_401_500 : ((49119:ℝ)/(2500000)) ≤ Real.exp (-(((49:ℝ)/10) * ((401:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_41_40 : ((658803:ℝ)/(100000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((41:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_437_500 : ((1380671:ℝ)/(100000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((437:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 18) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_43_40 : ((8057:ℝ)/(1562500)) ≤ Real.exp (-(((49:ℝ)/10) * ((43:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_443_500 : ((325457:ℝ)/(25000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((443:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 18) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_451_500 : ((1203663:ℝ)/(100000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((451:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 18) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_453_500 : ((1180301:ℝ)/(100000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((453:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 18) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_47_40 : ((315899:ℝ)/(100000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((47:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_47_50 : ((99917:ℝ)/(10000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((47:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_49_40 : ((30907:ℝ)/(12500000)) ≤ Real.exp (-(((49:ℝ)/10) * ((49:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 21) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_507_500 : ((695287:ℝ)/(100000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((507:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_51_40 : ((24191:ℝ)/(12500000)) ≤ Real.exp (-(((49:ℝ)/10) * ((51:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 21) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_527_500 : ((285767:ℝ)/(50000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((527:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_549_500 : ((46069:ℝ)/(10000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((549:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 22) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_567_500 : ((96547:ℝ)/(25000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((567:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_59_50 : ((154127:ℝ)/(50000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((59:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 21) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_5_4 : ((218749:ℝ)/(100000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((5:ℝ)/(4)))) := by
  apply exp_neg_ge_rat (n := 22) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_6_5 : ((139739:ℝ)/(50000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((6:ℝ)/(5)))) := by
  apply exp_neg_ge_rat (n := 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_701_1000 : ((3222863:ℝ)/(100000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((701:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_779_1000 : ((549787:ℝ)/(25000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((779:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 18) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_79_100 : ((260469:ℝ)/(12500000)) ≤ Real.exp (-(((49:ℝ)/10) * ((79:ℝ)/(100)))) := by
  apply exp_neg_ge_rat (n := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_79_50 : ((2171:ℝ)/(5000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((79:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_7_8 : ((1373923:ℝ)/(100000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((7:ℝ)/(8)))) := by
  apply exp_neg_ge_rat (n := 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_841_1000 : ((162299:ℝ)/(10000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((841:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_87_100 : ((1407999:ℝ)/(100000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((87:ℝ)/(100)))) := by
  apply exp_neg_ge_rat (n := 18) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_87_250 : ((18173603:ℝ)/(100000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((87:ℝ)/(250)))) := by
  apply exp_neg_ge_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_921_1000 : ((1096661:ℝ)/(100000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((921:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_951_1000 : ((47337:ℝ)/(5000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((951:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_96_125 : ((464187:ℝ)/(20000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((96:ℝ)/(125)))) := by
  apply exp_neg_ge_rat (n := 18) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_983_1000 : ((161869:ℝ)/(20000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((983:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_9_10 : ((1215517:ℝ)/(100000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((9:ℝ)/(10)))) := by
  apply exp_neg_ge_rat (n := 18) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_9_25 : ((3427161:ℝ)/(20000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((9:ℝ)/(25)))) := by
  apply exp_neg_ge_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_9_5 : ((7387:ℝ)/(50000000)) ≤ Real.exp (-(((49:ℝ)/10) * ((9:ℝ)/(5)))) := by
  apply exp_neg_ge_rat (n := 22) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_a_9_8 : ((1009:ℝ)/(250000)) ≤ Real.exp (-(((49:ℝ)/10) * ((9:ℝ)/(8)))) := by
  apply exp_neg_ge_rat (n := 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_1017_1000 : ((2716211:ℝ)/(5000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((1017:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_107_125 : ((7479221:ℝ)/(12500000)) ≤ Real.exp (-(((3:ℝ)/5) * ((107:ℝ)/(125)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_1093_1000 : ((51902667:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((1093:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_11_10 : ((51685133:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((11:ℝ)/(10)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_11_25 : ((76797353:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((11:ℝ)/(25)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_122_125 : ((55677169:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((122:ℝ)/(125)))) := by
  apply exp_neg_ge_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_1249_1000 : ((9453001:ℝ)/(20000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((1249:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_127_100 : ((23336601:ℝ)/(50000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((127:ℝ)/(100)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_12_25 : ((74976159:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((12:ℝ)/(25)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_139_200 : ((65902091:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((139:ℝ)/(200)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_13_25 : ((9149769:ℝ)/(12500000)) ≤ Real.exp (-(((3:ℝ)/5) * ((13:ℝ)/(25)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_141_100 : ((42912801:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((141:ℝ)/(100)))) := by
  apply exp_neg_ge_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_143_125 : ((50338499:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((143:ℝ)/(125)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_14_25 : ((7146231:ℝ)/(10000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((14:ℝ)/(25)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_163_200 : ((15330983:ℝ)/(25000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((163:ℝ)/(200)))) := by
  apply exp_neg_ge_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_171_200 : ((59869679:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((171:ℝ)/(200)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_173_200 : ((3719471:ℝ)/(6250000)) ≤ Real.exp (-(((3:ℝ)/5) * ((173:ℝ)/(200)))) := by
  apply exp_neg_ge_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_187_250 : ((3989961:ℝ)/(6250000)) ≤ Real.exp (-(((3:ℝ)/5) * ((187:ℝ)/(250)))) := by
  apply exp_neg_ge_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_19_20 : ((56552543:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((19:ℝ)/(20)))) := by
  apply exp_neg_ge_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_19_50 : ((3184497:ℝ)/(4000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((19:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_1_1 : ((54881163:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((1:ℝ)/(1)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_1_2 : ((37040911:ℝ)/(50000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((1:ℝ)/(2)))) := by
  apply exp_neg_ge_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_1_4 : ((86070797:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((1:ℝ)/(4)))) := by
  apply exp_neg_ge_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_1_5 : ((88692043:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((1:ℝ)/(5)))) := by
  apply exp_neg_ge_rat (n := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_207_250 : ((30423733:ℝ)/(50000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((207:ℝ)/(250)))) := by
  apply exp_neg_ge_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_211_250 : ((482129:ℝ)/(800000)) ≤ Real.exp (-(((3:ℝ)/5) * ((211:ℝ)/(250)))) := by
  apply exp_neg_ge_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_21_20 : ((2662959:ℝ)/(5000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((21:ℝ)/(20)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_21_50 : ((77724473:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((21:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_223_250 : ((3659701:ℝ)/(6250000)) ≤ Real.exp (-(((3:ℝ)/5) * ((223:ℝ)/(250)))) := by
  apply exp_neg_ge_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_239_200 : ((4882147:ℝ)/(10000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((239:ℝ)/(200)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_23_20 : ((25078803:ℝ)/(50000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((23:ℝ)/(20)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_23_50 : ((75881293:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((23:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_27_50 : ((2260157:ℝ)/(3125000)) ≤ Real.exp (-(((3:ℝ)/5) * ((27:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_29_50 : ((70609887:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((29:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_2_5 : ((39331393:ℝ)/(50000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((2:ℝ)/(5)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_327_250 : ((45621093:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((327:ℝ)/(250)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_379_500 : ((63457487:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((379:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_37_40 : ((28703613:ℝ)/(50000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((37:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_39_40 : ((27855293:ℝ)/(50000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((39:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_3_10 : ((83527021:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((3:ℝ)/(10)))) := by
  apply exp_neg_ge_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_3_5 : ((4360477:ℝ)/(6250000)) ≤ Real.exp (-(((3:ℝ)/5) * ((3:ℝ)/(5)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_401_500 : ((61804129:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((401:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_41_40 : ((54064089:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((41:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_437_500 : ((46243:ℝ)/(78125)) ≤ Real.exp (-(((3:ℝ)/5) * ((437:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_43_40 : ((26233127:ℝ)/(50000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((43:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_443_500 : ((11753279:ℝ)/(20000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((443:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_451_500 : ((58204937:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((451:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_453_500 : ((58065413:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((453:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_47_40 : ((49410857:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((47:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_47_50 : ((56892879:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((47:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_49_40 : ((9590109:ℝ)/(20000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((49:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_507_500 : ((13605523:ℝ)/(25000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((507:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_51_40 : ((46533393:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((51:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_527_500 : ((53131511:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((527:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_549_500 : ((6468399:ℝ)/(12500000)) ≤ Real.exp (-(((3:ℝ)/5) * ((549:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_567_500 : ((25320719:ℝ)/(50000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((567:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_59_50 : ((24631423:ℝ)/(50000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((59:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_5_4 : ((9447331:ℝ)/(20000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((5:ℝ)/(4)))) := by
  apply exp_neg_ge_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_6_5 : ((1947009:ℝ)/(4000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((6:ℝ)/(5)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_701_1000 : ((6566527:ℝ)/(10000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((701:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_779_1000 : ((31331469:ℝ)/(50000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((779:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_79_100 : ((2490029:ℝ)/(4000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((79:ℝ)/(100)))) := by
  apply exp_neg_ge_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_79_50 : ((38751527:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((79:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_7_8 : ((3697221:ℝ)/(6250000)) ≤ Real.exp (-(((3:ℝ)/5) * ((7:ℝ)/(8)))) := by
  apply exp_neg_ge_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_841_1000 : ((30187351:ℝ)/(50000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((841:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_87_100 : ((59333269:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((87:ℝ)/(100)))) := by
  apply exp_neg_ge_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_87_250 : ((81155753:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((87:ℝ)/(250)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_921_1000 : ((3596573:ℝ)/(6250000)) ≤ Real.exp (-(((3:ℝ)/5) * ((921:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_951_1000 : ((28259311:ℝ)/(50000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((951:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_96_125 : ((31538941:ℝ)/(50000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((96:ℝ)/(125)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_983_1000 : ((6930477:ℝ)/(12500000)) ≤ Real.exp (-(((3:ℝ)/5) * ((983:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_9_10 : ((2330993:ℝ)/(4000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((9:ℝ)/(10)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_9_25 : ((8057353:ℝ)/(10000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((9:ℝ)/(25)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_9_5 : ((265309:ℝ)/(781250)) ≤ Real.exp (-(((3:ℝ)/5) * ((9:ℝ)/(5)))) := by
  apply exp_neg_ge_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_b_9_8 : ((25457821:ℝ)/(50000000)) ≤ Real.exp (-(((3:ℝ)/5) * ((9:ℝ)/(8)))) := by
  apply exp_neg_ge_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_1017_1000 : ((36852483:ℝ)/(50000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((1017:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_107_125 : ((7735229:ℝ)/(10000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((107:ℝ)/(125)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_1093_1000 : ((14408701:ℝ)/(20000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((1093:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_11_10 : ((71892373:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((11:ℝ)/(10)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_11_25 : ((87634099:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((11:ℝ)/(25)))) := by
  apply exp_neg_ge_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_122_125 : ((4663571:ℝ)/(6250000)) ≤ Real.exp (-(((3:ℝ)/10) * ((122:ℝ)/(125)))) := by
  apply exp_neg_ge_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_1249_1000 : ((68749549:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((1249:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_127_100 : ((17079447:ℝ)/(25000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((127:ℝ)/(100)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_12_25 : ((43294387:ℝ)/(50000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((12:ℝ)/(25)))) := by
  apply exp_neg_ge_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_139_200 : ((81180103:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((139:ℝ)/(200)))) := by
  apply exp_neg_ge_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_13_25 : ((85555919:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((13:ℝ)/(25)))) := by
  apply exp_neg_ge_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_141_100 : ((65507863:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((141:ℝ)/(100)))) := by
  apply exp_neg_ge_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_143_125 : ((70949629:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((143:ℝ)/(125)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_14_25 : ((84535383:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((14:ℝ)/(25)))) := by
  apply exp_neg_ge_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_163_200 : ((39154799:ℝ)/(50000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((163:ℝ)/(200)))) := by
  apply exp_neg_ge_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_171_200 : ((77375499:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((171:ℝ)/(200)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_173_200 : ((1928593:ℝ)/(2500000)) ≤ Real.exp (-(((3:ℝ)/10) * ((173:ℝ)/(200)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_187_250 : ((79899547:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((187:ℝ)/(250)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_19_20 : ((3008057:ℝ)/(4000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((19:ℝ)/(20)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_19_50 : ((17845159:ℝ)/(20000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((19:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_1_1 : ((37040911:ℝ)/(50000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((1:ℝ)/(1)))) := by
  apply exp_neg_ge_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_1_2 : ((86070797:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((1:ℝ)/(2)))) := by
  apply exp_neg_ge_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_1_4 : ((23193587:ℝ)/(25000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((1:ℝ)/(4)))) := by
  apply exp_neg_ge_rat (n := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_1_5 : ((94176453:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((1:ℝ)/(5)))) := by
  apply exp_neg_ge_rat (n := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_207_250 : ((39002393:ℝ)/(50000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((207:ℝ)/(250)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_211_250 : ((3881563:ℝ)/(5000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((211:ℝ)/(250)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_21_20 : ((72978887:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((21:ℝ)/(20)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_21_50 : ((22040371:ℝ)/(25000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((21:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_223_250 : ((3826069:ℝ)/(5000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((223:ℝ)/(250)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_239_200 : ((34936181:ℝ)/(50000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((239:ℝ)/(200)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_23_20 : ((14164407:ℝ)/(20000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((23:ℝ)/(20)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_23_50 : ((87109869:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((23:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_27_50 : ((2126103:ℝ)/(2500000)) ≤ Real.exp (-(((3:ℝ)/10) * ((27:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_29_50 : ((84029689:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((29:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_2_5 : ((88692043:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((2:ℝ)/(5)))) := by
  apply exp_neg_ge_rat (n := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_327_250 : ((16885847:ℝ)/(25000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((327:ℝ)/(250)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_379_500 : ((79660207:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((379:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_37_40 : ((18941889:ℝ)/(25000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((37:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_39_40 : ((18659881:ℝ)/(25000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((39:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_3_10 : ((45696559:ℝ)/(50000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((3:ℝ)/(10)))) := by
  apply exp_neg_ge_rat (n := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_3_5 : ((83527021:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((3:ℝ)/(5)))) := by
  apply exp_neg_ge_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_401_500 : ((39307801:ℝ)/(50000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((401:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_41_40 : ((36764143:ℝ)/(50000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((41:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_437_500 : ((76935713:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((437:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_43_40 : ((72433593:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((43:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_443_500 : ((76659243:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((443:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_451_500 : ((238413:ℝ)/(312500)) ≤ Real.exp (-(((3:ℝ)/10) * ((451:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_453_500 : ((9525083:ℝ)/(12500000)) ≤ Real.exp (-(((3:ℝ)/10) * ((453:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_47_40 : ((8786607:ℝ)/(12500000)) ≤ Real.exp (-(((3:ℝ)/10) * ((47:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_47_50 : ((9428421:ℝ)/(12500000)) ≤ Real.exp (-(((3:ℝ)/10) * ((47:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_49_40 : ((17311583:ℝ)/(25000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((49:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_507_500 : ((7377133:ℝ)/(10000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((507:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_51_40 : ((68215389:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((51:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_527_500 : ((14578273:ℝ)/(20000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((527:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_549_500 : ((71935521:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((549:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_567_500 : ((35581399:ℝ)/(50000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((567:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_59_50 : ((8773437:ℝ)/(12500000)) ≤ Real.exp (-(((3:ℝ)/10) * ((59:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_5_4 : ((68728927:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((5:ℝ)/(4)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_6_5 : ((4360477:ℝ)/(6250000)) ≤ Real.exp (-(((3:ℝ)/10) * ((6:ℝ)/(5)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_701_1000 : ((8103411:ℝ)/(10000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((701:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_779_1000 : ((39579963:ℝ)/(50000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((779:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_79_100 : ((9862391:ℝ)/(12500000)) ≤ Real.exp (-(((3:ℝ)/10) * ((79:ℝ)/(100)))) := by
  apply exp_neg_ge_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_79_50 : ((2490029:ℝ)/(4000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((79:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_7_8 : ((19228159:ℝ)/(25000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((7:ℝ)/(8)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_841_1000 : ((77701159:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((841:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_87_100 : ((77028091:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((87:ℝ)/(100)))) := by
  apply exp_neg_ge_rat (n := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_87_250 : ((90086487:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((87:ℝ)/(250)))) := by
  apply exp_neg_ge_rat (n := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_921_1000 : ((18964633:ℝ)/(25000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((921:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_951_1000 : ((18794717:ℝ)/(25000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((951:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_96_125 : ((15884317:ℝ)/(20000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((96:ℝ)/(125)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_983_1000 : ((18615151:ℝ)/(25000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((983:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_9_10 : ((76337949:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((9:ℝ)/(10)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_9_25 : ((89762759:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((9:ℝ)/(25)))) := by
  apply exp_neg_ge_rat (n := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_9_5 : ((2330993:ℝ)/(4000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((9:ℝ)/(5)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_c_9_8 : ((71355197:ℝ)/(100000000)) ≤ Real.exp (-(((3:ℝ)/10) * ((9:ℝ)/(8)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_1017_1000 : ((1052353:ℝ)/(12500000)) ≤ Real.exp (-(((73:ℝ)/30) * ((1017:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_107_125 : ((3114107:ℝ)/(25000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((107:ℝ)/(125)))) := by
  apply exp_neg_ge_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_1093_1000 : ((6997387:ℝ)/(100000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((1093:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_11_10 : ((6879207:ℝ)/(100000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((11:ℝ)/(10)))) := by
  apply exp_neg_ge_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_11_25 : ((4284749:ℝ)/(12500000)) ≤ Real.exp (-(((73:ℝ)/30) * ((11:ℝ)/(25)))) := by
  apply exp_neg_ge_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_122_125 : ((9302069:ℝ)/(100000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((122:ℝ)/(125)))) := by
  apply exp_neg_ge_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_1249_1000 : ((4787157:ℝ)/(100000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((1249:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_127_100 : ((2274339:ℝ)/(50000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((127:ℝ)/(100)))) := by
  apply exp_neg_ge_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_12_25 : ((31098829:ℝ)/(100000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((12:ℝ)/(25)))) := by
  apply exp_neg_ge_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_139_200 : ((18430437:ℝ)/(100000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((139:ℝ)/(200)))) := by
  apply exp_neg_ge_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_13_25 : ((28214523:ℝ)/(100000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((13:ℝ)/(25)))) := by
  apply exp_neg_ge_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_141_100 : ((3235457:ℝ)/(100000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((141:ℝ)/(100)))) := by
  apply exp_neg_ge_rat (n := 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_143_125 : ((1545183:ℝ)/(25000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((143:ℝ)/(125)))) := by
  apply exp_neg_ge_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_14_25 : ((1023909:ℝ)/(4000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((14:ℝ)/(25)))) := by
  apply exp_neg_ge_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_163_200 : ((1376327:ℝ)/(10000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((163:ℝ)/(200)))) := by
  apply exp_neg_ge_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_171_200 : ((1560847:ℝ)/(12500000)) ≤ Real.exp (-(((73:ℝ)/30) * ((171:ℝ)/(200)))) := by
  apply exp_neg_ge_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_173_200 : ((6093299:ℝ)/(50000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((173:ℝ)/(200)))) := by
  apply exp_neg_ge_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_187_250 : ((8100207:ℝ)/(50000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((187:ℝ)/(250)))) := by
  apply exp_neg_ge_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_19_20 : ((1981919:ℝ)/(20000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((19:ℝ)/(20)))) := by
  apply exp_neg_ge_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_19_50 : ((39666361:ℝ)/(100000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((19:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_1_1 : ((4387193:ℝ)/(50000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((1:ℝ)/(1)))) := by
  apply exp_neg_ge_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_1_2 : ((2962159:ℝ)/(10000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((1:ℝ)/(2)))) := by
  apply exp_neg_ge_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_1_4 : ((1360643:ℝ)/(2500000)) ≤ Real.exp (-(((73:ℝ)/30) * ((1:ℝ)/(4)))) := by
  apply exp_neg_ge_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_1_5 : ((15366797:ℝ)/(25000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((1:ℝ)/(5)))) := by
  apply exp_neg_ge_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_207_250 : ((13334707:ℝ)/(100000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((207:ℝ)/(250)))) := by
  apply exp_neg_ge_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_211_250 : ((6412759:ℝ)/(50000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((211:ℝ)/(250)))) := by
  apply exp_neg_ge_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_21_20 : ((7769223:ℝ)/(100000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((21:ℝ)/(20)))) := by
  apply exp_neg_ge_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_21_50 : ((35987447:ℝ)/(100000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((21:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_223_250 : ((11411673:ℝ)/(100000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((223:ℝ)/(250)))) := by
  apply exp_neg_ge_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_239_200 : ((1364847:ℝ)/(25000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((239:ℝ)/(200)))) := by
  apply exp_neg_ge_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_23_20 : ((6091149:ℝ)/(100000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((23:ℝ)/(20)))) := by
  apply exp_neg_ge_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_23_50 : ((16324869:ℝ)/(50000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((23:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_27_50 : ((26874293:ℝ)/(100000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((27:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_29_50 : ((24381797:ℝ)/(100000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((29:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_2_5 : ((37782153:ℝ)/(100000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((2:ℝ)/(5)))) := by
  apply exp_neg_ge_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_327_250 : ((4146937:ℝ)/(100000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((327:ℝ)/(250)))) := by
  apply exp_neg_ge_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_379_500 : ((7905481:ℝ)/(50000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((379:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_37_40 : ((5265571:ℝ)/(50000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((37:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_39_40 : ((9324731:ℝ)/(100000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((39:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_3_10 : ((48190899:ℝ)/(100000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((3:ℝ)/(10)))) := by
  apply exp_neg_ge_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_3_5 : ((23223627:ℝ)/(100000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((3:ℝ)/(5)))) := by
  apply exp_neg_ge_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_401_500 : ((1775701:ℝ)/(12500000)) ≤ Real.exp (-(((73:ℝ)/30) * ((401:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_41_40 : ((4128261:ℝ)/(50000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((41:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_437_500 : ((11922613:ℝ)/(100000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((437:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_43_40 : ((1827671:ℝ)/(25000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((43:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_443_500 : ((5789753:ℝ)/(50000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((443:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_451_500 : ((11137341:ℝ)/(100000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((451:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_453_500 : ((11029463:ℝ)/(100000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((453:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_47_40 : ((114633:ℝ)/(2000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((47:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_47_50 : ((5076843:ℝ)/(50000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((47:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_49_40 : ((1268763:ℝ)/(25000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((49:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_507_500 : ((4240253:ℝ)/(50000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((507:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_51_40 : ((561709:ℝ)/(12500000)) ≤ Real.exp (-(((73:ℝ)/30) * ((51:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_527_500 : ((7693969:ℝ)/(100000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((527:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_549_500 : ((27003:ℝ)/(390625)) ≤ Real.exp (-(((73:ℝ)/30) * ((549:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_567_500 : ((253319:ℝ)/(4000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((567:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_59_50 : ((5662337:ℝ)/(100000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((59:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_5_4 : ((4775523:ℝ)/(100000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((5:ℝ)/(4)))) := by
  apply exp_neg_ge_rat (n := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_6_5 : ((674171:ℝ)/(12500000)) ≤ Real.exp (-(((73:ℝ)/30) * ((6:ℝ)/(5)))) := by
  apply exp_neg_ge_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_701_1000 : ((4540827:ℝ)/(25000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((701:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_779_1000 : ((15023317:ℝ)/(100000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((779:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_79_100 : ((14626527:ℝ)/(100000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((79:ℝ)/(100)))) := by
  apply exp_neg_ge_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_79_50 : ((2139353:ℝ)/(100000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((79:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_7_8 : ((2973409:ℝ)/(25000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((7:ℝ)/(8)))) := by
  apply exp_neg_ge_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_841_1000 : ((12919487:ℝ)/(100000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((841:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_87_100 : ((6019613:ℝ)/(50000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((87:ℝ)/(100)))) := by
  apply exp_neg_ge_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_87_250 : ((8575697:ℝ)/(20000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((87:ℝ)/(250)))) := by
  apply exp_neg_ge_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_921_1000 : ((5317073:ℝ)/(50000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((921:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_951_1000 : ((9885511:ℝ)/(100000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((951:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_96_125 : ((1928859:ℝ)/(12500000)) ≤ Real.exp (-(((73:ℝ)/30) * ((96:ℝ)/(125)))) := by
  apply exp_neg_ge_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_983_1000 : ((1828993:ℝ)/(20000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((983:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_9_10 : ((5595837:ℝ)/(50000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((9:ℝ)/(10)))) := by
  apply exp_neg_ge_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_9_25 : ((5205567:ℝ)/(12500000)) ≤ Real.exp (-(((73:ℝ)/30) * ((9:ℝ)/(25)))) := by
  apply exp_neg_ge_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_9_5 : ((250507:ℝ)/(20000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((9:ℝ)/(5)))) := by
  apply exp_neg_ge_rat (n := 18) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_d_9_8 : ((6473197:ℝ)/(100000000)) ≤ Real.exp (-(((73:ℝ)/30) * ((9:ℝ)/(8)))) := by
  apply exp_neg_ge_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_1017_1000 : ((24910021:ℝ)/(100000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((1017:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_107_125 : ((485013:ℝ)/(1562500)) ≤ Real.exp (-(((41:ℝ)/30) * ((107:ℝ)/(125)))) := by
  apply exp_neg_ge_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_1093_1000 : ((11226267:ℝ)/(50000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((1093:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_11_10 : ((22238763:ℝ)/(100000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((11:ℝ)/(10)))) := by
  apply exp_neg_ge_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_11_25 : ((54808037:ℝ)/(100000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((11:ℝ)/(25)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_122_125 : ((26345659:ℝ)/(100000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((122:ℝ)/(125)))) := by
  apply exp_neg_ge_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_1249_1000 : ((725661:ℝ)/(4000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((1249:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_127_100 : ((17628263:ℝ)/(100000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((127:ℝ)/(100)))) := by
  apply exp_neg_ge_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_12_25 : ((810817:ℝ)/(1562500)) ≤ Real.exp (-(((41:ℝ)/30) * ((12:ℝ)/(25)))) := by
  apply exp_neg_ge_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_139_200 : ((9670137:ℝ)/(25000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((139:ℝ)/(200)))) := by
  apply exp_neg_ge_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_13_25 : ((24565827:ℝ)/(50000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((13:ℝ)/(25)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_141_100 : ((14558429:ℝ)/(100000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((141:ℝ)/(100)))) := by
  apply exp_neg_ge_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_143_125 : ((10470443:ℝ)/(50000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((143:ℝ)/(125)))) := by
  apply exp_neg_ge_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_14_25 : ((11629471:ℝ)/(25000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((14:ℝ)/(25)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_163_200 : ((16414903:ℝ)/(50000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((163:ℝ)/(200)))) := by
  apply exp_neg_ge_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_171_200 : ((7770821:ℝ)/(25000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((171:ℝ)/(200)))) := by
  apply exp_neg_ge_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_173_200 : ((3832671:ℝ)/(12500000)) ≤ Real.exp (-(((41:ℝ)/30) * ((173:ℝ)/(200)))) := by
  apply exp_neg_ge_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_187_250 : ((35977851:ℝ)/(100000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((187:ℝ)/(250)))) := by
  apply exp_neg_ge_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_19_20 : ((27298639:ℝ)/(100000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((19:ℝ)/(20)))) := by
  apply exp_neg_ge_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_19_50 : ((29745851:ℝ)/(50000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((19:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_1_1 : ((25495539:ℝ)/(100000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((1:ℝ)/(1)))) := by
  apply exp_neg_ge_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_1_2 : ((12623277:ℝ)/(25000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((1:ℝ)/(2)))) := by
  apply exp_neg_ge_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_1_4 : ((35529251:ℝ)/(50000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((1:ℝ)/(4)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_1_5 : ((76083913:ℝ)/(100000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((1:ℝ)/(5)))) := by
  apply exp_neg_ge_rat (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_207_250 : ((32251681:ℝ)/(100000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((207:ℝ)/(250)))) := by
  apply exp_neg_ge_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_211_250 : ((31554099:ℝ)/(100000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((211:ℝ)/(250)))) := by
  apply exp_neg_ge_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_21_20 : ((1488221:ℝ)/(6250000)) ≤ Real.exp (-(((41:ℝ)/30) * ((21:ℝ)/(20)))) := by
  apply exp_neg_ge_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_21_50 : ((11265357:ℝ)/(20000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((21:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_223_250 : ((3693823:ℝ)/(12500000)) ≤ Real.exp (-(((41:ℝ)/30) * ((223:ℝ)/(250)))) := by
  apply exp_neg_ge_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_239_200 : ((19531011:ℝ)/(100000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((239:ℝ)/(200)))) := by
  apply exp_neg_ge_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_23_20 : ((1298117:ℝ)/(6250000)) ≤ Real.exp (-(((41:ℝ)/30) * ((23:ℝ)/(20)))) := by
  apply exp_neg_ge_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_23_50 : ((53330239:ℝ)/(100000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((23:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_27_50 : ((47806909:ℝ)/(100000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((27:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_29_50 : ((9052723:ℝ)/(20000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((29:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_2_5 : ((28943809:ℝ)/(50000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((2:ℝ)/(5)))) := by
  apply exp_neg_ge_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_327_250 : ((3347227:ℝ)/(20000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((327:ℝ)/(250)))) := by
  apply exp_neg_ge_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_379_500 : ((35489499:ℝ)/(100000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((379:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_37_40 : ((28247459:ℝ)/(100000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((37:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_39_40 : ((26381689:ℝ)/(100000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((39:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_3_10 : ((2654601:ℝ)/(4000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((3:ℝ)/(10)))) := by
  apply exp_neg_ge_rat (n := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_3_5 : ((8808633:ℝ)/(20000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((3:ℝ)/(5)))) := by
  apply exp_neg_ge_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_401_500 : ((6683659:ℝ)/(20000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((401:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_41_40 : ((4927831:ℝ)/(20000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((41:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_437_500 : ((30286543:ℝ)/(100000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((437:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_43_40 : ((5752929:ℝ)/(25000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((43:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_443_500 : ((5958779:ℝ)/(20000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((443:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_451_500 : ((29149473:ℝ)/(100000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((451:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_453_500 : ((28990557:ℝ)/(100000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((453:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_47_40 : ((20072221:ℝ)/(100000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((47:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_47_50 : ((27674281:ℝ)/(100000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((47:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_49_40 : ((18746433:ℝ)/(100000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((49:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_507_500 : ((12506181:ℝ)/(50000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((507:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_51_40 : ((8754107:ℝ)/(50000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((51:ℝ)/(40)))) := by
  apply exp_neg_ge_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_527_500 : ((23681721:ℝ)/(100000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((527:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_549_500 : ((1393727:ℝ)/(6250000)) ≤ Real.exp (-(((41:ℝ)/30) * ((549:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_567_500 : ((10614521:ℝ)/(50000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((567:ℝ)/(500)))) := by
  apply exp_neg_ge_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_59_50 : ((19935529:ℝ)/(100000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((59:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_5_4 : ((4529187:ℝ)/(25000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((5:ℝ)/(4)))) := by
  apply exp_neg_ge_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_6_5 : ((4849501:ℝ)/(25000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((6:ℝ)/(5)))) := by
  apply exp_neg_ge_rat (n := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_701_1000 : ((4795583:ℝ)/(12500000)) ≤ Real.exp (-(((41:ℝ)/30) * ((701:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_779_1000 : ((34485427:ℝ)/(100000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((779:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_79_100 : ((16985437:ℝ)/(50000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((79:ℝ)/(100)))) := by
  apply exp_neg_ge_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_79_50 : ((11540203:ℝ)/(100000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((79:ℝ)/(50)))) := by
  apply exp_neg_ge_rat (n := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_7_8 : ((1512259:ℝ)/(5000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((7:ℝ)/(8)))) := by
  apply exp_neg_ge_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_841_1000 : ((3960467:ℝ)/(12500000)) ≤ Real.exp (-(((41:ℝ)/30) * ((841:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_87_100 : ((30452563:ℝ)/(100000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((87:ℝ)/(100)))) := by
  apply exp_neg_ge_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_87_250 : ((62151203:ℝ)/(100000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((87:ℝ)/(250)))) := by
  apply exp_neg_ge_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_921_1000 : ((28402301:ℝ)/(100000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((921:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_951_1000 : ((6815339:ℝ)/(25000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((951:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_96_125 : ((1400311:ℝ)/(4000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((96:ℝ)/(125)))) := by
  apply exp_neg_ge_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_983_1000 : ((1304741:ℝ)/(5000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((983:ℝ)/(1000)))) := by
  apply exp_neg_ge_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_9_10 : ((29229257:ℝ)/(100000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((9:ℝ)/(10)))) := by
  apply exp_neg_ge_rat (n := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_9_25 : ((15285059:ℝ)/(25000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((9:ℝ)/(25)))) := by
  apply exp_neg_ge_rat (n := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_9_5 : ((1708699:ℝ)/(20000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((9:ℝ)/(5)))) := by
  apply exp_neg_ge_rat (n := 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])

lemma exG_e_9_8 : ((5372943:ℝ)/(25000000)) ≤ Real.exp (-(((41:ℝ)/30) * ((9:ℝ)/(8)))) := by
  apply exp_neg_ge_rat (n := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])


end Work.LinnikAreas.A7
