import Mathlib
import Mathlib.NumberTheory.AbelSummation
import Submission.Commons.NumberTheory.Mertens.mertens_lower
import Submission.Commons.NumberTheory.Mertens.legendre_sum_identity
import Submission.Commons.Analysis.SpecialFunctions.Log.log_factorial_sub_bounds
import Submission.Commons.NumberTheory.Chebyshev.psi_sub_theta_eventually_le

namespace Commons.NumberTheory.Mertens

open Finset Real MeasureTheory
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000

/-! ## Elementary upper bounds for `log` of `2^a 3^b 5^c` and of primes -/

private lemma logprime_le (p m a b c : ℕ) (hm : 2^a * 3^b * 5^c = m) (hmp : m ≤ p) (hm2 : 0 < m) :
    Real.log (p:ℝ) ≤ (a * (0.6931471808:ℝ) + b * 1.0986122888 + c * 1.6094379126) + ((p:ℝ) - m)/m := by
  have h2 : Real.log (2:ℝ) ≤ 0.6931471808 := le_of_lt Real.log_two_lt_d9
  have h3 : Real.log (3:ℝ) ≤ 1.0986122888 := le_of_lt Real.log_three_lt_d9
  have h5 : Real.log (5:ℝ) ≤ 1.6094379126 := le_of_lt Real.log_five_lt_d9
  have hcast : (((2^a * 3^b * 5^c : ℕ)) : ℝ) = (2:ℝ)^a * (3:ℝ)^b * (5:ℝ)^c := by
    push_cast; ring
  have hlogm : Real.log (m:ℝ) ≤ a * 0.6931471808 + b * 1.0986122888 + c * 1.6094379126 := by
    rw [← hm, hcast]
    rw [show (2:ℝ)^a * (3:ℝ)^b * (5:ℝ)^c = ((2:ℝ)^a * (3:ℝ)^b) * (5:ℝ)^c from by ring]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow]
    nlinarith [h2, h3, h5, (Nat.cast_nonneg a : (0:ℝ) ≤ (a:ℝ)),
      (Nat.cast_nonneg b : (0:ℝ) ≤ (b:ℝ)), (Nat.cast_nonneg c : (0:ℝ) ≤ (c:ℝ))]
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm2
  have hp0 : (0:ℝ) < (p:ℝ) := by
    have h : (m:ℝ) ≤ (p:ℝ) := by exact_mod_cast hmp
    linarith
  have hpos : (0:ℝ) < (p:ℝ)/(m:ℝ) := by positivity
  have h1 : Real.log ((p:ℝ)/(m:ℝ)) ≤ (p:ℝ)/(m:ℝ) - 1 := Real.log_le_sub_one_of_pos hpos
  have h3' : ((p:ℝ) - m)/m = (p:ℝ)/(m:ℝ) - 1 := by
    rw [sub_div, div_self (ne_of_gt hm0)]
  have h2' : Real.log (p:ℝ) = Real.log (m:ℝ) + Real.log ((p:ℝ)/(m:ℝ)) := by
    conv_lhs => rw [(mul_div_cancel₀ (p:ℝ) (ne_of_gt hm0)).symm]
    exact Real.log_mul (ne_of_gt hm0) (ne_of_gt hpos)
  rw [h2', h3']
  linarith

/-! ## The finite sum over primes `<= 401` -/

set_option maxRecDepth 1000000 in
private lemma partial_cSum_le :
    ∑ p ∈ (401:ℕ).primesLE, Real.log (p:ℝ)/((p:ℝ)*((p:ℝ)-1)) ≤ 0.7534 := by
  have h2 : Real.log (2:ℝ) ≤ 0.6931471808 := by
    have h := logprime_le 2 2 1 0 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h3 : Real.log (3:ℝ) ≤ 1.0986122888 := by
    have h := logprime_le 3 3 0 1 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h5 : Real.log (5:ℝ) ≤ 1.6094379126 := by
    have h := logprime_le 5 5 0 0 1 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h7 : Real.log (7:ℝ) ≤ 1.958426136267 := by
    have h := logprime_le 7 6 1 1 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h11 : Real.log (11:ℝ) ≤ 2.402585093401 := by
    have h := logprime_le 11 10 1 0 1 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h13 : Real.log (13:ℝ) ≤ 2.568239983734 := by
    have h := logprime_le 13 12 2 1 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h17 : Real.log (17:ℝ) ≤ 2.8350887232 := by
    have h := logprime_le 17 16 4 0 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h19 : Real.log (19:ℝ) ≤ 2.945927313956 := by
    have h := logprime_le 19 18 1 2 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h23 : Real.log (23:ℝ) ≤ 3.1457322742 := by
    have h := logprime_le 23 20 2 0 1 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h29 : Real.log (29:ℝ) ≤ 3.369910940475 := by
    have h := logprime_le 29 27 0 3 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h31 : Real.log (31:ℝ) ≤ 3.434530715534 := by
    have h := logprime_le 31 30 1 1 1 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h37 : Real.log (37:ℝ) ≤ 3.611296716978 := by
    have h := logprime_le 37 36 2 2 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h41 : Real.log (41:ℝ) ≤ 3.713879455001 := by
    have h := logprime_le 41 40 3 0 1 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h43 : Real.log (43:ℝ) ≤ 3.763879455001 := by
    have h := logprime_le 43 40 3 0 1 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h47 : Real.log (47:ℝ) ≤ 3.851106934645 := by
    have h := logprime_le 47 45 0 2 1 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h53 : Real.log (53:ℝ) ≤ 3.972023006 := by
    have h := logprime_le 53 50 1 0 2 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h59 : Real.log (59:ℝ) ≤ 4.081576639793 := by
    have h := logprime_le 59 54 1 3 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h61 : Real.log (61:ℝ) ≤ 4.111011229667 := by
    have h := logprime_le 61 60 2 1 1 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h67 : Real.log (67:ℝ) ≤ 4.2057580848 := by
    have h := logprime_le 67 64 6 0 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h71 : Real.log (71:ℝ) ≤ 4.2682580848 := by
    have h := logprime_le 71 64 6 0 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h73 : Real.log (73:ℝ) ≤ 4.290555008889 := by
    have h := logprime_le 73 72 3 2 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h79 : Real.log (79:ℝ) ≤ 4.370821447334 := by
    have h := logprime_le 79 75 0 1 2 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h83 : Real.log (83:ℝ) ≤ 4.419140513225 := by
    have h := logprime_le 83 81 0 4 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h89 : Real.log (89:ℝ) ≤ 4.493214587299 := by
    have h := logprime_le 89 81 0 4 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h97 : Real.log (97:ℝ) ≤ 4.574764859467 := by
    have h := logprime_le 97 96 5 1 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h101 : Real.log (101:ℝ) ≤ 4.6151701868 := by
    have h := logprime_le 101 100 2 0 2 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h103 : Real.log (103:ℝ) ≤ 4.635170186801 := by
    have h := logprime_le 103 100 2 0 2 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h107 : Real.log (107:ℝ) ≤ 4.675170186801 := by
    have h := logprime_le 107 100 2 0 2 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h109 : Real.log (109:ℝ) ≤ 4.69139048726 := by
    have h := logprime_le 109 108 2 3 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h113 : Real.log (113:ℝ) ≤ 4.728427524297 := by
    have h := logprime_le 113 108 2 3 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h127 : Real.log (127:ℝ) ≤ 4.8443137378 := by
    have h := logprime_le 127 125 0 0 3 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h131 : Real.log (131:ℝ) ≤ 4.8754677656 := by
    have h := logprime_le 131 128 7 0 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h137 : Real.log (137:ℝ) ≤ 4.920089593815 := by
    have h := logprime_le 137 135 0 3 1 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h139 : Real.log (139:ℝ) ≤ 4.93490440863 := by
    have h := logprime_le 139 135 0 3 1 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h149 : Real.log (149:ℝ) ≤ 5.004535523023 := by
    have h := logprime_le 149 144 4 2 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h151 : Real.log (151:ℝ) ≤ 5.017301961467 := by
    have h := logprime_le 151 150 1 1 2 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h157 : Real.log (157:ℝ) ≤ 5.057301961467 := by
    have h := logprime_le 157 150 1 1 2 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h163 : Real.log (163:ℝ) ≤ 5.093769175507 := by
    have h := logprime_le 163 162 1 4 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h167 : Real.log (167:ℝ) ≤ 5.118460533531 := by
    have h := logprime_le 167 162 1 4 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h173 : Real.log (173:ℝ) ≤ 5.155497570568 := by
    have h := logprime_le 173 162 1 4 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h179 : Real.log (179:ℝ) ≤ 5.192534607605 := by
    have h := logprime_le 179 162 1 4 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h181 : Real.log (181:ℝ) ≤ 5.198512407356 := by
    have h := logprime_le 181 180 2 2 1 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h191 : Real.log (191:ℝ) ≤ 5.254067962912 := by
    have h := logprime_le 191 180 2 2 1 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h193 : Real.log (193:ℝ) ≤ 5.262703706934 := by
    have h := logprime_le 193 192 6 1 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h197 : Real.log (197:ℝ) ≤ 5.283537040267 := by
    have h := logprime_le 197 192 6 1 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h199 : Real.log (199:ℝ) ≤ 5.293953706934 := by
    have h := logprime_le 199 192 6 1 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h211 : Real.log (211:ℝ) ≤ 5.3533173676 := by
    have h := logprime_le 211 200 3 0 2 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h223 : Real.log (223:ℝ) ≤ 5.407685816208 := by
    have h := logprime_le 223 216 3 3 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h227 : Real.log (227:ℝ) ≤ 5.424989291689 := by
    have h := logprime_le 227 225 0 2 2 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h229 : Real.log (229:ℝ) ≤ 5.433878180578 := by
    have h := logprime_le 229 225 0 2 2 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h233 : Real.log (233:ℝ) ≤ 5.451655958356 := by
    have h := logprime_le 233 225 0 2 2 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h239 : Real.log (239:ℝ) ≤ 5.478322625023 := by
    have h := logprime_le 239 225 0 2 2 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h241 : Real.log (241:ℝ) ≤ 5.484805591267 := by
    have h := logprime_le 241 240 4 1 1 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h251 : Real.log (251:ℝ) ≤ 5.5254609186 := by
    have h := logprime_le 251 250 1 0 3 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h257 : Real.log (257:ℝ) ≤ 5.5490836964 := by
    have h := logprime_le 257 256 8 0 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h263 : Real.log (263:ℝ) ≤ 5.5725211964 := by
    have h := logprime_le 263 256 8 0 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h269 : Real.log (269:ℝ) ≤ 5.5959586964 := by
    have h := logprime_le 269 256 8 0 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h271 : Real.log (271:ℝ) ≤ 5.602125663504 := by
    have h := logprime_le 271 270 1 3 1 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h277 : Real.log (277:ℝ) ≤ 5.624347885726 := by
    have h := logprime_le 277 270 1 3 1 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h281 : Real.log (281:ℝ) ≤ 5.639162700541 := by
    have h := logprime_le 281 270 1 3 1 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h283 : Real.log (283:ℝ) ≤ 5.646570107949 := by
    have h := logprime_le 283 270 1 3 1 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h293 : Real.log (293:ℝ) ≤ 5.680321592712 := by
    have h := logprime_le 293 288 5 2 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h307 : Real.log (307:ℝ) ≤ 5.727115808934 := by
    have h := logprime_le 307 300 2 1 2 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h311 : Real.log (311:ℝ) ≤ 5.740449142267 := by
    have h := logprime_le 311 300 2 1 2 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h313 : Real.log (313:ℝ) ≤ 5.747115808934 := by
    have h := logprime_le 313 300 2 1 2 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h317 : Real.log (317:ℝ) ≤ 5.760449142267 := by
    have h := logprime_le 317 300 2 1 2 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h331 : Real.log (331:ℝ) ≤ 5.802348455072 := by
    have h := logprime_le 331 324 2 4 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h337 : Real.log (337:ℝ) ≤ 5.820866973591 := by
    have h := logprime_le 337 324 2 4 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h347 : Real.log (347:ℝ) ≤ 5.851731171121 := by
    have h := logprime_le 347 324 2 4 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h349 : Real.log (349:ℝ) ≤ 5.857904010628 := by
    have h := logprime_le 349 324 2 4 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h353 : Real.log (353:ℝ) ≤ 5.87024968964 := by
    have h := logprime_le 353 324 2 4 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h359 : Real.log (359:ℝ) ≤ 5.888768208159 := by
    have h := logprime_le 359 324 2 4 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h367 : Real.log (367:ℝ) ≤ 5.905548477045 := by
    have h := logprime_le 367 360 3 2 1 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h373 : Real.log (373:ℝ) ≤ 5.922215143712 := by
    have h := logprime_le 373 360 3 2 1 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h379 : Real.log (379:ℝ) ≤ 5.937592693267 := by
    have h := logprime_le 379 375 0 1 3 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h383 : Real.log (383:ℝ) ≤ 5.948259359934 := by
    have h := logprime_le 383 375 0 1 3 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h389 : Real.log (389:ℝ) ≤ 5.963663387734 := by
    have h := logprime_le 389 384 7 1 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h397 : Real.log (397:ℝ) ≤ 5.984496721067 := by
    have h := logprime_le 397 384 7 1 0 (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h401 : Real.log (401:ℝ) ≤ 5.9939645484 := by
    have h := logprime_le 401 400 4 0 2 (by norm_num) (by norm_num) (by norm_num)
    linarith
  rw [show (401:ℕ).primesLE = ({2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401} : Finset ℕ) by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num
  linarith

private lemma theta_real_le (t : ℝ) (ht : 0 ≤ t) : Chebyshev.theta t ≤ Real.log 3 * t :=
  le_trans (Chebyshev.theta_le_psi t) (Commons.NumberTheory.Chebyshev.psi_le_log3_mul_real t ht)

private noncomputable def wt (i : ℕ) : ℝ := ((i:ℝ)*((i:ℝ)-1))⁻¹

private noncomputable def pl (i : ℕ) : ℝ := if i.Prime then Real.log (i:ℝ) else 0

private lemma G_eq_theta (K : ℕ) :
    ∑ i ∈ Finset.range (K+1), pl i = Chebyshev.theta (K : ℝ) := by
  have hIcc : Finset.range (K+1) = Finset.Icc 0 K := by
    ext i; simp only [Finset.mem_range, Finset.mem_Icc]; omega
  rw [hIcc, ← Commons.NumberTheory.Mertens.theta_eq_sum_cumulative (K:ℝ), Nat.floor_natCast]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Set.indicator_apply]
  by_cases h : i.Prime <;> simp [pl, h]

private lemma tel (M : ℕ) (hM : 402 ≤ M) :
    ∑ i ∈ Finset.Ico 402 M, (1/((i:ℝ)-2) - 1/((i:ℝ)-1)) = 1/400 - 1/((M:ℝ)-2) := by
  induction M with
  | zero => omega
  | succ M ih =>
    rcases Nat.lt_or_ge M 402 with h | h
    · have hM401 : M = 401 := by omega
      subst hM401
      norm_num
    · rw [Finset.sum_Ico_succ_top h, ih h]
      have hcast : ((M+1 : ℕ) : ℝ) - 2 = (M:ℝ) - 1 := by push_cast; ring
      rw [hcast]
      have hM402 : (402:ℝ) ≤ (M:ℝ) := by exact_mod_cast h
      have h0 : ((M:ℝ)-1) ≠ 0 := by linarith
      have h1 : ((M:ℝ)-2) ≠ 0 := by linarith
      field_simp
      ring

private lemma sum_inv_bound (M : ℕ) (hM : 402 ≤ M) :
    ∑ i ∈ Finset.Ico 402 M, (1/(((i:ℝ)-1)*((i:ℝ)+1))) ≤ 1/400 - 1/((M:ℝ)-2) := by
  calc ∑ i ∈ Finset.Ico 402 M, (1/(((i:ℝ)-1)*((i:ℝ)+1)))
      ≤ ∑ i ∈ Finset.Ico 402 M, (1/((i:ℝ)-2) - 1/((i:ℝ)-1)) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_Ico] at hi
        have hi3 : 3 ≤ i := by omega
        have hiR : (3:ℝ) ≤ (i:ℝ) := by exact_mod_cast hi3
        have ha : ((i:ℝ)-2) ≠ 0 := by linarith
        have hb : ((i:ℝ)-1) ≠ 0 := by linarith
        have hc : ((i:ℝ)+1) ≠ 0 := by linarith
        have e : 1/((i:ℝ)-2) - 1/((i:ℝ)-1) = 1/(((i:ℝ)-2)*((i:ℝ)-1)) := by
          rw [div_sub_div _ _ ha hb]
          congr 1
          ring
        rw [e]
        apply one_div_le_one_div_of_le
        · nlinarith
        · nlinarith
    _ = 1/400 - 1/((M:ℝ)-2) := tel M hM

private lemma tail_abel (m : ℕ) (hm : 402 ≤ m) :
    ∑ i ∈ Finset.Ico 402 (m+1), (if i.Prime then Real.log (i : ℝ) / ((i:ℝ)*((i:ℝ)-1)) else 0)
      ≤ 2 * Real.log 3 / 400 := by
  have hL : (∑ i ∈ Finset.Ico 402 (m+1), wt i * pl i)
      = ∑ i ∈ Finset.Ico 402 (m+1), (if i.Prime then Real.log (i : ℝ) / ((i:ℝ)*((i:ℝ)-1)) else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [wt, pl]
    by_cases h : i.Prime
    · rw [if_pos h, if_pos h, inv_mul_eq_div]
    · rw [if_neg h, if_neg h, mul_zero]
  rw [← hL]
  have habel := Finset.sum_Ico_by_parts (f := wt) (g := pl) (m := 402) (n := m+1) (Nat.lt_succ_of_le hm)
  simp only [smul_eq_mul] at habel
  rw [habel]
  simp only [Nat.add_sub_cancel]
  rw [G_eq_theta m, G_eq_theta 401]
  have hG : (∑ i ∈ Finset.Ico 402 m, (wt (i+1) - wt i) * (∑ k ∈ Finset.range (i+1), pl k))
      = ∑ i ∈ Finset.Ico 402 m, (wt (i+1) - wt i) * Chebyshev.theta (i:ℝ) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [G_eq_theta i]
  rw [hG]
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hmR : (402:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hTm : wt m * Chebyshev.theta (m:ℝ) ≤ Real.log 3 / ((m:ℝ)-1) := by
    have hθm : Chebyshev.theta (m:ℝ) ≤ Real.log 3 * (m:ℝ) := theta_real_le m (Nat.cast_nonneg m)
    have hm2 : (2:ℝ) ≤ (m:ℝ) := by linarith
    have hwpos : 0 ≤ wt m := by
      simp only [wt]
      apply inv_nonneg.mpr
      nlinarith
    calc wt m * Chebyshev.theta (m:ℝ) ≤ wt m * (Real.log 3 * m) :=
          mul_le_mul_of_nonneg_left hθm hwpos
      _ = Real.log 3 / ((m:ℝ)-1) := by
          simp only [wt]
          have h0 : (m:ℝ) ≠ 0 := by linarith
          have h1 : ((m:ℝ)-1) ≠ 0 := by linarith
          field_simp
  have hterm : ∀ i ∈ Finset.Ico 402 m,
      (-(wt (i+1) - wt i)) * Chebyshev.theta (i:ℝ)
        ≤ 2 * Real.log 3 * (1/(((i:ℝ)-1)*((i:ℝ)+1))) := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hi2 : 2 ≤ i := by omega
    have hiR : (2:ℝ) ≤ (i:ℝ) := by exact_mod_cast hi2
    have hθi : Chebyshev.theta (i:ℝ) ≤ Real.log 3 * (i:ℝ) := theta_real_le i (Nat.cast_nonneg i)
    have hdiff : -(wt (i+1) - wt i) = 2/((i:ℝ)*((i:ℝ)-1)*((i:ℝ)+1)) := by
      simp only [wt]
      have h1 : ((i+1:ℕ):ℝ) = (i:ℝ)+1 := by push_cast; ring
      rw [h1]
      have hna : ((i:ℝ)-1) ≠ 0 := by linarith
      have hnb : ((i:ℝ)+1) ≠ 0 := by linarith
      have hnc : ((i:ℝ)+1-1) ≠ 0 := by linarith
      have hnd : (i:ℝ) ≠ 0 := by linarith
      field_simp
      ring
    have hstep : 0 ≤ 2/((i:ℝ)*((i:ℝ)-1)*((i:ℝ)+1)) := by
      apply div_nonneg (by norm_num)
      apply mul_nonneg
      · exact mul_nonneg (by linarith) (by linarith)
      · linarith
    have hfin : 2/((i:ℝ)*((i:ℝ)-1)*((i:ℝ)+1)) * (Real.log 3 * (i:ℝ))
        = 2 * Real.log 3 * (1/(((i:ℝ)-1)*((i:ℝ)+1))) := by
      have hna : (i:ℝ) ≠ 0 := by linarith
      have hnb : ((i:ℝ)-1) ≠ 0 := by linarith
      have hnc : ((i:ℝ)+1) ≠ 0 := by linarith
      field_simp
    calc (-(wt (i+1) - wt i)) * Chebyshev.theta (i:ℝ)
        = (2/((i:ℝ)*((i:ℝ)-1)*((i:ℝ)+1))) * Chebyshev.theta (i:ℝ) := by rw [hdiff]
      _ ≤ (2/((i:ℝ)*((i:ℝ)-1)*((i:ℝ)+1))) * (Real.log 3 * (i:ℝ)) :=
          mul_le_mul_of_nonneg_left hθi hstep
      _ = 2 * Real.log 3 * (1/(((i:ℝ)-1)*((i:ℝ)+1))) := hfin
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum
  have hsb := sum_inv_bound m hm
  have hval : 2 * Real.log 3 * (∑ i ∈ Finset.Ico 402 m, (1/(((i:ℝ)-1)*((i:ℝ)+1))))
      ≤ 2 * Real.log 3 * (1/400 - 1/((m:ℝ)-2)) :=
    mul_le_mul_of_nonneg_left hsb (by positivity)
  have hS : -(∑ i ∈ Finset.Ico 402 m, (wt (i+1) - wt i) * Chebyshev.theta (i:ℝ))
      ≤ 2 * Real.log 3 * (1/400 - 1/((m:ℝ)-2)) := by
    have e : (∑ i ∈ Finset.Ico 402 m, ((-(wt (i+1) - wt i)) * Chebyshev.theta (i:ℝ)))
        = -(∑ i ∈ Finset.Ico 402 m, (wt (i+1) - wt i) * Chebyshev.theta (i:ℝ)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro i hi; ring
    rw [← e]
    linarith [hsum, hval]
  have hT401 : 0 ≤ wt 402 * Chebyshev.theta (401:ℝ) := by
    apply mul_nonneg
    · simp only [wt]; positivity
    · exact Chebyshev.theta_nonneg 401
  have hfinal2 : Real.log 3 / ((m:ℝ)-1) + 2 * Real.log 3 * (1/400 - 1/((m:ℝ)-2))
      ≤ 2 * Real.log 3 / 400 := by
    have hm1 : (0:ℝ) < (m:ℝ)-1 := by linarith
    have h400 : (0:ℝ) < (m:ℝ)-2 := by linarith
    rw [show Real.log 3 / ((m:ℝ)-1) + 2 * Real.log 3 * (1/400 - 1/((m:ℝ)-2))
        = Real.log 3 * (1/((m:ℝ)-1) + 2*(1/400 - 1/((m:ℝ)-2))) by ring]
    rw [show (2 * Real.log 3 / 400 : ℝ) = Real.log 3 * (2/400) by ring]
    apply mul_le_mul_of_nonneg_left _ hlog3
    have e : 1/((m:ℝ)-1) + 2*(1/400 - 1/((m:ℝ)-2)) = 1/((m:ℝ)-1) - 2/((m:ℝ)-2) + 2/400 := by ring
    rw [e]
    have hz : 1/((m:ℝ)-1) - 2/((m:ℝ)-2) ≤ 0 := by
      rw [div_sub_div _ _ (by linarith) (by linarith)]
      apply div_nonpos_of_nonpos_of_nonneg
      · nlinarith
      · positivity
    linarith
  linarith [hTm, hS, hT401, hfinal2]
private lemma tail_cSum_le (m : ℕ) :
    ∑ p ∈ m.primesLE.filter (fun p => 401 < p),
      Real.log (p:ℝ)/((p:ℝ)*((p:ℝ)-1)) ≤ 2 * Real.log 3 / 400 := by
  by_cases hm : 402 ≤ m
  · have hset : m.primesLE.filter (fun p => 401 < p)
        = (Finset.Ico 402 (m+1)).filter (fun p => p.Prime) := by
      ext p
      simp only [Finset.mem_filter, Nat.mem_primesLE, Finset.mem_Ico]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨by omega, by omega⟩, h2⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨by omega, h3⟩, by omega⟩
    rw [hset, Finset.sum_filter]
    exact tail_abel m hm
  · rw [not_le] at hm
    have hempty : m.primesLE.filter (fun p => 401 < p) = ∅ := by
      apply Finset.ext
      intro p
      constructor
      · intro hp
        rw [Finset.mem_filter, Nat.mem_primesLE] at hp
        omega
      · intro hp; exact absurd hp (by simp)
    rw [hempty, Finset.sum_empty]
    positivity

/-! ## Assembly: the bound on the prime-power correction sum -/

private lemma cSum_le (n : ℕ) :
    ∑ p ∈ n.primesLE, Real.log (p:ℝ)/((p:ℝ)*((p:ℝ)-1)) ≤ 0.76 := by
  have hterm_nonneg : ∀ p : ℕ, 2 ≤ p → 0 ≤ Real.log (p:ℝ)/((p:ℝ)*((p:ℝ)-1)) := by
    intro p hp
    have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
    apply div_nonneg
    · exact Real.log_nonneg (by linarith)
    · nlinarith
  rcases lt_or_ge n 402 with h | h
  · have hsub : n.primesLE ⊆ (401:ℕ).primesLE := by
      intro p hp
      rw [Nat.mem_primesLE] at hp ⊢
      exact ⟨by omega, hp.2⟩
    calc ∑ p ∈ n.primesLE, Real.log (p:ℝ)/((p:ℝ)*((p:ℝ)-1))
        ≤ ∑ p ∈ (401:ℕ).primesLE, Real.log (p:ℝ)/((p:ℝ)*((p:ℝ)-1)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun p hp _ => hterm_nonneg p (Nat.Prime.two_le (Nat.prime_of_mem_primesLE hp)))
      _ ≤ 0.7534 := partial_cSum_le
      _ ≤ 0.76 := by norm_num
  · have happ : (401:ℕ).primesLE = n.primesLE.filter (fun p => p ≤ 401) := by
      apply Finset.ext; intro p
      simp only [Nat.mem_primesLE, Finset.mem_filter]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨by omega, h2⟩, h1⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h3, h2⟩
    have hnot : n.primesLE.filter (fun p => ¬ p ≤ 401) = n.primesLE.filter (fun p => 401 < p) := by
      apply Finset.filter_congr
      intro p hp
      simp only [not_le]
    have htot : ∑ p ∈ n.primesLE, Real.log (p:ℝ)/((p:ℝ)*((p:ℝ)-1))
        = ∑ p ∈ (401:ℕ).primesLE, Real.log (p:ℝ)/((p:ℝ)*((p:ℝ)-1))
          + ∑ p ∈ n.primesLE.filter (fun p => 401 < p),
              Real.log (p:ℝ)/((p:ℝ)*((p:ℝ)-1)) := by
      conv_lhs => rw [← Finset.sum_filter_add_sum_filter_not (s := n.primesLE)
        (p := fun p => p ≤ 401) (f := fun p => Real.log (p:ℝ)/((p:ℝ)*((p:ℝ)-1)))]
      rw [← happ, hnot]
    have h2 : ∑ p ∈ n.primesLE.filter (fun p => 401 < p),
        Real.log (p:ℝ)/((p:ℝ)*((p:ℝ)-1)) ≤ 2 * Real.log 3 / 400 := tail_cSum_le n
    have h3 : 2 * Real.log 3 / 400 ≤ 0.0055 := by
      have hlt := Real.log_three_lt_d9
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 400)]
      linarith
    rw [htot]
    linarith [partial_cSum_le, h2, h3]

/-! ## The Legendre tail bound -/

private lemma legendre_tail_le (n p : ℕ) (hp : 2 ≤ p) :
    (∑ i ∈ Finset.Ico 2 (n+1), ((n / p^i : ℕ) : ℝ)) ≤ (n:ℝ)/((p:ℝ)*((p:ℝ)-1)) := by
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have hr0 : (0:ℝ) ≤ 1/(p:ℝ) := by positivity
  have hr1 : 1/(p:ℝ) < 1 := by
    rw [div_lt_one hp0]; linarith
  have hstep : ∀ i ∈ Finset.Ico 2 (n+1), ((n / p^i : ℕ) : ℝ) ≤ (n:ℝ) * ((1:ℝ)/(p:ℝ))^i := by
    intro i hi
    have hpi : (0:ℕ) < p^i := pow_pos (by omega) i
    have hle := Nat.cast_div_le (α := ℝ) (m := n) (n := p^i)
    have hcast : ((p^i : ℕ) : ℝ) = (p:ℝ)^i := by push_cast; ring
    rw [hcast] at hle
    have hrew : (n:ℝ)/(p:ℝ)^i = (n:ℝ) * ((1:ℝ)/(p:ℝ))^i := by
      rw [div_pow, one_pow]; field_simp
    linarith [hle]
  have hgeom : (∑ i ∈ Finset.Ico 2 (n+1), ((1:ℝ)/(p:ℝ))^i) ≤ 1/((p:ℝ)*((p:ℝ)-1)) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [show Finset.Ico 2 (0+1) = ∅ from by rw [Finset.Ico_eq_empty_iff]; omega,
        Finset.sum_empty]
      apply div_nonneg (by norm_num)
      nlinarith [hp2]
    · have hgn : (∑ i ∈ Finset.Ico 2 (n+1), ((1:ℝ)/(p:ℝ))^i)
          = (((1:ℝ)/(p:ℝ))^2 - ((1:ℝ)/(p:ℝ))^(n+1)) / (1 - 1/(p:ℝ)) := by
        rw [geom_sum_Ico' (ne_of_lt hr1) (by omega)]
      rw [hgn]
      have h1r : 0 < 1 - 1/(p:ℝ) := by linarith
      rw [div_le_iff₀ h1r]
      have hnn : 0 ≤ ((1:ℝ)/(p:ℝ))^(n+1) := by positivity
      have hval : (1/((p:ℝ)*((p:ℝ)-1))) * (1 - 1/(p:ℝ)) = ((1:ℝ)/(p:ℝ))^2 := by
        have hpne : (p:ℝ) ≠ 0 := ne_of_gt hp0
        have hp1ne : ((p:ℝ)-1) ≠ 0 := by linarith
        field_simp
      nlinarith [hval, hnn, hr0]
  calc (∑ i ∈ Finset.Ico 2 (n+1), ((n / p^i : ℕ) : ℝ))
      ≤ ∑ i ∈ Finset.Ico 2 (n+1), (n:ℝ) * ((1:ℝ)/(p:ℝ))^i := Finset.sum_le_sum hstep
    _ = (n:ℝ) * (∑ i ∈ Finset.Ico 2 (n+1), ((1:ℝ)/(p:ℝ))^i) := by rw [Finset.mul_sum]
    _ ≤ (n:ℝ) * (1/((p:ℝ)*((p:ℝ)-1))) :=
        mul_le_mul_of_nonneg_left hgeom (Nat.cast_nonneg n)
    _ = (n:ℝ)/((p:ℝ)*((p:ℝ)-1)) := by ring

/-! ## The integer lower bound for `logDiv` -/

private lemma logDiv_nat_ge (n : ℕ) (hn : 2 ≤ n) :
    Real.log (n:ℝ) - 1.76 + 1/(n:ℝ) ≤ logDiv (n:ℝ) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hfac := (Commons.Analysis.SpecialFunctions.Log.log_factorial_sub_bounds hn).1
  have hleg := Commons.NumberTheory.Mertens.legendre_sum_identity n
  have hlogDiv : logDiv (n:ℝ) = ∑ p ∈ n.primesLE, Real.log (p:ℝ)/(p:ℝ) := by
    unfold logDiv
    rw [Nat.floor_natCast]
  have hFnn : 0 ≤ ∑ p ∈ n.primesLE,
      (((n:ℝ)/(p:ℝ)) - ((n/p:ℕ):ℝ)) * Real.log (p:ℝ) := by
    apply Finset.sum_nonneg
    intro p hp
    rw [Nat.mem_primesLE] at hp
    have hp2 : 2 ≤ p := hp.2.two_le
    have hle : ((n/p:ℕ):ℝ) ≤ (n:ℝ)/(p:ℝ) := by
      have := Nat.cast_div_le (α := ℝ) (m := n) (n := p)
      have hcast : ((p:ℕ):ℝ) = (p:ℝ) := by norm_num
      rwa [hcast] at this
    have hlogp : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by
      have h1p : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
      linarith)
    exact mul_nonneg (by linarith) hlogp
  have hTle : (∑ p ∈ n.primesLE,
        (∑ i ∈ Finset.Ico 2 (n+1), ((n/p^i:ℕ):ℝ)) * Real.log (p:ℝ))
      ≤ (n:ℝ) * 0.76 := by
    have h1 : (∑ p ∈ n.primesLE,
        (∑ i ∈ Finset.Ico 2 (n+1), ((n/p^i:ℕ):ℝ)) * Real.log (p:ℝ))
        ≤ ∑ p ∈ n.primesLE, ((n:ℝ)/((p:ℝ)*((p:ℝ)-1))) * Real.log (p:ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [Nat.mem_primesLE] at hp
      have hp2 : 2 ≤ p := hp.2.two_le
      have hlogp : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by
        have h1p : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
        linarith)
      exact mul_le_mul_of_nonneg_right (legendre_tail_le n p hp2) hlogp
    have h2 : (∑ p ∈ n.primesLE, ((n:ℝ)/((p:ℝ)*((p:ℝ)-1))) * Real.log (p:ℝ))
        = (n:ℝ) * (∑ p ∈ n.primesLE, Real.log (p:ℝ)/((p:ℝ)*((p:ℝ)-1))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Nat.mem_primesLE] at hp
      have hp2 : 2 ≤ p := hp.2.two_le
      have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 0 < p)
      have hp1 : (0:ℝ) < (p:ℝ)-1 := by
        have h2p : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
        linarith
      field_simp
    calc (∑ p ∈ n.primesLE, (∑ i ∈ Finset.Ico 2 (n+1), ((n/p^i:ℕ):ℝ)) * Real.log (p:ℝ))
        ≤ ∑ p ∈ n.primesLE, ((n:ℝ)/((p:ℝ)*((p:ℝ)-1))) * Real.log (p:ℝ) := h1
      _ = (n:ℝ) * (∑ p ∈ n.primesLE, Real.log (p:ℝ)/((p:ℝ)*((p:ℝ)-1))) := h2
      _ ≤ (n:ℝ) * 0.76 := mul_le_mul_of_nonneg_left (cSum_le n) (Nat.cast_nonneg n)
  have hmain : (n:ℝ) * (Real.log (n:ℝ) - 1.76 + 1/(n:ℝ))
      ≤ (n:ℝ) * (∑ p ∈ n.primesLE, Real.log (p:ℝ)/(p:ℝ)) := by
    rw [hleg]
    have : (n:ℝ) * (Real.log (n:ℝ) - 1.76 + 1/(n:ℝ))
        = (n:ℝ) * Real.log (n:ℝ) - (n:ℝ) + 1 - 0.76 * (n:ℝ) := by
      field_simp
      ring
    rw [this]
    linarith [hfac, hFnn, hTle]
  have := le_of_mul_le_mul_left hmain hn0
  rw [hlogDiv]
  linarith [this]

/-! ## The real statement -/

/-- **Sharp lower bound for the first Mertens sum.** -/
theorem logDiv_ge_log_sub_sharp (x : ℝ) (hx : 2 ≤ x) :
    Real.log x - 1.76 ≤ Commons.NumberTheory.Mertens.logDiv x := by
  have hx0 : 0 < x := by linarith
  have hn2 : 2 ≤ ⌊x⌋₊ := by
    have h := Nat.floor_mono hx
    simp only [Nat.floor_ofNat] at h
    exact h
  have hn0 : (0:ℝ) < ((⌊x⌋₊ : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < ⌊x⌋₊)
  have hlogx : Real.log x ≤ Real.log ((⌊x⌋₊ : ℕ) : ℝ) + 1/((⌊x⌋₊ : ℕ) : ℝ) := by
    have h1 : Real.log x ≤ Real.log (((⌊x⌋₊ : ℕ) : ℝ)+1) :=
      Real.log_le_log hx0 (by have := Nat.lt_floor_add_one x; linarith)
    have hsplit : (((⌊x⌋₊ : ℕ) : ℝ)+1) = ((⌊x⌋₊ : ℕ) : ℝ)*(1 + 1/((⌊x⌋₊ : ℕ) : ℝ)) := by
      field_simp
    rw [hsplit, Real.log_mul (ne_of_gt hn0) (by positivity)] at h1
    have h2 : Real.log (1 + 1/((⌊x⌋₊ : ℕ) : ℝ)) ≤ 1/((⌊x⌋₊ : ℕ) : ℝ) := by
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 1/((⌊x⌋₊ : ℕ) : ℝ) by positivity)
      linarith
    linarith
  have hfloor : logDiv x = logDiv (((⌊x⌋₊ : ℕ) : ℝ)) := by
    simp only [logDiv]
    rw [Nat.floor_natCast]
  have hint := logDiv_nat_ge ⌊x⌋₊ hn2
  rw [hfloor]
  linarith [hlogx, hint]

end Commons.NumberTheory.Mertens
