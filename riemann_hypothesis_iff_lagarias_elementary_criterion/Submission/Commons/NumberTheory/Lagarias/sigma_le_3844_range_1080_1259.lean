import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.IntervalCases
import Submission.Commons.NumberTheory.SigmaCheck

namespace Commons.NumberTheory.Lagarias

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private def sigmaFastAux : ℕ → ℕ → ℕ
  | _n, 0 => 0
  | n, k + 1 => sigmaFastAux n k + if n % (k + 1) = 0 then (k + 1) else 0

private def sigmaFast (n : ℕ) : ℕ := sigmaFastAux n n

private lemma sigmaFastAux_eq_sum (n k : ℕ) :
    sigmaFastAux n k = ∑ i ∈ Finset.Ico 1 (k + 1), if i ∣ n then i else 0 := by
  induction k with
  | zero =>
      simp [sigmaFastAux]
  | succ k ih =>
      rw [sigmaFastAux]
      rw [ih]
      rw [Finset.sum_Ico_succ_top (show 1 ≤ k + 1 by omega)]
      simp [Nat.dvd_iff_mod_eq_zero, add_comm]

private lemma sigma_eq_sigmaFast (n : ℕ) : (ArithmeticFunction.sigma 1 n : ℕ) = sigmaFast n := by
  rw [ArithmeticFunction.sigma_apply]
  unfold Nat.divisors
  rw [Finset.sum_filter]
  simp only [pow_one]
  rw [← sigmaFastAux_eq_sum n n]
  unfold sigmaFast
  rfl

private theorem sigma_le_3844_1080_1089_chk_1080 :
    (List.range' 1080 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 3844) = true := by
  decide +kernel

private lemma sigma_le_3844_1080_1089 (n : ℕ) (ha : 1080 ≤ n) (hb : n ≤ 1089) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 3844 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_3844_1080_1089_chk_1080 n (by omega) (by omega)

private theorem sigma_le_3844_1090_1099_chk_1090 :
    (List.range' 1090 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 3844) = true := by
  decide +kernel

private lemma sigma_le_3844_1090_1099 (n : ℕ) (ha : 1090 ≤ n) (hb : n ≤ 1099) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 3844 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_3844_1090_1099_chk_1090 n (by omega) (by omega)

private theorem sigma_le_3844_1100_1109_chk_1100 :
    (List.range' 1100 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 3844) = true := by
  decide +kernel

private lemma sigma_le_3844_1100_1109 (n : ℕ) (ha : 1100 ≤ n) (hb : n ≤ 1109) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 3844 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_3844_1100_1109_chk_1100 n (by omega) (by omega)

private theorem sigma_le_3844_1110_1119_chk_1110 :
    (List.range' 1110 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 3844) = true := by
  decide +kernel

private lemma sigma_le_3844_1110_1119 (n : ℕ) (ha : 1110 ≤ n) (hb : n ≤ 1119) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 3844 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_3844_1110_1119_chk_1110 n (by omega) (by omega)

private theorem sigma_le_3844_1120_1129_chk_1120 :
    (List.range' 1120 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 3844) = true := by
  decide +kernel

private lemma sigma_le_3844_1120_1129 (n : ℕ) (ha : 1120 ≤ n) (hb : n ≤ 1129) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 3844 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_3844_1120_1129_chk_1120 n (by omega) (by omega)

private theorem sigma_le_3844_1130_1139_chk_1130 :
    (List.range' 1130 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 3844) = true := by
  decide +kernel

private lemma sigma_le_3844_1130_1139 (n : ℕ) (ha : 1130 ≤ n) (hb : n ≤ 1139) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 3844 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_3844_1130_1139_chk_1130 n (by omega) (by omega)

private theorem sigma_le_3844_1140_1149_chk_1140 :
    (List.range' 1140 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 3844) = true := by
  decide +kernel

private lemma sigma_le_3844_1140_1149 (n : ℕ) (ha : 1140 ≤ n) (hb : n ≤ 1149) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 3844 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_3844_1140_1149_chk_1140 n (by omega) (by omega)

private theorem sigma_le_3844_1150_1159_chk_1150 :
    (List.range' 1150 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 3844) = true := by
  decide +kernel

private lemma sigma_le_3844_1150_1159 (n : ℕ) (ha : 1150 ≤ n) (hb : n ≤ 1159) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 3844 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_3844_1150_1159_chk_1150 n (by omega) (by omega)

private theorem sigma_le_3844_1160_1169_chk_1160 :
    (List.range' 1160 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 3844) = true := by
  decide +kernel

private lemma sigma_le_3844_1160_1169 (n : ℕ) (ha : 1160 ≤ n) (hb : n ≤ 1169) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 3844 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_3844_1160_1169_chk_1160 n (by omega) (by omega)

private theorem sigma_le_3844_1170_1179_chk_1170 :
    (List.range' 1170 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 3844) = true := by
  decide +kernel

private lemma sigma_le_3844_1170_1179 (n : ℕ) (ha : 1170 ≤ n) (hb : n ≤ 1179) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 3844 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_3844_1170_1179_chk_1170 n (by omega) (by omega)

private theorem sigma_le_3844_1180_1189_chk_1180 :
    (List.range' 1180 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 3844) = true := by
  decide +kernel

private lemma sigma_le_3844_1180_1189 (n : ℕ) (ha : 1180 ≤ n) (hb : n ≤ 1189) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 3844 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_3844_1180_1189_chk_1180 n (by omega) (by omega)

private theorem sigma_le_3844_1190_1199_chk_1190 :
    (List.range' 1190 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 3844) = true := by
  decide +kernel

private lemma sigma_le_3844_1190_1199 (n : ℕ) (ha : 1190 ≤ n) (hb : n ≤ 1199) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 3844 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_3844_1190_1199_chk_1190 n (by omega) (by omega)

private theorem sigma_le_3844_1200_1209_chk_1200 :
    (List.range' 1200 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 3844) = true := by
  decide +kernel

private lemma sigma_le_3844_1200_1209 (n : ℕ) (ha : 1200 ≤ n) (hb : n ≤ 1209) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 3844 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_3844_1200_1209_chk_1200 n (by omega) (by omega)

private theorem sigma_le_3844_1210_1219_chk_1210 :
    (List.range' 1210 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 3844) = true := by
  decide +kernel

private lemma sigma_le_3844_1210_1219 (n : ℕ) (ha : 1210 ≤ n) (hb : n ≤ 1219) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 3844 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_3844_1210_1219_chk_1210 n (by omega) (by omega)

private theorem sigma_le_3844_1220_1229_chk_1220 :
    (List.range' 1220 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 3844) = true := by
  decide +kernel

private lemma sigma_le_3844_1220_1229 (n : ℕ) (ha : 1220 ≤ n) (hb : n ≤ 1229) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 3844 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_3844_1220_1229_chk_1220 n (by omega) (by omega)

private theorem sigma_le_3844_1230_1239_chk_1230 :
    (List.range' 1230 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 3844) = true := by
  decide +kernel

private lemma sigma_le_3844_1230_1239 (n : ℕ) (ha : 1230 ≤ n) (hb : n ≤ 1239) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 3844 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_3844_1230_1239_chk_1230 n (by omega) (by omega)

private theorem sigma_le_3844_1240_1249_chk_1240 :
    (List.range' 1240 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 3844) = true := by
  decide +kernel

private lemma sigma_le_3844_1240_1249 (n : ℕ) (ha : 1240 ≤ n) (hb : n ≤ 1249) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 3844 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_3844_1240_1249_chk_1240 n (by omega) (by omega)

private theorem sigma_le_3844_1250_1259_chk_1250 :
    (List.range' 1250 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 3844) = true := by
  decide +kernel

private lemma sigma_le_3844_1250_1259 (n : ℕ) (ha : 1250 ≤ n) (hb : n ≤ 1259) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 3844 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_3844_1250_1259_chk_1250 n (by omega) (by omega)

theorem sigma_le_3844_range_1080_1259 (n : ℕ) (hL : 1080 ≤ n) (hU : n ≤ 1259) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 3844 := by
  by_cases h : n ≤ 1089
  · exact sigma_le_3844_1080_1089 n (by omega) h
  · by_cases h : n ≤ 1099
    · exact sigma_le_3844_1090_1099 n (by omega) h
    · by_cases h : n ≤ 1109
      · exact sigma_le_3844_1100_1109 n (by omega) h
      · by_cases h : n ≤ 1119
        · exact sigma_le_3844_1110_1119 n (by omega) h
        · by_cases h : n ≤ 1129
          · exact sigma_le_3844_1120_1129 n (by omega) h
          · by_cases h : n ≤ 1139
            · exact sigma_le_3844_1130_1139 n (by omega) h
            · by_cases h : n ≤ 1149
              · exact sigma_le_3844_1140_1149 n (by omega) h
              · by_cases h : n ≤ 1159
                · exact sigma_le_3844_1150_1159 n (by omega) h
                · by_cases h : n ≤ 1169
                  · exact sigma_le_3844_1160_1169 n (by omega) h
                  · by_cases h : n ≤ 1179
                    · exact sigma_le_3844_1170_1179 n (by omega) h
                    · by_cases h : n ≤ 1189
                      · exact sigma_le_3844_1180_1189 n (by omega) h
                      · by_cases h : n ≤ 1199
                        · exact sigma_le_3844_1190_1199 n (by omega) h
                        · by_cases h : n ≤ 1209
                          · exact sigma_le_3844_1200_1209 n (by omega) h
                          · by_cases h : n ≤ 1219
                            · exact sigma_le_3844_1210_1219 n (by omega) h
                            · by_cases h : n ≤ 1229
                              · exact sigma_le_3844_1220_1229 n (by omega) h
                              · by_cases h : n ≤ 1239
                                · exact sigma_le_3844_1230_1239 n (by omega) h
                                · by_cases h : n ≤ 1249
                                  · exact sigma_le_3844_1240_1249 n (by omega) h
                                  · by_cases h : n ≤ 1259
                                    · exact sigma_le_3844_1250_1259 n (by omega) h
                                    · omega

end Commons.NumberTheory.Lagarias