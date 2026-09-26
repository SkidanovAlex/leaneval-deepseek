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

private theorem sigma_le_3224_1001_1010_chk_1001 :
    (List.range' 1001 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 3224) = true := by
  decide +kernel

private lemma sigma_le_3224_1001_1010 (n : ℕ) (ha : 1001 ≤ n) (hb : n ≤ 1010) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 3224 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_3224_1001_1010_chk_1001 n (by omega) (by omega)

private theorem sigma_le_3224_1011_1020_chk_1011 :
    (List.range' 1011 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 3224) = true := by
  decide +kernel

private lemma sigma_le_3224_1011_1020 (n : ℕ) (ha : 1011 ≤ n) (hb : n ≤ 1020) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 3224 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_3224_1011_1020_chk_1011 n (by omega) (by omega)

private theorem sigma_le_3224_1021_1030_chk_1021 :
    (List.range' 1021 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 3224) = true := by
  decide +kernel

private lemma sigma_le_3224_1021_1030 (n : ℕ) (ha : 1021 ≤ n) (hb : n ≤ 1030) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 3224 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_3224_1021_1030_chk_1021 n (by omega) (by omega)

private theorem sigma_le_3224_1031_1040_chk_1031 :
    (List.range' 1031 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 3224) = true := by
  decide +kernel

private lemma sigma_le_3224_1031_1040 (n : ℕ) (ha : 1031 ≤ n) (hb : n ≤ 1040) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 3224 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_3224_1031_1040_chk_1031 n (by omega) (by omega)

private theorem sigma_le_3224_1041_1050_chk_1041 :
    (List.range' 1041 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 3224) = true := by
  decide +kernel

private lemma sigma_le_3224_1041_1050 (n : ℕ) (ha : 1041 ≤ n) (hb : n ≤ 1050) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 3224 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_3224_1041_1050_chk_1041 n (by omega) (by omega)

private theorem sigma_le_3224_1051_1060_chk_1051 :
    (List.range' 1051 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 3224) = true := by
  decide +kernel

private lemma sigma_le_3224_1051_1060 (n : ℕ) (ha : 1051 ≤ n) (hb : n ≤ 1060) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 3224 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_3224_1051_1060_chk_1051 n (by omega) (by omega)

private theorem sigma_le_3224_1061_1070_chk_1061 :
    (List.range' 1061 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 3224) = true := by
  decide +kernel

private lemma sigma_le_3224_1061_1070 (n : ℕ) (ha : 1061 ≤ n) (hb : n ≤ 1070) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 3224 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_3224_1061_1070_chk_1061 n (by omega) (by omega)

private theorem sigma_le_3224_1071_1079_chk_1071 :
    (List.range' 1071 9).all (Commons.NumberTheory.SigmaCheck.sigmaChk 3224) = true := by
  decide +kernel

private lemma sigma_le_3224_1071_1079 (n : ℕ) (ha : 1071 ≤ n) (hb : n ≤ 1079) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 3224 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_3224_1071_1079_chk_1071 n (by omega) (by omega)

theorem sigma_le_3224_range_1001_1079 (n : ℕ) (hL : 1001 ≤ n) (hU : n ≤ 1079) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 3224 := by
  by_cases h : n ≤ 1010
  · exact sigma_le_3224_1001_1010 n (by omega) h
  · by_cases h : n ≤ 1020
    · exact sigma_le_3224_1011_1020 n (by omega) h
    · by_cases h : n ≤ 1030
      · exact sigma_le_3224_1021_1030 n (by omega) h
      · by_cases h : n ≤ 1040
        · exact sigma_le_3224_1031_1040 n (by omega) h
        · by_cases h : n ≤ 1050
          · exact sigma_le_3224_1041_1050 n (by omega) h
          · by_cases h : n ≤ 1060
            · exact sigma_le_3224_1051_1060 n (by omega) h
            · by_cases h : n ≤ 1070
              · exact sigma_le_3224_1061_1070 n (by omega) h
              · by_cases h : n ≤ 1079
                · exact sigma_le_3224_1071_1079 n (by omega) h
                · omega

end Commons.NumberTheory.Lagarias