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

private theorem sigma_le_4368_1260_1269_chk_1260 :
    (List.range' 1260 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 4368) = true := by
  decide +kernel

private lemma sigma_le_4368_1260_1269 (n : ℕ) (ha : 1260 ≤ n) (hb : n ≤ 1269) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 4368 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_4368_1260_1269_chk_1260 n (by omega) (by omega)

private theorem sigma_le_4368_1270_1279_chk_1270 :
    (List.range' 1270 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 4368) = true := by
  decide +kernel

private lemma sigma_le_4368_1270_1279 (n : ℕ) (ha : 1270 ≤ n) (hb : n ≤ 1279) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 4368 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_4368_1270_1279_chk_1270 n (by omega) (by omega)

private theorem sigma_le_4368_1280_1289_chk_1280 :
    (List.range' 1280 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 4368) = true := by
  decide +kernel

private lemma sigma_le_4368_1280_1289 (n : ℕ) (ha : 1280 ≤ n) (hb : n ≤ 1289) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 4368 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_4368_1280_1289_chk_1280 n (by omega) (by omega)

private theorem sigma_le_4368_1290_1299_chk_1290 :
    (List.range' 1290 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 4368) = true := by
  decide +kernel

private lemma sigma_le_4368_1290_1299 (n : ℕ) (ha : 1290 ≤ n) (hb : n ≤ 1299) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 4368 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_4368_1290_1299_chk_1290 n (by omega) (by omega)

private theorem sigma_le_4368_1300_1309_chk_1300 :
    (List.range' 1300 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 4368) = true := by
  decide +kernel

private lemma sigma_le_4368_1300_1309 (n : ℕ) (ha : 1300 ≤ n) (hb : n ≤ 1309) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 4368 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_4368_1300_1309_chk_1300 n (by omega) (by omega)

private theorem sigma_le_4368_1310_1319_chk_1310 :
    (List.range' 1310 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 4368) = true := by
  decide +kernel

private lemma sigma_le_4368_1310_1319 (n : ℕ) (ha : 1310 ≤ n) (hb : n ≤ 1319) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 4368 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_4368_1310_1319_chk_1310 n (by omega) (by omega)

private theorem sigma_le_4368_1320_1329_chk_1320 :
    (List.range' 1320 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 4368) = true := by
  decide +kernel

private lemma sigma_le_4368_1320_1329 (n : ℕ) (ha : 1320 ≤ n) (hb : n ≤ 1329) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 4368 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_4368_1320_1329_chk_1320 n (by omega) (by omega)

private theorem sigma_le_4368_1330_1339_chk_1330 :
    (List.range' 1330 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 4368) = true := by
  decide +kernel

private lemma sigma_le_4368_1330_1339 (n : ℕ) (ha : 1330 ≤ n) (hb : n ≤ 1339) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 4368 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_4368_1330_1339_chk_1330 n (by omega) (by omega)

private theorem sigma_le_4368_1340_1349_chk_1340 :
    (List.range' 1340 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 4368) = true := by
  decide +kernel

private lemma sigma_le_4368_1340_1349 (n : ℕ) (ha : 1340 ≤ n) (hb : n ≤ 1349) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 4368 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_4368_1340_1349_chk_1340 n (by omega) (by omega)

private theorem sigma_le_4368_1350_1359_chk_1350 :
    (List.range' 1350 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 4368) = true := by
  decide +kernel

private lemma sigma_le_4368_1350_1359 (n : ℕ) (ha : 1350 ≤ n) (hb : n ≤ 1359) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 4368 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_4368_1350_1359_chk_1350 n (by omega) (by omega)

private theorem sigma_le_4368_1360_1369_chk_1360 :
    (List.range' 1360 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 4368) = true := by
  decide +kernel

private lemma sigma_le_4368_1360_1369 (n : ℕ) (ha : 1360 ≤ n) (hb : n ≤ 1369) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 4368 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_4368_1360_1369_chk_1360 n (by omega) (by omega)

private theorem sigma_le_4368_1370_1379_chk_1370 :
    (List.range' 1370 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 4368) = true := by
  decide +kernel

private lemma sigma_le_4368_1370_1379 (n : ℕ) (ha : 1370 ≤ n) (hb : n ≤ 1379) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 4368 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_4368_1370_1379_chk_1370 n (by omega) (by omega)

private theorem sigma_le_4368_1380_1389_chk_1380 :
    (List.range' 1380 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 4368) = true := by
  decide +kernel

private lemma sigma_le_4368_1380_1389 (n : ℕ) (ha : 1380 ≤ n) (hb : n ≤ 1389) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 4368 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_4368_1380_1389_chk_1380 n (by omega) (by omega)

private theorem sigma_le_4368_1390_1399_chk_1390 :
    (List.range' 1390 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 4368) = true := by
  decide +kernel

private lemma sigma_le_4368_1390_1399 (n : ℕ) (ha : 1390 ≤ n) (hb : n ≤ 1399) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 4368 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_4368_1390_1399_chk_1390 n (by omega) (by omega)

private theorem sigma_le_4368_1400_1409_chk_1400 :
    (List.range' 1400 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 4368) = true := by
  decide +kernel

private lemma sigma_le_4368_1400_1409 (n : ℕ) (ha : 1400 ≤ n) (hb : n ≤ 1409) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 4368 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_4368_1400_1409_chk_1400 n (by omega) (by omega)

private theorem sigma_le_4368_1410_1419_chk_1410 :
    (List.range' 1410 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 4368) = true := by
  decide +kernel

private lemma sigma_le_4368_1410_1419 (n : ℕ) (ha : 1410 ≤ n) (hb : n ≤ 1419) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 4368 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_4368_1410_1419_chk_1410 n (by omega) (by omega)

private theorem sigma_le_4368_1420_1429_chk_1420 :
    (List.range' 1420 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 4368) = true := by
  decide +kernel

private lemma sigma_le_4368_1420_1429 (n : ℕ) (ha : 1420 ≤ n) (hb : n ≤ 1429) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 4368 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_4368_1420_1429_chk_1420 n (by omega) (by omega)

private theorem sigma_le_4368_1430_1439_chk_1430 :
    (List.range' 1430 10).all (Commons.NumberTheory.SigmaCheck.sigmaChk 4368) = true := by
  decide +kernel

private lemma sigma_le_4368_1430_1439 (n : ℕ) (ha : 1430 ≤ n) (hb : n ≤ 1439) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 4368 := by
  exact Commons.NumberTheory.SigmaCheck.sigma_le_of_check sigma_le_4368_1430_1439_chk_1430 n (by omega) (by omega)


theorem sigma_le_4368_range_1260_1439 (n : ℕ) (hL : 1260 ≤ n) (hU : n ≤ 1439) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 4368 := by
  by_cases h : n ≤ 1269
  · exact sigma_le_4368_1260_1269 n (by omega) h
  · by_cases h : n ≤ 1279
    · exact sigma_le_4368_1270_1279 n (by omega) h
    · by_cases h : n ≤ 1289
      · exact sigma_le_4368_1280_1289 n (by omega) h
      · by_cases h : n ≤ 1299
        · exact sigma_le_4368_1290_1299 n (by omega) h
        · by_cases h : n ≤ 1309
          · exact sigma_le_4368_1300_1309 n (by omega) h
          · by_cases h : n ≤ 1319
            · exact sigma_le_4368_1310_1319 n (by omega) h
            · by_cases h : n ≤ 1329
              · exact sigma_le_4368_1320_1329 n (by omega) h
              · by_cases h : n ≤ 1339
                · exact sigma_le_4368_1330_1339 n (by omega) h
                · by_cases h : n ≤ 1349
                  · exact sigma_le_4368_1340_1349 n (by omega) h
                  · by_cases h : n ≤ 1359
                    · exact sigma_le_4368_1350_1359 n (by omega) h
                    · by_cases h : n ≤ 1369
                      · exact sigma_le_4368_1360_1369 n (by omega) h
                      · by_cases h : n ≤ 1379
                        · exact sigma_le_4368_1370_1379 n (by omega) h
                        · by_cases h : n ≤ 1389
                          · exact sigma_le_4368_1380_1389 n (by omega) h
                          · by_cases h : n ≤ 1399
                            · exact sigma_le_4368_1390_1399 n (by omega) h
                            · by_cases h : n ≤ 1409
                              · exact sigma_le_4368_1400_1409 n (by omega) h
                              · by_cases h : n ≤ 1419
                                · exact sigma_le_4368_1410_1419 n (by omega) h
                                · by_cases h : n ≤ 1429
                                  · exact sigma_le_4368_1420_1429 n (by omega) h
                                  · by_cases h : n ≤ 1439
                                    · exact sigma_le_4368_1430_1439 n (by omega) h
                                    · omega


end Commons.NumberTheory.Lagarias