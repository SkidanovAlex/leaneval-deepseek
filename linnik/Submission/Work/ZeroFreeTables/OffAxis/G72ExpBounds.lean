import Submission.Work.ZeroFreeTables.OffAxis.G72Base

noncomputable section

namespace Work.ZeroFreeTables.OffAxis

open Work.ZeroFreeTables
open scoped BigOperators


/-- Taylor's theorem with the Lagrange remainder for `Real.exp`, 8 terms, on `[-1,1]`. -/
lemma exp_bound8 {y : ℝ} (hy : |y| ≤ 1) :
    |Real.exp y - (∑ m ∈ Finset.range 8, y^m / (Nat.factorial m : ℝ))| ≤ 9/322560 := by
  have h := Real.exp_bound (x := y) hy (n := 8) (by norm_num)
  have h4 : |y|^8 * (((8:ℕ) + 1 : ℝ) / ((Nat.factorial 8 : ℝ) * 8)) ≤ 9/322560 := by
    have h3 : |y|^8 ≤ 1 := by
      rw [← one_pow 8]
      exact pow_le_pow_left₀ (abs_nonneg y) hy 8
    calc |y|^8 * (((8:ℕ) + 1 : ℝ) / ((Nat.factorial 8 : ℝ) * 8))
        ≤ 1 * (((8:ℕ) + 1 : ℝ) / ((Nat.factorial 8 : ℝ) * 8)) := by gcongr
      _ = 9/322560 := by norm_num
  linarith [h, h4]

lemma exp1_upper : Real.exp ((1:ℝ)) ≤ (1359141/500000 : ℝ) := by
  have h := exp_bound8 (y := ((1:ℝ))) (by norm_num)
  have h2 : (∑ m ∈ Finset.range 8, (((1:ℝ)))^m / (Nat.factorial m : ℝ)) = (685/252 : ℝ) := by norm_num
  rw [h2] at h
  linarith [(abs_le.mp h).2]
lemma exp1_lower : (1359113/500000 : ℝ) ≤ Real.exp ((1:ℝ)) := by
  have h := exp_bound8 (y := ((1:ℝ))) (by norm_num)
  have h2 : (∑ m ∈ Finset.range 8, (((1:ℝ)))^m / (Nat.factorial m : ℝ)) = (685/252 : ℝ) := by norm_num
  rw [h2] at h
  linarith [(abs_le.mp h).1]
lemma exp1_5_upper : Real.exp ((1:ℝ)/5) ≤ (1221431/1000000 : ℝ) := by
  have h := exp_bound8 (y := ((1:ℝ)/5)) (by norm_num)
  have h2 : (∑ m ∈ Finset.range 8, (((1:ℝ)/5))^m / (Nat.factorial m : ℝ)) = (20038639/16406250 : ℝ) := by norm_num
  rw [h2] at h
  linarith [(abs_le.mp h).2]
lemma exp1_5_lower : (610687/500000 : ℝ) ≤ Real.exp ((1:ℝ)/5) := by
  have h := exp_bound8 (y := ((1:ℝ)/5)) (by norm_num)
  have h2 : (∑ m ∈ Finset.range 8, (((1:ℝ)/5))^m / (Nat.factorial m : ℝ)) = (20038639/16406250 : ℝ) := by norm_num
  rw [h2] at h
  linarith [(abs_le.mp h).1]
lemma exp1_100_upper : Real.exp ((1:ℝ)/100) ≤ (1010079/1000000 : ℝ) := by
  have h := exp_bound8 (y := ((1:ℝ)/100)) (by norm_num)
  have h2 : (∑ m ∈ Finset.range 8, (((1:ℝ)/100))^m / (Nat.factorial m : ℝ)) = (509065284210420701/504000000000000000 : ℝ) := by norm_num
  rw [h2] at h
  linarith [(abs_le.mp h).2]
lemma exp1_100_lower : (505011/500000 : ℝ) ≤ Real.exp ((1:ℝ)/100) := by
  have h := exp_bound8 (y := ((1:ℝ)/100)) (by norm_num)
  have h2 : (∑ m ∈ Finset.range 8, (((1:ℝ)/100))^m / (Nat.factorial m : ℝ)) = (509065284210420701/504000000000000000 : ℝ) := by norm_num
  rw [h2] at h
  linarith [(abs_le.mp h).1]
lemma exp3_10_upper : Real.exp ((3:ℝ)/10) ≤ (1349887/1000000 : ℝ) := by
  have h := exp_bound8 (y := ((3:ℝ)/10)) (by norm_num)
  have h2 : (∑ m ∈ Finset.range 8, (((3:ℝ)/10))^m / (Nat.factorial m : ℝ)) = (7559209313/5600000000 : ℝ) := by norm_num
  rw [h2] at h
  linarith [(abs_le.mp h).2]
lemma exp3_10_lower : (134983/100000 : ℝ) ≤ Real.exp ((3:ℝ)/10) := by
  have h := exp_bound8 (y := ((3:ℝ)/10)) (by norm_num)
  have h2 : (∑ m ∈ Finset.range 8, (((3:ℝ)/10))^m / (Nat.factorial m : ℝ)) = (7559209313/5600000000 : ℝ) := by norm_num
  rw [h2] at h
  linarith [(abs_le.mp h).1]
lemma exp31_100_upper : Real.exp ((31:ℝ)/100) ≤ (681727/500000 : ℝ) := by
  have h := exp_bound8 (y := ((31:ℝ)/100)) (by norm_num)
  have h2 : (∑ m ∈ Finset.range 8, (((31:ℝ)/100))^m / (Nat.factorial m : ℝ)) = (687166256418610811/504000000000000000 : ℝ) := by norm_num
  rw [h2] at h
  linarith [(abs_le.mp h).2]
lemma exp31_100_lower : (1363397/1000000 : ℝ) ≤ Real.exp ((31:ℝ)/100) := by
  have h := exp_bound8 (y := ((31:ℝ)/100)) (by norm_num)
  have h2 : (∑ m ∈ Finset.range 8, (((31:ℝ)/100))^m / (Nat.factorial m : ℝ)) = (687166256418610811/504000000000000000 : ℝ) := by norm_num
  rw [h2] at h
  linarith [(abs_le.mp h).1]
lemma exp7_10_upper : Real.exp ((7:ℝ)/10) ≤ (100689/50000 : ℝ) := by
  have h := exp_bound8 (y := ((7:ℝ)/10)) (by norm_num)
  have h2 : (∑ m ∈ Finset.range 8, (((7:ℝ)/10))^m / (Nat.factorial m : ℝ)) = (14499008339/7200000000 : ℝ) := by norm_num
  rw [h2] at h
  linarith [(abs_le.mp h).2]
lemma exp7_10_lower : (2013723/1000000 : ℝ) ≤ Real.exp ((7:ℝ)/10) := by
  have h := exp_bound8 (y := ((7:ℝ)/10)) (by norm_num)
  have h2 : (∑ m ∈ Finset.range 8, (((7:ℝ)/10))^m / (Nat.factorial m : ℝ)) = (14499008339/7200000000 : ℝ) := by norm_num
  rw [h2] at h
  linarith [(abs_le.mp h).1]
lemma exp1_2_upper : Real.exp ((1:ℝ)/2) ≤ (1319/800 : ℝ) := by
  have h := exp_bound8 (y := ((1:ℝ)/2)) (by norm_num)
  have h2 : (∑ m ∈ Finset.range 8, (((1:ℝ)/2))^m / (Nat.factorial m : ℝ)) = (354541/215040 : ℝ) := by norm_num
  rw [h2] at h
  linarith [(abs_le.mp h).2]
lemma exp1_2_lower : (1648693/1000000 : ℝ) ≤ Real.exp ((1:ℝ)/2) := by
  have h := exp_bound8 (y := ((1:ℝ)/2)) (by norm_num)
  have h2 : (∑ m ∈ Finset.range 8, (((1:ℝ)/2))^m / (Nat.factorial m : ℝ)) = (354541/215040 : ℝ) := by norm_num
  rw [h2] at h
  linarith [(abs_le.mp h).1]
lemma exp2_5_upper : Real.exp ((2:ℝ)/5) ≤ (1491853/1000000 : ℝ) := by
  have h := exp_bound8 (y := ((2:ℝ)/5)) (by norm_num)
  have h2 : (∑ m ∈ Finset.range 8, (((2:ℝ)/5))^m / (Nat.factorial m : ℝ)) = (36712873/24609375 : ℝ) := by norm_num
  rw [h2] at h
  linarith [(abs_le.mp h).2]
lemma exp2_5_lower : (372949/250000 : ℝ) ≤ Real.exp ((2:ℝ)/5) := by
  have h := exp_bound8 (y := ((2:ℝ)/5)) (by norm_num)
  have h2 : (∑ m ∈ Finset.range 8, (((2:ℝ)/5))^m / (Nat.factorial m : ℝ)) = (36712873/24609375 : ℝ) := by norm_num
  rw [h2] at h
  linarith [(abs_le.mp h).1]
lemma exp4_5_upper : Real.exp ((4:ℝ)/5) ≤ (445113/200000 : ℝ) := by
  have h := exp_bound8 (y := ((4:ℝ)/5)) (by norm_num)
  have h2 : (∑ m ∈ Finset.range 8, (((4:ℝ)/5))^m / (Nat.factorial m : ℝ)) = (6085451/2734375 : ℝ) := by norm_num
  rw [h2] at h
  linarith [(abs_le.mp h).2]
lemma exp4_5_lower : (556377/250000 : ℝ) ≤ Real.exp ((4:ℝ)/5) := by
  have h := exp_bound8 (y := ((4:ℝ)/5)) (by norm_num)
  have h2 : (∑ m ∈ Finset.range 8, (((4:ℝ)/5))^m / (Nat.factorial m : ℝ)) = (6085451/2734375 : ℝ) := by norm_num
  rw [h2] at h
  linarith [(abs_le.mp h).1]
lemma exp3_5_upper : Real.exp ((3:ℝ)/5) ≤ (1822147/1000000 : ℝ) := by
  have h := exp_bound8 (y := ((3:ℝ)/5)) (by norm_num)
  have h2 : (∑ m ∈ Finset.range 8, (((3:ℝ)/5))^m / (Nat.factorial m : ℝ)) = (39858839/21875000 : ℝ) := by norm_num
  rw [h2] at h
  linarith [(abs_le.mp h).2]
lemma exp3_5_lower : (182209/100000 : ℝ) ≤ Real.exp ((3:ℝ)/5) := by
  have h := exp_bound8 (y := ((3:ℝ)/5)) (by norm_num)
  have h2 : (∑ m ∈ Finset.range 8, (((3:ℝ)/5))^m / (Nat.factorial m : ℝ)) = (39858839/21875000 : ℝ) := by norm_num
  rw [h2] at h
  linarith [(abs_le.mp h).1]
lemma exp9_10_upper : Real.exp ((9:ℝ)/10) ≤ (122981/50000 : ℝ) := by
  have h := exp_bound8 (y := ((9:ℝ)/10)) (by norm_num)
  have h2 : (∑ m ∈ Finset.range 8, (((9:ℝ)/10))^m / (Nat.factorial m : ℝ)) = (13773711071/5600000000 : ℝ) := by norm_num
  rw [h2] at h
  linarith [(abs_le.mp h).2]
lemma exp9_10_lower : (2459563/1000000 : ℝ) ≤ Real.exp ((9:ℝ)/10) := by
  have h := exp_bound8 (y := ((9:ℝ)/10)) (by norm_num)
  have h2 : (∑ m ∈ Finset.range 8, (((9:ℝ)/10))^m / (Nat.factorial m : ℝ)) = (13773711071/5600000000 : ℝ) := by norm_num
  rw [h2] at h
  linarith [(abs_le.mp h).1]
lemma gridE_71_200 : |Real.exp (2*((71:ℝ)/200)) - (203399/100000 : ℝ)| ≤ 1/1000 := by
  rw [show (2:ℝ)*((71:ℝ)/200) = (71:ℝ)/100 by norm_num]
  have h := exp_bound8 (y := (71:ℝ)/100) (by norm_num)
  have h2 : (∑ m ∈ Finset.range 8, ((71:ℝ)/100)^m / (Nat.factorial m : ℝ)) = (113903413184035899/56000000000000000 : ℝ) := by norm_num
  rw [h2] at h
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]
lemma gridE_101_200 : |Real.exp (2*((101:ℝ)/200)) - (1716/625 : ℝ)| ≤ 1/1000 := by
  rw [show (2:ℝ)*((101:ℝ)/200) = (101:ℝ)/100 by norm_num]
  rw [show (101:ℝ)/100 = 1 + (1:ℝ)/100 by norm_num, Real.exp_add]
  have h1 := exp_bound8 (y := ((1:ℝ))) (by norm_num)
  have hs1 : (∑ m ∈ Finset.range 8, ((1:ℝ))^m / (Nat.factorial m : ℝ)) = (685/252 : ℝ) := by norm_num
  rw [hs1] at h1
  have h2 := exp_bound8 (y := ((1:ℝ)/100)) (by norm_num)
  have hs2 : (∑ m ∈ Finset.range 8, ((1:ℝ)/100)^m / (Nat.factorial m : ℝ)) = (509065284210420701/504000000000000000 : ℝ) := by norm_num
  rw [hs2] at h2
  have h1lo : (876791/322560 : ℝ) ≤ Real.exp 1 := by linarith [(abs_le.mp h1).1]
  have h1hi : Real.exp 1 ≤ (876809/322560 : ℝ) := by linarith [(abs_le.mp h1).2]
  have h2lo : (509051221710420701/504000000000000000 : ℝ) ≤ Real.exp (1/100) := by linarith [(abs_le.mp h2).1]
  have h2hi : Real.exp (1/100) ≤ (509079346710420701/504000000000000000 : ℝ) := by linarith [(abs_le.mp h2).2]
  have hnn1 : (0:ℝ) ≤ Real.exp (1/100) := Real.exp_nonneg _
  have hp1 := mul_le_mul h2lo h1lo (by norm_num : (0:ℝ) ≤ (876791/322560 : ℝ)) hnn1
  have hp2 := mul_le_mul h2hi h1hi (Real.exp_nonneg 1) (by norm_num : (0:ℝ) ≤ (509079346710420701/504000000000000000 : ℝ))
  rw [abs_le]
  constructor <;> linarith [hp1, hp2]
lemma gridE_131_200 : |Real.exp (2*((131:ℝ)/200)) - (370617/100000 : ℝ)| ≤ 1/1000 := by
  rw [show (2:ℝ)*((131:ℝ)/200) = (131:ℝ)/100 by norm_num]
  rw [show (131:ℝ)/100 = 1 + (31:ℝ)/100 by norm_num, Real.exp_add]
  have h1 := exp_bound8 (y := ((1:ℝ))) (by norm_num)
  have hs1 : (∑ m ∈ Finset.range 8, ((1:ℝ))^m / (Nat.factorial m : ℝ)) = (685/252 : ℝ) := by norm_num
  rw [hs1] at h1
  have h2 := exp_bound8 (y := ((31:ℝ)/100)) (by norm_num)
  have hs2 : (∑ m ∈ Finset.range 8, ((31:ℝ)/100)^m / (Nat.factorial m : ℝ)) = (687166256418610811/504000000000000000 : ℝ) := by norm_num
  rw [hs2] at h2
  have h1lo : (876791/322560 : ℝ) ≤ Real.exp 1 := by linarith [(abs_le.mp h1).1]
  have h1hi : Real.exp 1 ≤ (876809/322560 : ℝ) := by linarith [(abs_le.mp h1).2]
  have h2lo : (687152193918610811/504000000000000000 : ℝ) ≤ Real.exp (31/100) := by linarith [(abs_le.mp h2).1]
  have h2hi : Real.exp (31/100) ≤ (98168616988372973/72000000000000000 : ℝ) := by linarith [(abs_le.mp h2).2]
  have hnn1 : (0:ℝ) ≤ Real.exp (31/100) := Real.exp_nonneg _
  have hp1 := mul_le_mul h2lo h1lo (by norm_num : (0:ℝ) ≤ (876791/322560 : ℝ)) hnn1
  have hp2 := mul_le_mul h2hi h1hi (Real.exp_nonneg 1) (by norm_num : (0:ℝ) ≤ (98168616988372973/72000000000000000 : ℝ))
  rw [abs_le]
  constructor <;> linarith [hp1, hp2]
lemma expB2b_3_10 : Real.exp (2*((3:ℝ)/10)) ≤ (1822147/1000000 : ℝ) := by
  rw [show (2:ℝ)*((3:ℝ)/10) = (3:ℝ)/5 by norm_num]
  exact exp3_5_upper
lemma expB2b_7_20 : Real.exp (2*((7:ℝ)/20)) ≤ (100689/50000 : ℝ) := by
  rw [show (2:ℝ)*((7:ℝ)/20) = (7:ℝ)/10 by norm_num]
  exact exp7_10_upper
lemma expB2b_1_2 : Real.exp (2*((1:ℝ)/2)) ≤ (1359141/500000 : ℝ) := by
  rw [show (2:ℝ)*((1:ℝ)/2) = (1:ℝ) by norm_num]
  exact exp1_upper
lemma expB2b_3_5 : Real.exp (2*((3:ℝ)/5)) ≤ (1660097/500000 : ℝ) := by
  rw [show (2:ℝ)*((3:ℝ)/5) = 1 + (1:ℝ)/5 by norm_num, Real.exp_add]
  have h4 : (0:ℝ) ≤ Real.exp ((1:ℝ)/5) := Real.exp_nonneg _
  calc Real.exp 1 * Real.exp ((1:ℝ)/5) ≤ (1359141/500000 : ℝ) * Real.exp ((1:ℝ)/5) := mul_le_mul_of_nonneg_right exp1_upper h4
    _ ≤ (1359141/500000 : ℝ) * (1221431/1000000 : ℝ) := mul_le_mul_of_nonneg_left exp1_5_upper (by norm_num)
    _ ≤ (1660097/500000 : ℝ) := by norm_num
lemma expB2b_7_10 : Real.exp (2*((7:ℝ)/10)) ≤ (2027639/500000 : ℝ) := by
  rw [show (2:ℝ)*((7:ℝ)/10) = 1 + (2:ℝ)/5 by norm_num, Real.exp_add]
  have h4 : (0:ℝ) ≤ Real.exp ((2:ℝ)/5) := Real.exp_nonneg _
  calc Real.exp 1 * Real.exp ((2:ℝ)/5) ≤ (1359141/500000 : ℝ) * Real.exp ((2:ℝ)/5) := mul_le_mul_of_nonneg_right exp1_upper h4
    _ ≤ (1359141/500000 : ℝ) * (1491853/1000000 : ℝ) := mul_le_mul_of_nonneg_left exp2_5_upper (by norm_num)
    _ ≤ (2027639/500000 : ℝ) := by norm_num
lemma expB2b_4_5 : Real.exp (2*((4:ℝ)/5)) ≤ (495311/100000 : ℝ) := by
  rw [show (2:ℝ)*((4:ℝ)/5) = 1 + (3:ℝ)/5 by norm_num, Real.exp_add]
  have h4 : (0:ℝ) ≤ Real.exp ((3:ℝ)/5) := Real.exp_nonneg _
  calc Real.exp 1 * Real.exp ((3:ℝ)/5) ≤ (1359141/500000 : ℝ) * Real.exp ((3:ℝ)/5) := mul_le_mul_of_nonneg_right exp1_upper h4
    _ ≤ (1359141/500000 : ℝ) * (1822147/1000000 : ℝ) := mul_le_mul_of_nonneg_left exp3_5_upper (by norm_num)
    _ ≤ (495311/100000 : ℝ) := by norm_num
lemma expB2b_9_10 : Real.exp (2*((9:ℝ)/10)) ≤ (3024857/500000 : ℝ) := by
  rw [show (2:ℝ)*((9:ℝ)/10) = 1 + (4:ℝ)/5 by norm_num, Real.exp_add]
  have h4 : (0:ℝ) ≤ Real.exp ((4:ℝ)/5) := Real.exp_nonneg _
  calc Real.exp 1 * Real.exp ((4:ℝ)/5) ≤ (1359141/500000 : ℝ) * Real.exp ((4:ℝ)/5) := mul_le_mul_of_nonneg_right exp1_upper h4
    _ ≤ (1359141/500000 : ℝ) * (445113/200000 : ℝ) := mul_le_mul_of_nonneg_left exp4_5_upper (by norm_num)
    _ ≤ (3024857/500000 : ℝ) := by norm_num
lemma expB2b_1 : Real.exp (2*((1:ℝ)/1)) ≤ (3694529/500000 : ℝ) := by
  rw [show (2:ℝ)*((1:ℝ)/1) = 1 + 1 by norm_num, Real.exp_add]
  have h4 : (0:ℝ) ≤ Real.exp 1 := Real.exp_nonneg _
  calc Real.exp 1 * Real.exp 1 ≤ (1359141/500000 : ℝ) * Real.exp 1 := mul_le_mul_of_nonneg_right exp1_upper h4
    _ ≤ (1359141/500000 : ℝ) * (1359141/500000 : ℝ) := mul_le_mul_of_nonneg_left exp1_upper (by norm_num)
    _ ≤ (3694529/500000 : ℝ) := by norm_num

end Work.ZeroFreeTables.OffAxis
end
