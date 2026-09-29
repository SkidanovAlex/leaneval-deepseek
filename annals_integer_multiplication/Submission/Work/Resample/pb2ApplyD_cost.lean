import Mathlib
import Submission.Work.Resample.pb2AppCostDefs
import Submission.Work.Resample.paApplyDCost

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace Work.Resample

open HvdH

/-- Arithmetic helper: the second summand dominates, for the four-term `isz` sum of `PB2Br`. -/
theorem pb2_le_add2 {a b c d : ℕ} : b ≤ a + b + c + d := by omega

/-- Cost arithmetic of one axis step of the `B̃` half of paper Theorem 4.1: the total cost bound
`pb2AppCost` of the phases of `pb2ApplyE` is dominated by a constant times the per-axis budget
`PB2Br`.  Mirror of `Work.Resample.paApplyD_cost`. -/
theorem pb2ApplyD_cost (Kal Kmul Kb Kp Ku Km7 Km6 Km2 : ℕ) :
    ∃ Kc : ℕ, ∀ (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ) (j : ℕ) (Pj : List HvdH.Val) (nw : HvdH.Val),
      HvdH.ResParams p α ss ts → j < HvdH.D →
      HvdH.vsz nw + 1 ≤ ts.prod * (2 * p + 8) + ts.prod + 2 →
      (Pj.map HvdH.vsz).sum ≤ 8 * (Kb * (ts.getD j 0 + 1) * (p + 1) ^ Kb) →
      Work.Resample.pb2AppCost Kal Kmul Kb Kp Ku Km7 Km6 Km2 Cm p α ss ts j Pj nw ≤
        Kc * Work.Resample.PB2Br Kb Cm p α ss ts j := by
  refine ⟨10000 * (Kal + Kmul + Kb + Kp + Ku + Km7 + Km6 + Km2 + 1), ?_⟩
  intro Cm p α ss ts j Pj nw hRes hj hnw hPj
  obtain ⟨hsslen, htslen, hp100, hα2, hαp, hdim⟩ := hRes
  have hD1 : 1 ≤ D := pbRndD_pos
  have htsz : (ts.getD j 0).size ≤ p := Nat.size_le.mpr (hdim j hj).2.2.1
  have hssz : (ss.getD j 0).size ≤ p :=
    Nat.size_le.mpr (lt_trans (hdim j hj).2.1 (hdim j hj).2.2.1)
  have hRes' : ResParams p α ss ts := ⟨hsslen, htslen, hp100, hα2, hαp, hdim⟩
  have hAsz : (((ss.take j).prod).size) ≤ D * p :=
    pbRnd_size_take_prod_le p α ss ts hRes' (le_of_lt hj)
  have hmulsz : ((((ss.take j).prod * (ss.getD j 0) : ℕ)).size) ≤ D * p + p :=
    le_trans (pa_size_mul _ _) (Nat.add_le_add hAsz hssz)
  set P : ℕ := PB2Br Kb Cm p α ss ts j with hP
  have hP1 : 1 ≤ P := by rw [hP]; unfold PB2Br; omega
  have b1 : Kb * (ts.getD j 0 + 1) * (p + 1) ^ Kb ≤ P := by rw [hP]; unfold PB2Br; omega
  have b2 : (ss.take j).prod * (ts.drop (j + 1)).prod *
      (Kb * (ts.getD j 0 + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1) +
        Kb * (ts.getD j 0 + 1) * (p + 1) ^ 2) ≤ P := by rw [hP]; unfold PB2Br; omega
  have b3 : ((ss.take j).prod * (ts.drop (j + 1)).prod *
      (ss.getD j 0 + ts.getD j 0 + 1) + 1) *
      ((2 * p + 8) + ((ss.take j).prod * (ts.drop (j + 1)).prod *
        (ss.getD j 0 + ts.getD j 0 + 1)).size + 1) *
      (((ss.take j).prod * (ts.drop (j + 1)).prod *
        (ss.getD j 0 + ts.getD j 0 + 1)).size + 1) ≤ P := by rw [hP]; unfold PB2Br; omega
  have b4 : isz ((ss.take j).prod : ℤ) + isz ((ss.getD j 0 : ℕ) : ℤ) +
      isz ((ts.getD j 0 : ℕ) : ℤ) + isz (((ts.drop (j + 1)).prod : ℕ) : ℤ) ≤ P := by
    rw [hP]; unfold PB2Br; omega
  have b5 : ts.prod * (2 * p + 8) + ts.prod + 2 ≤ P := by rw [hP]; unfold PB2Br; omega
  have b6 : (D + 1) * (p + 2) ≤ P := by rw [hP]; unfold PB2Br; omega
  have b7 : (D + 1) * (p + 2) * ((D + 1) * (p + 2)) ≤ P := by rw [hP]; unfold PB2Br; omega
  have hzI : ∀ n : ℕ, isz ((n : ℕ) : ℤ) = n.size + 2 := by
    intro n; simp [isz, Int.natAbs_natCast]
  have hc1 : (ss.take j).prod * (ts.drop (j + 1)).prod *
      (Kb * (ts.getD j 0 + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1) +
        Kb * (ts.getD j 0 + 1) * (p + 1) ^ 2) ≤ P := b2
  have hc2 : Kal * ((ss.take j).prod * (ts.drop (j + 1)).prod *
      (ss.getD j 0 + ts.getD j 0 + 1) + 1) *
      ((2 * p + 8) + ((ss.take j).prod * (ts.drop (j + 1)).prod *
        (ss.getD j 0 + ts.getD j 0 + 1)).size + 1) *
      (((ss.take j).prod * (ts.drop (j + 1)).prod *
        (ss.getD j 0 + ts.getD j 0 + 1)).size + 1) ≤ Kal * P := by
    have h : Kal * ((ss.take j).prod * (ts.drop (j + 1)).prod *
        (ss.getD j 0 + ts.getD j 0 + 1) + 1) *
        ((2 * p + 8) + ((ss.take j).prod * (ts.drop (j + 1)).prod *
          (ss.getD j 0 + ts.getD j 0 + 1)).size + 1) *
        (((ss.take j).prod * (ts.drop (j + 1)).prod *
          (ss.getD j 0 + ts.getD j 0 + 1)).size + 1) =
      Kal * (((ss.take j).prod * (ts.drop (j + 1)).prod *
        (ss.getD j 0 + ts.getD j 0 + 1) + 1) *
        ((2 * p + 8) + ((ss.take j).prod * (ts.drop (j + 1)).prod *
          (ss.getD j 0 + ts.getD j 0 + 1)).size + 1) *
        (((ss.take j).prod * (ts.drop (j + 1)).prod *
          (ss.getD j 0 + ts.getD j 0 + 1)).size + 1)) := by ring
    rw [h]
    exact Nat.mul_le_mul_left Kal b3
  have hc3 : Kal * (isz ((ss.take j).prod : ℤ) + isz ((ss.getD j 0 : ℕ) : ℤ) +
      isz ((ts.getD j 0 : ℕ) : ℤ) + isz (((ts.drop (j + 1)).prod : ℕ) : ℤ)) ≤ Kal * P :=
    Nat.mul_le_mul_left Kal b4
  have hc4 : Kp * (vsz nw + 1) ≤ Kp * P := Nat.mul_le_mul_left Kp (le_trans hnw b5)
  have hc5 : 5 * ((Pj.map vsz).sum + 1) + 2 ≤ 47 * P := by
    have h1 : (Pj.map vsz).sum ≤ 8 * (Kb * (ts.getD j 0 + 1) * (p + 1) ^ Kb) := hPj
    have h2 : 5 * ((Pj.map vsz).sum + 1) + 2 ≤
        5 * (8 * (Kb * (ts.getD j 0 + 1) * (p + 1) ^ Kb) + 1) + 2 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 5 (Nat.add_le_add_right h1 1)) 2
    have h3 : 5 * (8 * (Kb * (ts.getD j 0 + 1) * (p + 1) ^ Kb) + 1) + 2 =
        40 * (Kb * (ts.getD j 0 + 1) * (p + 1) ^ Kb) + 7 := by ring
    have h4 : 40 * (Kb * (ts.getD j 0 + 1) * (p + 1) ^ Kb) + 7 ≤ 47 * P := pa_forty_seven b1 hP1
    exact le_trans h2 (le_trans (le_of_eq h3) h4)
  have hc6 : Ku * (vsz nw + 1) ≤ Ku * P := Nat.mul_le_mul_left Ku (le_trans hnw b5)
  have hc7 : Km7 * (vsz (Val.int ((ss.getD j 0 : ℕ) : ℤ)) + 1) ≤ 32 * Km7 * P := by
    have hsz : vsz (Val.int ((ss.getD j 0 : ℕ) : ℤ)) + 1 ≤ 32 * P := by
      rw [Work.ConvR.vsz_int, hzI (ss.getD j 0)]
      have h3 : (ss.getD j 0).size + 2 ≤ P := by
        rw [← hzI (ss.getD j 0)]
        exact le_trans (pb2_le_add2 (a := isz ((ss.take j).prod : ℤ))
          (b := isz ((ss.getD j 0 : ℕ) : ℤ)) (c := isz ((ts.getD j 0 : ℕ) : ℤ))
          (d := isz (((ts.drop (j + 1)).prod : ℕ) : ℤ))) b4
      have h4 : (ss.getD j 0).size + 2 + 1 ≤ P + 1 := Nat.add_le_add_right h3 1
      have h5 : P + 1 ≤ 32 * P :=
        le_trans (pa_two_mul hP1) (Nat.mul_le_mul_right P (by norm_num : 2 ≤ 32))
      exact le_trans h4 h5
    calc Km7 * (vsz (Val.int ((ss.getD j 0 : ℕ) : ℤ)) + 1) ≤ Km7 * (32 * P) :=
          Nat.mul_le_mul_left Km7 hsz
      _ = 32 * Km7 * P := by ring
  have hc8 : Km6 * (vsz (Val.int (((ss.take j).prod : ℕ) : ℤ)) + 1) ≤ 32 * Km6 * P := by
    have hsz : vsz (Val.int (((ss.take j).prod : ℕ) : ℤ)) + 1 ≤ 32 * P := by
      rw [Work.ConvR.vsz_int, hzI ((ss.take j).prod)]
      have h3 : ((ss.take j).prod).size + 2 ≤ P := by
        rw [← hzI ((ss.take j).prod)]
        exact le_trans (pa_le_add1 (a := isz ((ss.take j).prod : ℤ))
          (b := isz ((ss.getD j 0 : ℕ) : ℤ)) (c := isz ((ts.getD j 0 : ℕ) : ℤ))
          (d := isz (((ts.drop (j + 1)).prod : ℕ) : ℤ))) b4
      have h4 : ((ss.take j).prod).size + 2 + 1 ≤ P + 1 := Nat.add_le_add_right h3 1
      have h5 : P + 1 ≤ 32 * P :=
        le_trans (pa_two_mul hP1) (Nat.mul_le_mul_right P (by norm_num : 2 ≤ 32))
      exact le_trans h4 h5
    calc Km6 * (vsz (Val.int (((ss.take j).prod : ℕ) : ℤ)) + 1) ≤ Km6 * (32 * P) :=
          Nat.mul_le_mul_left Km6 hsz
      _ = 32 * Km6 * P := by ring
  have hc9 : Kmul * (((ss.take j).prod).size + 1) * ((ss.getD j 0).size + 1) ≤ Kmul * P := by
    have h1 : ((ss.take j).prod).size + 1 ≤ (D + 1) * (p + 2) := pa_size_add_one hAsz
    have h2 : (ss.getD j 0).size + 1 ≤ (D + 1) * (p + 2) := pa_size_add_one' hssz
    have h3 : (((ss.take j).prod).size + 1) * ((ss.getD j 0).size + 1) ≤
        ((D + 1) * (p + 2)) * ((D + 1) * (p + 2)) := Nat.mul_le_mul h1 h2
    have h4 : ((D + 1) * (p + 2)) * ((D + 1) * (p + 2)) ≤ P := by
      calc ((D + 1) * (p + 2)) * ((D + 1) * (p + 2))
          = (D + 1) * (p + 2) * ((D + 1) * (p + 2)) := by ring
        _ ≤ P := b7
    have h5 : (((ss.take j).prod).size + 1) * ((ss.getD j 0).size + 1) ≤ P := le_trans h3 h4
    calc Kmul * (((ss.take j).prod).size + 1) * ((ss.getD j 0).size + 1)
        = Kmul * ((((ss.take j).prod).size + 1) * ((ss.getD j 0).size + 1)) := by ring
      _ ≤ Kmul * P := Nat.mul_le_mul_left Kmul h5
  have hc10 : Km2 * (vsz (Val.int ((((ss.take j).prod) * (ss.getD j 0) : ℕ) : ℤ)) + 1) ≤
      16 * Km2 * P := by
    have hsz : vsz (Val.int ((((ss.take j).prod) * (ss.getD j 0) : ℕ) : ℤ)) + 1 ≤ 16 * P := by
      rw [Work.ConvR.vsz_int, hzI ((ss.take j).prod * (ss.getD j 0))]
      have h3 : (((ss.take j).prod * (ss.getD j 0) : ℕ)).size + 2 ≤ P :=
        le_trans (pa_size_mul_add hmulsz) b6
      have h4 : (((ss.take j).prod * (ss.getD j 0) : ℕ)).size + 2 + 1 ≤ P + 1 :=
        Nat.add_le_add_right h3 1
      have h5 : P + 1 ≤ 16 * P :=
        le_trans (pa_two_mul hP1) (Nat.mul_le_mul_right P (by norm_num : 2 ≤ 16))
      exact le_trans h4 h5
    calc Km2 * (vsz (Val.int ((((ss.take j).prod) * (ss.getD j 0) : ℕ) : ℤ)) + 1) ≤
          Km2 * (16 * P) := Nat.mul_le_mul_left Km2 hsz
      _ = 16 * Km2 * P := by ring
  have key : pb2AppCost Kal Kmul Kb Kp Ku Km7 Km6 Km2 Cm p α ss ts j Pj nw ≤
      (P + Kal * P + Kal * P) +
        (Kp * P + (47 * P + (Ku * P + (32 * Km7 * P + (32 * Km6 * P +
          (Kmul * P + 16 * Km2 * P)))))) := by
    unfold pb2AppCost
    exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hc1 hc2) hc3)
      (Nat.add_le_add hc4 (Nat.add_le_add hc5 (Nat.add_le_add hc6 (Nat.add_le_add hc7
        (Nat.add_le_add hc8 (Nat.add_le_add hc9 hc10))))))
  have hid : (P + Kal * P + Kal * P) +
        (Kp * P + (47 * P + (Ku * P + (32 * Km7 * P + (32 * Km6 * P +
          (Kmul * P + 16 * Km2 * P)))))) =
      (1 + 2 * Kal + Kp + 47 + Ku + 32 * Km7 + 32 * Km6 + Kmul + 16 * Km2) * P := by
    ring
  rw [hid] at key
  refine le_trans key (Nat.mul_le_mul_right P ?_)
  exact pa_coef

end Work.Resample
