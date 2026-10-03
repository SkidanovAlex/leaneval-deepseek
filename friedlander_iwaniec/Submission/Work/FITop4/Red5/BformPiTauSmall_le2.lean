import Mathlib
import Submission.Work.FITop4.Red5.BformPiTauSmall_le

namespace Work.FITop4.Red5

theorem BformPiTauSmall_le2 :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℕ, ∀ (x N Y Pz : ℕ) (κ Ccoe τ ϑ : ℝ),
      x₀ ≤ x → 1 ≤ N → 1 ≤ κ → κ ≤ 4 → 0 < ϑ → 8 * ϑ ≤ 1 → 1 ≤ ϑ * (x : ℝ) →
      (Y : ℝ) * (N : ℝ) ≤ κ * ϑ * (x : ℝ) →
      (∑ m ∈ Finset.Icc 1 Y, |∑ n ∈ Finset.Icc 1 (2 * N),
          (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ PiCond Pz n ∧ TauCond τ n
            then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc Ccoe n
              * Work.FITop.atilFIa (m * n) else 0)|)
        ≤ C * (ϑ * (x : ℝ)) ^ ((3 : ℝ) / 4) * (Real.log (x : ℝ)) ^ (65536 : ℕ) := by
  obtain ⟨C, x₀, hC, hbound⟩ := BformPiTauSmall_le
  refine ⟨(C : ℝ) * (4 : ℝ) ^ ((3 : ℝ) / 4), ?_, x₀, ?_⟩
  · exact mul_pos (by exact_mod_cast hC) (Real.rpow_pos_of_pos (by norm_num) _)
  intro x N Y Pz κ Ccoe τ ϑ hx hN hκ1 hκ4 hϑ0 hϑ8 hϑx hYN
  have hκ0 : 0 < κ := lt_of_lt_of_le zero_lt_one hκ1
  -- verify the parent's hypotheses with `ϑ̄ = κ * ϑ`
  have hϑ'0 : 0 < κ * ϑ := mul_pos hκ0 hϑ0
  have hϑx0 : 0 ≤ ϑ * (x : ℝ) := le_trans zero_le_one hϑx
  have h2 : 2 * (κ * ϑ) ≤ 1 := by nlinarith [hϑ8, hκ4, hϑ0]
  have hx1 : 1 ≤ κ * ϑ * (x : ℝ) := by
    have hle : (1 : ℝ) ≤ κ * (ϑ * (x : ℝ)) := by nlinarith [hϑx, hκ1, hϑx0]
    linarith [hle]
  have h := hbound x N Y Pz Ccoe τ (κ * ϑ) hx hN hϑ'0 h2 hx1 hYN
  -- `x ≥ 1`, so the logarithmic factor is nonnegative
  have hxpos : (0 : ℝ) < (x : ℝ) := by nlinarith [hϑx, hϑ0]
  have hxne : x ≠ 0 := by
    intro h0; rw [h0] at hxpos; simp at hxpos
  have hx1n : 1 ≤ x := Nat.one_le_iff_ne_zero.mpr hxne
  have hlog0 : 0 ≤ (Real.log (x : ℝ)) ^ (65536 : ℕ) :=
    pow_nonneg (Real.log_nonneg (by exact_mod_cast hx1n)) _
  -- absorb `κ^{3/4} ≤ 4^{3/4}` into the constant
  have hbase : ((κ * ϑ) * (x : ℝ)) ^ ((3 : ℝ) / 4)
      ≤ (4 : ℝ) ^ ((3 : ℝ) / 4) * (ϑ * (x : ℝ)) ^ ((3 : ℝ) / 4) := by
    have h5 : κ * (ϑ * (x : ℝ)) ≤ 4 * (ϑ * (x : ℝ)) :=
      mul_le_mul_of_nonneg_right hκ4 hϑx0
    have h6 : ((κ * ϑ) * (x : ℝ)) = κ * (ϑ * (x : ℝ)) := by ring
    rw [h6]
    calc (κ * (ϑ * (x : ℝ))) ^ ((3 : ℝ) / 4)
        ≤ (4 * (ϑ * (x : ℝ))) ^ ((3 : ℝ) / 4) :=
          Real.rpow_le_rpow (by positivity) h5 (by norm_num)
      _ = (4 : ℝ) ^ ((3 : ℝ) / 4) * (ϑ * (x : ℝ)) ^ ((3 : ℝ) / 4) :=
          Real.mul_rpow (by norm_num) hϑx0
  calc (∑ m ∈ Finset.Icc 1 Y, |∑ n ∈ Finset.Icc 1 (2 * N),
        (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ PiCond Pz n ∧ TauCond τ n
          then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc Ccoe n
            * Work.FITop.atilFIa (m * n) else 0)|)
      ≤ (C : ℝ) * ((κ * ϑ) * (x : ℝ)) ^ ((3 : ℝ) / 4)
          * (Real.log (x : ℝ)) ^ (65536 : ℕ) := h
    _ ≤ (C : ℝ) * ((4 : ℝ) ^ ((3 : ℝ) / 4) * (ϑ * (x : ℝ)) ^ ((3 : ℝ) / 4))
          * (Real.log (x : ℝ)) ^ (65536 : ℕ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg C)) hlog0
    _ = (C : ℝ) * (4 : ℝ) ^ ((3 : ℝ) / 4) * (ϑ * (x : ℝ)) ^ ((3 : ℝ) / 4)
          * (Real.log (x : ℝ)) ^ (65536 : ℕ) := by ring

end Work.FITop4.Red5
