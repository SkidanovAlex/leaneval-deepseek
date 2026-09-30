import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.SD.window_helpers

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

/-- Existence of a geometric grid `P (7/5)^j` (with `1 < 7/5`) whose window starts
`j₀ … N` all dominate `T`, all dominate `P`, all have `P (7/5)^(j+1) ≤ Q`, and such
that the logarithmic ratio `log (P (7/5)^N) / log (P (7/5)^j₀)` exceeds `exp (4K+CM)`. -/
theorem geo_grid_exists (P Q T K CM : ℝ) (h2P : 2 ≤ P) (hT : 1 ≤ T)
    (hQ4 : P * T * Real.exp 4 ≤ Q)
    (hlogQ : Real.exp (4 * K + CM + 1) * (Real.log P + Real.log T + 2) + 2 ≤ Real.log Q) :
    ∃ N j₀ : ℕ, j₀ + 1 ≤ N ∧
      (∀ j ∈ Finset.Icc j₀ (N - 1), T ≤ P * (7/5)^j) ∧
      (∀ j ∈ Finset.Icc j₀ (N - 1), P ≤ P * (7/5)^j) ∧
      (∀ j ∈ Finset.Icc j₀ (N - 1), P * (7/5)^(j+1) ≤ Q) ∧
      Real.exp (4*K + CM) < Real.log (P * (7/5)^N) / Real.log (P * (7/5)^j₀) := by
  have hP : 0 < P := by linarith
  have hTpos : 0 < T := by linarith
  have hQpos : 0 < Q := by
    have h : (0 : ℝ) < P * T * Real.exp 4 := by positivity
    linarith
  have hr1 : (1 : ℝ) < 7/5 := by norm_num
  have hexp4 : (5 : ℝ) ≤ Real.exp 4 := by
    have h := Real.add_one_le_exp 4; linarith
  have hlogr_lt2 : Real.log (7/5 : ℝ) < 2 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 7/5 by norm_num)
    linarith
  -- the two minimisers
  have hex_j0 : ∃ j : ℕ, T ≤ P * (7/5)^j := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (T / P) hr1
    refine ⟨n, ?_⟩
    have h := mul_lt_mul_of_pos_right hn hP
    rw [div_mul_cancel₀ T (ne_of_gt hP)] at h
    nlinarith [h]
  have hex_N : ∃ j : ℕ, Q * (5/7) < P * (7/5)^j := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (Q * (5/7) / P) hr1
    refine ⟨n, ?_⟩
    have h := mul_lt_mul_of_pos_right hn hP
    rw [div_mul_cancel₀ (Q * (5/7)) (ne_of_gt hP)] at h
    nlinarith [h]
  let j₀ : ℕ := Nat.find hex_j0
  let N : ℕ := Nat.find hex_N
  have hj0 : T ≤ P * (7/5)^j₀ := Nat.find_spec hex_j0
  have hN : Q * (5/7) < P * (7/5)^N := Nat.find_spec hex_N
  -- key step: `j₀ < N`
  have hle_j0 : P * (7/5)^j₀ ≤ Q * (5/7) := by
    have hPe4 : P * (7/5)^j₀ ≤ P * T * Real.exp 4 * (5/7) := by
      rcases Nat.eq_zero_or_pos j₀ with h0 | hpos
      · rw [h0]; simp only [pow_zero, mul_one]
        have hT5 : (5 : ℝ) ≤ T * Real.exp 4 := by
          have := mul_le_mul hT hexp4 (by norm_num : (0:ℝ) ≤ 5) (le_of_lt hTpos)
          linarith [this]
        have h1 : (1 : ℝ) ≤ T * Real.exp 4 * (5/7) := by nlinarith [hT5]
        calc P = P * 1 := by ring
          _ ≤ P * (T * Real.exp 4 * (5/7)) := mul_le_mul_of_nonneg_left h1 (le_of_lt hP)
          _ = P * T * Real.exp 4 * (5/7) := by ring
      · have hmin : ¬ (T ≤ P * (7/5)^(j₀ - 1)) :=
          Nat.find_min hex_j0 (show j₀ - 1 < j₀ by omega)
        have hlt : P * (7/5)^(j₀ - 1) < T := lt_of_not_ge hmin
        have heq : j₀ = (j₀ - 1) + 1 := by omega
        rw [heq, pow_succ]
        have hcoef : (7/5 : ℝ) ≤ P * Real.exp 4 * (5/7) := by
          have hP5 : (10 : ℝ) ≤ P * Real.exp 4 := by
            have := mul_le_mul h2P hexp4 (by norm_num : (0:ℝ) ≤ 5) (by linarith : (0:ℝ) ≤ P)
            linarith [this]
          nlinarith [hP5]
        have hle2 : T * (7/5) ≤ P * T * Real.exp 4 * (5/7) := by
          calc T * (7/5) ≤ T * (P * Real.exp 4 * (5/7)) :=
                mul_le_mul_of_nonneg_left hcoef (le_of_lt hTpos)
            _ = P * T * Real.exp 4 * (5/7) := by ring
        nlinarith [hlt, hle2]
    have h2 : P * T * Real.exp 4 * (5/7) ≤ Q * (5/7) := by
      have := mul_le_mul_of_nonneg_right hQ4 (show (0 : ℝ) ≤ 5/7 by norm_num)
      linarith [this]
    linarith [hPe4, h2]
  have hj0ltN : j₀ < N := by
    have h1 : P * (7/5)^j₀ < P * (7/5)^N := lt_of_le_of_lt hle_j0 hN
    have h2 : (7/5:ℝ)^j₀ < (7/5:ℝ)^N := (mul_lt_mul_iff_of_pos_left hP).mp h1
    exact (pow_lt_pow_iff_right₀ hr1).mp h2
  have hNQ : P * (7/5)^N ≤ Q := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · rw [h0]; simp only [pow_zero, mul_one]
      nlinarith [hQ4, hT, hexp4, hP]
    · have hmin : ¬ (Q * (5/7) < P * (7/5)^(N - 1)) :=
        Nat.find_min hex_N (show N - 1 < N by omega)
      have hle : P * (7/5)^(N - 1) ≤ Q * (5/7) := le_of_not_gt hmin
      have heq : N = (N - 1) + 1 := by omega
      rw [heq, pow_succ]
      nlinarith [hle]
  refine ⟨N, j₀, Nat.succ_le_of_lt hj0ltN, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [Finset.mem_Icc] at hj
    have hmono : P * (7/5)^j₀ ≤ P * (7/5)^j :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (le_of_lt hr1) hj.1) (le_of_lt hP)
    linarith [hj0, hmono]
  · intro j hj
    have h1 : (1 : ℝ) ≤ (7/5)^j := one_le_pow₀ (le_of_lt hr1)
    nlinarith [hP, h1]
  · intro j hj
    rw [Finset.mem_Icc] at hj
    have hmono : P * (7/5)^(j + 1) ≤ P * (7/5)^N :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (le_of_lt hr1) (by omega)) (le_of_lt hP)
    linarith [hmono, hNQ]
  · -- the logarithmic ratio
    have hden_pos : 0 < Real.log (P * (7/5)^j₀) := by
      apply Real.log_pos
      have h1 : (1 : ℝ) ≤ (7/5)^j₀ := one_le_pow₀ (le_of_lt hr1)
      nlinarith [h2P, h1]
    have hden_le : Real.log (P * (7/5)^j₀) ≤ Real.log P + Real.log T + 2 := by
      rcases Nat.eq_zero_or_pos j₀ with h0 | hpos
      · rw [h0]; simp only [pow_zero, mul_one]
        have := Real.log_nonneg hT
        linarith
      · have hmin : ¬ (T ≤ P * (7/5)^(j₀ - 1)) :=
          Nat.find_min hex_j0 (show j₀ - 1 < j₀ by omega)
        have hlt : P * (7/5)^(j₀ - 1) < T := lt_of_not_ge hmin
        have heq : j₀ = (j₀ - 1) + 1 := by omega
        have hltT : P * (7/5)^j₀ < T * (7/5) := by
          rw [heq, pow_succ]; nlinarith [hlt]
        have hloglt : Real.log (P * (7/5)^j₀) < Real.log (T * (7/5)) :=
          Real.log_lt_log (mul_pos hP (pow_pos (by norm_num) j₀)) hltT
        have hlogT : Real.log (T * (7/5)) = Real.log T + Real.log (7/5) :=
          Real.log_mul (ne_of_gt hTpos) (by norm_num)
        have hlogP : 0 ≤ Real.log P := Real.log_nonneg (by linarith)
        have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hT
        linarith [hloglt, hlogT, hlogr_lt2, hlogP, hlogT0]
    have hnum_lt : Real.log Q - Real.log (7/5) < Real.log (P * (7/5)^N) := by
      have h2 : Real.log (Q * (5/7)) < Real.log (P * (7/5)^N) :=
        Real.log_lt_log (mul_pos hQpos (by norm_num)) hN
      have h3 : Real.log (Q * (5/7)) = Real.log Q + Real.log ((5:ℝ)/7) :=
        Real.log_mul (ne_of_gt hQpos) (by norm_num)
      have h4 : Real.log ((5:ℝ)/7) = -Real.log (7/5) := by
        rw [show (5:ℝ)/7 = (7/5)⁻¹ by norm_num, Real.log_inv]
      linarith [h2, h3, h4]
    have hS_pos : 0 < Real.log P + Real.log T + 2 := by
      have h1 : 0 ≤ Real.log P := Real.log_nonneg (by linarith)
      have h2 : 0 ≤ Real.log T := Real.log_nonneg hT
      linarith
    have hA_ge : Real.exp (4*K + CM + 1) * (Real.log P + Real.log T + 2)
        ≤ Real.log Q - Real.log (7/5) := by linarith [hlogQ, hlogr_lt2]
    have hA_nonneg : 0 ≤ Real.log Q - Real.log (7/5) :=
      le_trans (mul_nonneg (Real.exp_pos (4*K+CM+1)).le (le_of_lt hS_pos)) hA_ge
    have hstep1 : Real.exp (4*K + CM + 1)
        ≤ (Real.log Q - Real.log (7/5)) / (Real.log P + Real.log T + 2) := by
      rw [le_div_iff₀ hS_pos]
      linarith [hA_ge]
    have hstep2 : (Real.log Q - Real.log (7/5)) / (Real.log P + Real.log T + 2)
        ≤ (Real.log Q - Real.log (7/5)) / Real.log (P * (7/5)^j₀) :=
      div_le_div_of_nonneg_left hA_nonneg hden_pos hden_le
    have hstep3 : (Real.log Q - Real.log (7/5)) / Real.log (P * (7/5)^j₀)
        < Real.log (P * (7/5)^N) / Real.log (P * (7/5)^j₀) :=
      div_lt_div_of_pos_right hnum_lt hden_pos
    have hexp_lt : Real.exp (4*K + CM) < Real.exp (4*K + CM + 1) := by
      rw [Real.exp_lt_exp]; linarith
    linarith [hstep1, hstep2, hstep3, hexp_lt]

end Work.BMF.SD
