import Mathlib

namespace Work.EKLComp

theorem critical_time (ε₀ d : ℝ) (hε₀ : 0 < ε₀) (hd : 0 < d) (hdε : d ≤ ε₀) (N : ℕ) (hN : 2 ≤ N)
    (hsep : ε₀ * Real.exp (-(3 * ((N : ℝ) - 1))) ≤ d) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ N - 1 ∧ ε₀ ≤ Real.exp (3 * (n : ℝ)) * d ∧
      Real.exp (3 * (n : ℝ)) * d ≤ Real.exp 3 * ε₀ := by
  classical
  have hN1 : 1 ≤ N := by omega
  have hcastN : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub hN1]; norm_num
  -- There is a natural number n with ε₀ ≤ exp(3n) * d: namely n = N-1.
  have hexN : ε₀ ≤ Real.exp (3 * ((N - 1 : ℕ) : ℝ)) * d := by
    have hmul : ε₀ * Real.exp (-(3 * ((N : ℝ) - 1))) * Real.exp (3 * ((N : ℝ) - 1))
        ≤ d * Real.exp (3 * ((N : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_right hsep (le_of_lt (Real.exp_pos _))
    have he : Real.exp (-(3 * ((N : ℝ) - 1))) * Real.exp (3 * ((N : ℝ) - 1)) = 1 := by
      rw [Real.exp_neg, inv_mul_cancel₀ (ne_of_gt (Real.exp_pos _))]
    rw [hcastN]
    calc ε₀ = ε₀ * (Real.exp (-(3 * ((N : ℝ) - 1))) * Real.exp (3 * ((N : ℝ) - 1))) := by
            rw [he, mul_one]
      _ = ε₀ * Real.exp (-(3 * ((N : ℝ) - 1))) * Real.exp (3 * ((N : ℝ) - 1)) := by ring
      _ ≤ d * Real.exp (3 * ((N : ℝ) - 1)) := hmul
      _ = Real.exp (3 * ((N : ℝ) - 1)) * d := by ring
  have hex : ∃ n : ℕ, ε₀ ≤ Real.exp (3 * (n : ℝ)) * d := ⟨N - 1, hexN⟩
  -- take the least such n
  set m := Nat.find hex with hmdef
  have hspec : ε₀ ≤ Real.exp (3 * (m : ℝ)) * d := by
    rw [hmdef]; exact Nat.find_spec hex
  have hmle : m ≤ N - 1 := by
    rw [hmdef]; exact Nat.find_le hexN
  by_cases h0 : m = 0
  · -- then d = ε₀, and n = 1 works
    have hdge : ε₀ ≤ d := by
      have h := hspec
      rw [h0] at h
      simpa using h
    have hdeq : d = ε₀ := le_antisymm hdε hdge
    refine ⟨1, le_refl 1, by omega, ?_, ?_⟩
    · have : Real.exp (3 * ((1 : ℕ) : ℝ)) = Real.exp 3 := by norm_num
      rw [hdeq, this]
      calc ε₀ = 1 * ε₀ := by ring
        _ ≤ Real.exp 3 * ε₀ :=
            mul_le_mul_of_nonneg_right (Real.one_le_exp (by norm_num)) hε₀.le
    · rw [hdeq]; norm_num
  · -- m ≥ 1: m is the minimal one, so exp(3(m-1))*d < ε₀
    have hm1 : 1 ≤ m := by omega
    refine ⟨m, hm1, hmle, hspec, ?_⟩
    have hcastm : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub hm1]; norm_num
    have hlt : Real.exp (3 * ((m - 1 : ℕ) : ℝ)) * d < ε₀ := by
      have hltm : m - 1 < Nat.find hex := by rw [← hmdef]; omega
      have hnot : ¬ (ε₀ ≤ Real.exp (3 * ((m - 1 : ℕ) : ℝ)) * d) := Nat.find_min hex hltm
      exact not_le.mp hnot
    have hexp : Real.exp (3 * (m : ℝ)) = Real.exp 3 * Real.exp (3 * ((m - 1 : ℕ) : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      rw [hcastm]; ring
    calc Real.exp (3 * (m : ℝ)) * d
        = Real.exp 3 * (Real.exp (3 * ((m - 1 : ℕ) : ℝ)) * d) := by rw [hexp]; ring
      _ ≤ Real.exp 3 * ε₀ := mul_le_mul_of_nonneg_left hlt.le (le_of_lt (Real.exp_pos 3))

end Work.EKLComp
