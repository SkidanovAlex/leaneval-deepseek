import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace Commons.NumberTheory.Harmonic

open Real

theorem abs_harmonic_sub_log_sub_euler_le_inv (n : ℕ) (hn : 1 ≤ n) :
    |(harmonic n : ℝ) - Real.log (n : ℝ) - Real.eulerMascheroniConstant| ≤ 1 / (n : ℝ) := by
  have hn0 : n ≠ 0 := by omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  -- Lower bound: γ < H_{m+1} - log (m+1)
  have hpos : 0 < (harmonic (m + 1) : ℝ) - Real.log ((m + 1 : ℕ) : ℝ)
      - Real.eulerMascheroniConstant := by
    have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' (m + 1)
    rw [Real.eulerMascheroniSeq', if_neg (Nat.succ_ne_zero m)] at h
    linarith
  -- Upper bound: H_{m+1} - log (m+1) - γ < 1/(m+1)
  have hlt : (harmonic (m + 1) : ℝ) - Real.log ((m + 1 : ℕ) : ℝ)
      - Real.eulerMascheroniConstant < 1 / ((m + 1 : ℕ) : ℝ) := by
    have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant m
    rw [Real.eulerMascheroniSeq] at h
    have hlog : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    have hcast : (harmonic (m + 1) : ℝ) = (harmonic m : ℝ) + 1 / ((m + 1 : ℕ) : ℝ) := by
      rw [harmonic_succ]; push_cast; ring
    rw [hcast, hlog]
    linarith
  rw [abs_of_pos hpos]
  exact le_of_lt hlt

end Commons.NumberTheory.Harmonic