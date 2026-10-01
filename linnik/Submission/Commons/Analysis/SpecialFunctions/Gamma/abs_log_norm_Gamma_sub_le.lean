import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gammaR_log_norm_sub_le_im

open Complex
set_option autoImplicit false
noncomputable section

namespace Commons.Analysis.SpecialFunctions.Gamma

theorem abs_log_norm_Gamma_sub_le (u₁ u₂ v : ℝ) (h1 : (1 : ℝ) / 2 ≤ u₁) (h12 : u₁ ≤ u₂) (h2 : u₂ ≤ 8) : |Real.log ‖Complex.Gamma ((u₂ : ℂ) + (v : ℂ) * I)‖ - Real.log ‖Complex.Gamma ((u₁ : ℂ) + (v : ℂ) * I)‖| ≤ (u₂ - u₁) * (Real.log (2 + |v|) + 2) := by
  have h1' : u₁ ≤ 8 := le_trans h12 h2
  have h2' : (1 : ℝ) / 2 ≤ u₂ := le_trans h1 h12
  have h := log_norm_Gamma_sub_abs_le u₁ u₂ v h1 h1' h2' h2
  rw [abs_sub_comm, abs_of_nonpos (by linarith : u₁ - u₂ ≤ 0), neg_sub] at h
  exact h

end Commons.Analysis.SpecialFunctions.Gamma
