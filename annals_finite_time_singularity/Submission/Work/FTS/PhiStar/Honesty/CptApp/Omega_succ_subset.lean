import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CptApp

/-- The first level function `m ↦ 2 / m` of the shrinking region is antitone. -/
private theorem two_div_succ_le (m : ℕ) (hm : 1 ≤ m) :
    2 / ((m + 1 : ℕ) : ℝ) ≤ 2 / (m : ℝ) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hle : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by push_cast; linarith
  exact div_le_div_of_nonneg_left (by norm_num) hmR hle

theorem Omega_succ_subset {m : ℕ} (hm : 1 ≤ m) :
    Work.FTS.PhiStar.Honesty.CptApp.Omega (m + 1) ⊆
      Work.FTS.PhiStar.Honesty.CptApp.Omega m := by
  intro p hp
  simp only [Omega, Set.mem_ofPred_eq] at hp ⊢
  have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  have hle : 2 / ((m + 1 : ℕ) : ℝ) ≤ 2 / (m : ℝ) := two_div_succ_le m hm
  rcases hp with h | h | h | h
  · exact Or.inl (lt_of_lt_of_le h hle)
  · exact Or.inr (Or.inl (by rw [hcast] at h; linarith))
  · exact Or.inr (Or.inr (Or.inl (lt_of_lt_of_le h hle)))
  · exact Or.inr (Or.inr (Or.inr (by linarith)))

end Work.FTS.PhiStar.Honesty.CptApp
