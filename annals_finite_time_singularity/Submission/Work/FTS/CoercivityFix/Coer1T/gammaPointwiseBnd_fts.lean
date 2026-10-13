import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Coercivity.Defs
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.Gam_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Coer1T

open scoped Real

/-- The angular coefficient `q(θ) = cos(2θ) - 1/3` of the paper's `Γ`-regularity lemma is
bounded by `4/3 ≤ 2` on the whole line. -/
lemma abs_qfun_le_two (θ : ℝ) : |Work.Spaces.qfun θ| ≤ 2 := by
  rw [Work.Spaces.qfun_apply]
  have h : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one (2 * θ)
  calc |Real.cos (2 * θ) - 1 / 3| ≤ |Real.cos (2 * θ)| + |(1 / 3 : ℝ)| := abs_sub _ _
    _ ≤ 1 + 1 / 3 := by
        have : |(1 / 3 : ℝ)| = 1 / 3 := abs_of_pos (by norm_num)
        linarith
    _ ≤ 2 := by norm_num

theorem gammaPointwiseBnd_fts (α : ℝ) (hα : 0 < α) :
    Work.Coercivity.GammaPointwiseBnd α := by
  intro θ hθ
  rcases hθ.1.eq_or_lt with h0 | h0
  · -- θ = 0: both sides vanish because `sin 0 = 0`
    subst h0
    rw [show (2 : ℝ) * 0 = 0 by ring, Real.sin_zero, zero_mul, abs_zero]
    have hG := (Work.Spaces.Gam_bounds α 0 hα hθ).1
    exact mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * α) hG
  rcases hθ.2.eq_or_lt with h1 | h1
  · -- θ = π/2: both sides vanish because `sin π = 0`
    subst h1
    rw [show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi, zero_mul, abs_zero]
    have hG := (Work.Spaces.Gam_bounds α (Real.pi / 2) hα hθ).1
    exact mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * α) hG
  · -- interior: `D_θΓ = α q Γ`
    have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨h0, h1⟩
    have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
    have hcos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩
    have hbase : 0 < Real.sin θ * Real.cos θ ^ 2 := by positivity
    have hGpos : 0 < Work.Spaces.Gam α θ := by
      rw [Work.Spaces.Gam]
      exact Real.rpow_pos_of_pos hbase _
    have hkey : Real.sin (2 * θ) * deriv (fun t => Work.Spaces.Gam α t) θ
        = α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ := by
      rw [← Work.Spaces.dthU_apply]
      exact Work.Spaces.dthU_Gam α θ hα hθ'
    rw [hkey, abs_mul, abs_mul, abs_of_pos hα, abs_of_pos hGpos]
    have hq := abs_qfun_le_two θ
    have h1' : α * |Work.Spaces.qfun θ| ≤ α * 2 :=
      mul_le_mul_of_nonneg_left hq (le_of_lt hα)
    calc α * |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ
        ≤ α * 2 * Work.Spaces.Gam α θ :=
          mul_le_mul_of_nonneg_right h1' (le_of_lt hGpos)
      _ = 2 * α * Work.Spaces.Gam α θ := by ring

end Work.FTS.CoercivityFix.Coer1T
