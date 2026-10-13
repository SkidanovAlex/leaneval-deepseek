import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.H2.LinfQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine.ZTracesAux

theorem slot_sin_le_HkIntegrand_gen {α : ℝ} {f : ℝ → ℝ → ℝ} {m : ℕ}
    (b a : ℕ) (hab : a + 1 + b ≤ m) (s : ℝ) {σ : ℝ}
    (hσ : σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.mixed b (a + 1) f s σ * Work.Spaces.w s) ^ 2
      * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) ≤ Work.Spaces.HkIntegrand α m f s σ := by
  -- `sin(2σ) > 0` on the open angular interval.
  have hS : 0 < Real.sin (2 * σ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ.1]) (by linarith [hσ.2, Real.pi_pos])
  -- The `(i,j) = (a+1,b)` slot of the mixed sum of `HkIntegrand` dominates.
  have hbase : (Work.Spaces.mixed b (a + 1) f s σ * Work.Spaces.Wt α s σ) ^ 2
      ≤ Work.Spaces.HkIntegrand α m f s σ :=
    Work.Spaces.sq_le_HkIntegrand_mixed α m f s σ (a + 1) b (by omega) hab
  -- `(sin(2σ)^{-γ/2})² = sin(2σ)^{-γ}`.
  have hP : (Real.sin (2 * σ) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = Real.sin (2 * σ) ^ (-(Work.Spaces.gam α)) := by
    rw [sq, ← Real.rpow_add hS]
    congr 1
    ring
  -- The left-hand side is exactly that slot.
  have hkey : (Work.Spaces.mixed b (a + 1) f s σ * Work.Spaces.w s) ^ 2
        * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
      = (Work.Spaces.mixed b (a + 1) f s σ * Work.Spaces.Wt α s σ) ^ 2 := by
    rw [Work.Spaces.Wt, Work.Spaces.wTheta]
    simp only [mul_pow]
    rw [hP]
    ring
  rw [hkey]
  exact hbase

end Work.FTS.EpsEngine.ZTracesAux
