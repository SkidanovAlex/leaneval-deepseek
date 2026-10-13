import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.HkSqAux.Defs
import Submission.Work.FTS.StrongEps.HkSqAux.lintegral_exp_subst_gen
import Submission.Work.FTS.StrongEps.HkSqAux.lintegral_arctan_exp_subst_gen
import Submission.Work.FTS.StrongEps.HkSqAux.lintegral_quad_log_subst

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsSrc

theorem lintegral_logSubst (U : ℝ → ℝ → ENNReal) :
    (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, U z θ)
      = ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ)
          * U (Real.exp s) (Real.arctan (Real.exp ζ)) := by
  -- The closed intervals `Iz = [0,∞)`, `Iθ = [0,π/2]` differ from the open ones only by
  -- null sets, so the iterated integral may be taken over the open quadrant `(0,∞) × (0,π/2)`,
  -- and `HkSqAux.lintegral_quad_log_subst` is exactly the log-coordinate substitution there.
  have hIθ : (fun z : ℝ => ∫⁻ θ in Work.Spaces.Iθ, U z θ)
      = fun z : ℝ => ∫⁻ θ in Set.Ioo 0 (Real.pi / 2), U z θ := by
    funext z
    exact (MeasureTheory.setLIntegral_congr
      (f := fun θ : ℝ => U z θ) (MeasureTheory.Ioo_ae_eq_Icc)).symm
  rw [Work.Spaces.Iz, hIθ]
  rw [(MeasureTheory.setLIntegral_congr
    (f := fun z : ℝ => ∫⁻ θ in Set.Ioo 0 (Real.pi / 2), U z θ)
    (MeasureTheory.Ioi_ae_eq_Ici)).symm]
  exact Work.FTS.StrongEps.HkSqAux.lintegral_quad_log_subst U

end Work.FTS.StrongEps.EpsSrc
