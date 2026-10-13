import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.L12JepsAux

theorem measurable_integral_sub_conv {K G : ℝ × ℝ → ℝ} (hK : Measurable K) (hG : Measurable G) (a : ℝ) :
    Measurable (fun ζ : ℝ => ∫ p : ℝ × ℝ, K p * G (a - p.1, ζ - p.2)) := by
  have h : Measurable (Function.uncurry
      (fun (ζ : ℝ) (p : ℝ × ℝ) => K p * G (a - p.1, ζ - p.2))) := by
    apply Measurable.mul
    · exact hK.comp measurable_snd
    · apply hG.comp
      fun_prop
  exact h.stronglyMeasurable.integral_prod_right.measurable

end Work.FTS.StrongEps.EpsE4Thr.L12JepsAux
