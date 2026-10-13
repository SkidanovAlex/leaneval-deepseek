import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.Zpz

lemma radGreen_up_tail {c : ℝ → ℝ} {p : ℝ}
    (hdinf : MeasureTheory.IntegrableOn (fun t => t * deriv c t * t ^ (-p - 1)) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn (fun t => deriv c t * t ^ (-p)) (Set.Ioi 1) := by
  -- On `Ioi 1` the two functions coincide: `t * t ^ (-p - 1) = t ^ (1 + (-p - 1)) = t ^ (-p)`.
  refine hdinf.congr_fun ?_ measurableSet_Ioi
  intro t ht
  have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
  have h1 : t ^ (1 : ℝ) * t ^ (-p - 1) = t ^ (-p) := by
    rw [← Real.rpow_add ht0]
    norm_num
  show t * deriv c t * t ^ (-p - 1) = deriv c t * t ^ (-p)
  rw [← h1, Real.rpow_one]
  ring

end Work.FTS.ClassCHon.Zpz
