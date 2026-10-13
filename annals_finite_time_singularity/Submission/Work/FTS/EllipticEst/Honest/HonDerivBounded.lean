import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.sliceLimitLeftExists
import Submission.Work.FTS.EllipticEst.Honest.bdd_of_integrableOn_deriv
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

theorem HonDerivBounded (u : ℝ → ℝ)
    (hderiv2 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv u) (deriv (fun t : ℝ => deriv u t) θ) θ)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t : ℝ => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ) :
    ∃ M : ℝ, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv u θ| ≤ M := by
  have hq : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  -- `(u'')²` is integrable on `(0, π/2)`, because `sEta ≥ 1` there
  have hsq : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun t : ℝ => deriv u t) θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.sliceLim_integrableOn_sq_of_integrableOn_mul_sEta u hint
  -- hence `|u''|` is integrable there (`|x| ≤ x² + 1`)
  have habs : MeasureTheory.IntegrableOn
      (fun θ : ℝ => |deriv (fun t : ℝ => deriv u t) θ|) (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.sliceLim_integrableOn_abs_of_integrableOn_sq u hsq
  -- hence `u''` itself is integrable
  have hint' : MeasureTheory.IntegrableOn (deriv (fun t : ℝ => deriv u t))
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine MeasureTheory.Integrable.mono' habs
      (measurable_deriv (fun t : ℝ => deriv u t)).aestronglyMeasurable ?_
    filter_upwards with θ
    rw [Real.norm_eq_abs]
  obtain ⟨C, -, hC⟩ :=
    bdd_of_integrableOn_deriv (φ := deriv u) hq (fun θ hθ => hderiv2 θ hθ) hint'
  exact ⟨C, hC⟩

end Work.FTS.EllipticEst.Honest
