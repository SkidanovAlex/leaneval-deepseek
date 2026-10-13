import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.TT.SliceCoercDefs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.sliceLimitLeftExists

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.WeakMoment.Open

/-- **Removing the weight `sEta = sin(2θ)^{-η}` from an integrability hypothesis on `D2 u`.**

`Iθ = [0, π/2]` differs from the open interval `(0, π/2)` by the two endpoints, a null set, and
on `(0, π/2)` the weight satisfies `1 ≤ sEta` (`0 < sin(2θ) ≤ 1` and the exponent `-η` is
nonpositive).  Hence `(u'')² ≤ (u'')²·sEta` there, and the two transfers

* `sliceLim_integrableOn_sq_of_integrableOn_mul_sEta` (`(u'')²·sEta ∈ L¹ ⟹ (u'')² ∈ L¹`), and
* `sliceLim_integrableOn_abs_of_integrableOn_sq` (`(u'')² ∈ L¹ ⟹ |u''| ∈ L¹`),

proved in `Submission.Work.FTS.EllipticEst.sliceLimitLeftExists` for the open interval, together
with `volume.restrict Iθ = volume.restrict (Ioo 0 (π/2))` give the two claims. -/
theorem IntegrableD2OfWeighted {u : ℝ → ℝ}
    (h : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.FTS.EllipticEst.TT.D2 u θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.FTS.EllipticEst.TT.D2 u θ) ^ 2) Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => |Work.FTS.EllipticEst.TT.D2 u θ|) Work.Spaces.Iθ := by
  -- `Iθ = [0, π/2]` and `(0, π/2)` carry the same measure (the two endpoints are null).
  have hms : (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ
      = (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
          (Set.Ioo 0 (Real.pi / 2)) := by
    rw [Work.Spaces.Iθ]
    exact (MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm
  -- both transfers are available on the open interval
  have hsq := Work.FTS.EllipticEst.sliceLim_integrableOn_sq_of_integrableOn_mul_sEta u h
  have habs := Work.FTS.EllipticEst.sliceLim_integrableOn_abs_of_integrableOn_sq u hsq
  constructor
  · change MeasureTheory.Integrable (fun θ : ℝ => (deriv (fun t : ℝ => deriv u t) θ) ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)
    rw [hms]
    exact hsq
  · change MeasureTheory.Integrable (fun θ : ℝ => |deriv (fun t : ℝ => deriv u t) θ|)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)
    rw [hms]
    exact habs

end Work.FTS.EllipticEst.WeakMoment.Open
