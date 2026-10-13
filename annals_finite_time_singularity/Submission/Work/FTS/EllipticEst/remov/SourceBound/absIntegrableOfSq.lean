import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real

namespace Work.FTS.EllipticEst.remov.SourceBound

/-- On a finite-measure set, `L²` integrability implies `L¹` integrability: here we use the
elementary pointwise bound `|g| ≤ (g² + 1)/2` (the AM–GM inequality), so that `|g|` is
dominated by the integrable function `(g² + 1)/2`.  The two measures involved,
`volume.restrict (Ioo 0 (π/2))` and `volume.restrict Iθ = volume.restrict (Icc 0 (π/2))`,
differ only by the null set `{0, π/2}`. -/
theorem absIntegrableOfSq {g : ℝ → ℝ}
    (hgm : MeasureTheory.AEStronglyMeasurable g (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))))
    (h : MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => |g θ|) (Set.Ioo 0 (Real.pi / 2)) := by
  -- `Ioo 0 (π/2)` and `Iθ = Icc 0 (π/2)` differ by a null set, so they carry the same
  -- restricted Lebesgue measure.
  have hrestrict : MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))
      = MeasureTheory.volume.restrict (Set.Icc 0 (Real.pi / 2)) :=
    Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
  have hsq : MeasureTheory.Integrable (fun θ => (g θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
    rw [hrestrict]
    exact h
  -- The constant `1` is integrable on a set of finite measure.
  have h1 : MeasureTheory.Integrable (fun _ : ℝ => (1 : ℝ))
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
    have hne : (MeasureTheory.volume (Set.Ioo 0 (Real.pi / 2)) : ENNReal) ≠ ⊤ := by
      rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
    exact MeasureTheory.integrableOn_const hne
  have hbound : MeasureTheory.Integrable (fun θ => (1 / 2 : ℝ) * ((g θ) ^ 2 + 1))
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    (hsq.add h1).const_mul (1 / 2)
  refine MeasureTheory.Integrable.mono' hbound (by simpa using hgm.norm) ?_
  filter_upwards with θ
  have hnorm : ‖|g θ|‖ = |g θ| := by simp
  rw [hnorm]
  nlinarith [sq_nonneg (|g θ| - 1), sq_abs (g θ)]

end Work.FTS.EllipticEst.remov.SourceBound
