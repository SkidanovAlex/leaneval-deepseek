import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

theorem integral_sq_eq_of_difference (n : ℕ) {c : ℝ → ℝ} {c_ : ℕ → ℝ → ℝ}
    (hcw : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 * (Work.Spaces.w t) ^ 2) (Set.Ioi 0))
    (hint : MeasureTheory.IntegrableOn (fun t : ℝ => (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2) (Set.Ioi 0))
    (hcross : MeasureTheory.IntegrableOn (fun t : ℝ => (c_ n t - c t) * c t * (Work.Spaces.w t) ^ 2) (Set.Ioi 0)) :
    ∫ t in Set.Ioi 0, (c_ n t) ^ 2 * (Work.Spaces.w t) ^ 2
      = (∫ t in Set.Ioi 0, (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2)
        + 2 * (∫ t in Set.Ioi 0, (c_ n t - c t) * c t * (Work.Spaces.w t) ^ 2)
        + ∫ t in Set.Ioi 0, (c t) ^ 2 * (Work.Spaces.w t) ^ 2 := by
  -- Pointwise, `(c_ n t)² = (c_ n t - c t)² + 2 (c_ n t - c t) c t + (c t)²`.
  have hcongr : (fun t : ℝ => (c_ n t) ^ 2 * (Work.Spaces.w t) ^ 2)
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)]
        (fun t : ℝ => ((c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2)
          + (2 * ((c_ n t - c t) * c t * (Work.Spaces.w t) ^ 2)
            + (c t) ^ 2 * (Work.Spaces.w t) ^ 2)) :=
    Filter.Eventually.of_forall (fun t => by ring)
  rw [MeasureTheory.integral_congr_ae hcongr]
  have h23 : MeasureTheory.IntegrableOn
      (fun t : ℝ => 2 * ((c_ n t - c t) * c t * (Work.Spaces.w t) ^ 2)
        + (c t) ^ 2 * (Work.Spaces.w t) ^ 2) (Set.Ioi 0) := (hcross.const_mul 2).add hcw
  rw [MeasureTheory.integral_add hint h23]
  rw [MeasureTheory.integral_add (hcross.const_mul 2) hcw]
  rw [MeasureTheory.integral_const_mul]
  ring

end Work.FTS.PhiStar.Honesty
