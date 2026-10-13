import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

/-- On a finite measure space, an a.e. strongly measurable function whose square is
integrable is integrable: the pointwise AM–GM bound `|f| ≤ (f² + 1)/2` exhibits `|f|` as
the sum of an integrable function and the integrable constant `1/2`. -/
lemma integrableOn_of_sq_integrableOn {f : ℝ → ℝ} {s : Set ℝ}
    (hm : MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume.restrict s))
    (hμ : MeasureTheory.volume s < ⊤)
    (h : MeasureTheory.IntegrableOn (fun x => f x ^ 2) s) :
    MeasureTheory.IntegrableOn f s := by
  have h1 : MeasureTheory.Integrable (fun _ : ℝ => (1 : ℝ))
      (MeasureTheory.volume.restrict s) :=
    MeasureTheory.integrable_const_iff.mpr
      (Or.inr ⟨by rw [MeasureTheory.Measure.restrict_apply_univ]; exact hμ⟩)
  have hg : MeasureTheory.Integrable (fun x => (f x ^ 2 + 1) / 2)
      (MeasureTheory.volume.restrict s) :=
    (h.add h1).div_const 2
  refine hg.mono' hm (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  nlinarith [sq_nonneg (|f x| - 1), sq_abs (f x)]

end Work.FTS.EllipticEst.H2W
