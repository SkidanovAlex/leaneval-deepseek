import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.HighMass.OneBody
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB3.CS.Pieces

open MeasureTheory Filter

/-- The cut-off symbol `p ↦ |f(‖p‖/κ)|` is integrable: it is continuous and compactly
supported (it vanishes for `‖p‖ > 2κ`). -/
lemma integrable_abs_symbol {fc : Work.BoseBoxFix.LowCut} {κ : ℝ} (hκ : 0 < κ) :
    Integrable (fun p : EuclideanSpace ℝ (Fin 3) => |fc.f (‖p‖ / κ)|) :=
  (continuous_abs.comp (fc.smooth.continuous.comp (continuous_norm.div_const κ)))
    |>.integrable_of_hasCompactSupport
      (Work.BoseFixB3.HighMass.lowcut_symbol_hasCompactSupport (fc := fc) (κ := κ) hκ).abs

theorem integral_symbol_mul_le {fc : Work.BoseBoxFix.LowCut} {κ C : ℝ} (hκ : 0 < κ) (hC : 0 ≤ C)
    {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hg0 : ∀ p, 0 ≤ g p) (hgC : ∀ p, g p ≤ C) :
    ∫ p : EuclideanSpace ℝ (Fin 3), |fc.f (‖p‖ / κ)| * g p
      ≤ (∫ p : EuclideanSpace ℝ (Fin 3), |fc.f (‖p‖ / κ)|) * C := by
  have hφ_int : Integrable (fun p : EuclideanSpace ℝ (Fin 3) => |fc.f (‖p‖ / κ)|) :=
    integrable_abs_symbol hκ
  have hφC_int : Integrable (fun p : EuclideanSpace ℝ (Fin 3) => |fc.f (‖p‖ / κ)| * C) :=
    hφ_int.mul_const C
  calc ∫ p : EuclideanSpace ℝ (Fin 3), |fc.f (‖p‖ / κ)| * g p
      ≤ ∫ p : EuclideanSpace ℝ (Fin 3), |fc.f (‖p‖ / κ)| * C :=
        integral_mono_of_nonneg
          (Eventually.of_forall fun p => mul_nonneg (abs_nonneg _) (hg0 p))
          hφC_int
          (Eventually.of_forall fun p => mul_le_mul_of_nonneg_left (hgC p) (abs_nonneg _))
    _ = (∫ p : EuclideanSpace ℝ (Fin 3), |fc.f (‖p‖ / κ)|) * C := integral_mul_const C _

end Work.BoseFixB3.CS.Pieces
