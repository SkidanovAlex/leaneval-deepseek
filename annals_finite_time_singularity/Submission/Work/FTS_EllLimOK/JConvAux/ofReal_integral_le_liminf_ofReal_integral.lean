import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `JConvAux.ofReal_integral_le_liminf_ofReal_integral` — the `θ`-Fatou step, in `ℝ≥0∞`

The real-valued `θ`-integrals of a sequence of nonnegative functions converge at least to the
integral of the a.e. limit, in the `ℝ≥0∞`-form used by `FTS_EllLimOK.HkSq_le_of_JConv`
(`∫⁻ liminf ≤ liminf ∫⁻`, `MeasureTheory.lintegral_liminf_le'`, plus the two conversions
`integral_eq_lintegral_of_nonneg_ae` and `ofReal_integral_eq_lintegral_ofReal` and
`ENNReal.ofReal_toReal_le`).

Note the Bochner-integral convention: if `A` is not integrable the left-hand side is `ofReal 0 = 0`
and the inequality is trivial, so no integrability of `A` is needed.
-/
open scoped Real Topology
open MeasureTheory Filter

namespace Work.FTS_EllLimOK.JConvAux

theorem ofReal_integral_le_liminf_ofReal_integral {a : ℕ → ℝ → ℝ} {A : ℝ → ℝ}
    (hint : ∀ n, MeasureTheory.IntegrableOn (a n) Work.Spaces.Iθ)
    (hnn : ∀ n θ, 0 ≤ a n θ)
    (hA : MeasureTheory.AEStronglyMeasurable A (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hAnn : ∀ θ, 0 ≤ A θ)
    (hlim : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Filter.Tendsto (fun n => a n θ) Filter.atTop (nhds (A θ))) :
    ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, A θ)
      ≤ Filter.liminf (fun n => ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, a n θ)) Filter.atTop := by
  have hfat := MeasureTheory.lintegral_liminf_le'
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ) (u := Filter.atTop)
    (f := fun n θ => ENNReal.ofReal (a n θ))
    (fun n => (hint n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
  have hEq : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ENNReal.ofReal (A θ)
        = Filter.liminf (fun n => ENNReal.ofReal (a n θ)) Filter.atTop := by
    filter_upwards [hlim] with θ hθ
    exact ((ENNReal.continuous_ofReal.tendsto (A θ)).comp hθ).liminf_eq.symm
  calc ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, A θ)
      = ENNReal.ofReal ((∫⁻ θ, ENNReal.ofReal (A θ)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)).toReal) := by
        rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
          (Filter.Eventually.of_forall hAnn) hA]
    _ ≤ (∫⁻ θ, ENNReal.ofReal (A θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
        ENNReal.ofReal_toReal_le
    _ = (∫⁻ θ, Filter.liminf (fun n => ENNReal.ofReal (a n θ)) Filter.atTop
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
        MeasureTheory.lintegral_congr_ae hEq
    _ ≤ Filter.liminf (fun n => ∫⁻ θ, ENNReal.ofReal (a n θ)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) Filter.atTop := hfat
    _ = Filter.liminf (fun n => ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, a n θ)) Filter.atTop := by
        refine Filter.liminf_congr (Filter.Eventually.of_forall fun n => ?_)
        exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hint n)
          (Filter.Eventually.of_forall (hnn n))).symm

end Work.FTS_EllLimOK.JConvAux
