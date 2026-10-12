import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB3.CS.Pieces

open MeasureTheory Metric

theorem integrableOn_sq_mul_div (v ω : EuclideanSpace ℝ (Fin 3) → ℝ) {R q : ℝ} (hq : 0 < q)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.Integrable v)
    (hωm : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume)
    (hω0 : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))), 0 ≤ ω z)
    (hω1 : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))), ω z ≤ 1) :
    MeasureTheory.IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) => (ω z) ^ 2 * (v z / (v z + q)))
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) MeasureTheory.volume := by
  -- The integrand is a.e. strongly measurable: it is the product of `ω^2` and `v / (v + q)`.
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun z : EuclideanSpace ℝ (Fin 3) => (ω z) ^ 2 * (v z / (v z + q))) MeasureTheory.volume := by
    have hωa : AEMeasurable ω MeasureTheory.volume := hωm.aemeasurable
    have hva : AEMeasurable v MeasureTheory.volume := hv1.aemeasurable
    exact ((hωa.pow_const 2).mul (hva.div (hva.add aemeasurable_const))).aestronglyMeasurable
  -- On the ball the integrand is dominated by the constant `1` (a.e.).
  refine MeasureTheory.IntegrableOn.of_bound (measure_ball_lt_top (μ := MeasureTheory.volume))
    hmeas.restrict 1 ?_
  refine ae_mono Measure.restrict_le_self ?_
  filter_upwards [hω0, hω1] with z h0 h1
  have hvz : 0 ≤ v z := hv z
  have hden : 0 < v z + q := by linarith
  have hb0 : 0 ≤ v z / (v z + q) := div_nonneg hvz hden.le
  have hb1 : v z / (v z + q) ≤ 1 := (div_le_one hden).mpr (by linarith)
  have ha0 : 0 ≤ (ω z) ^ 2 := sq_nonneg _
  have ha1 : (ω z) ^ 2 ≤ 1 := by nlinarith
  have hg0 : 0 ≤ (ω z) ^ 2 * (v z / (v z + q)) := mul_nonneg ha0 hb0
  have hg1 : (ω z) ^ 2 * (v z / (v z + q)) ≤ 1 := by nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg hg0]
  exact hg1

end Work.BoseFixB3.CS.Pieces
