import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory

namespace Work.BoseBogFS

/-- Comparison of the two singular weights `‖p‖⁻³` (cut off at radius `L`) and `‖p‖⁻²`:
for a nonnegative `f`, the integral of `f p / ‖p‖ ^ 3` over the exterior of the ball of
radius `L` is at most `A` times the full integral of `f p / ‖p‖ ^ 2`, as soon as
`A⁻¹ ≤ L` (so that `‖p‖ ≥ L` forces `‖p‖⁻¹ ≤ A`). -/
theorem setIntegral_inv_cube_le {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ∀ p, 0 ≤ f p)
    {A L C : ℝ} (hA : 0 < A) (hL : A⁻¹ ≤ L)
    (hint : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => f p / ‖p‖ ^ 2))
    (hcou : (∫ p : EuclideanSpace ℝ (Fin 3), f p / ‖p‖ ^ 2) ≤ C) :
    (∫ p in {p : EuclideanSpace ℝ (Fin 3) | L < ‖p‖}, f p / ‖p‖ ^ 3) ≤ A * C := by
  have hLpos : 0 < L := lt_of_lt_of_le (inv_pos.mpr hA) hL
  -- rewrite `f p / ‖p‖ ^ 3` as `(f p / ‖p‖ ^ 2) * ‖p‖⁻¹`
  have hid : ∀ p : EuclideanSpace ℝ (Fin 3),
      f p / ‖p‖ ^ 3 = (f p / ‖p‖ ^ 2) * (‖p‖)⁻¹ := by
    intro p
    rw [div_eq_mul_inv, div_eq_mul_inv, pow_succ, mul_inv_rev]; ring
  -- the pointwise bound on the exterior of the ball
  have hbound : ∀ p, L < ‖p‖ → f p / ‖p‖ ^ 3 ≤ A * (f p / ‖p‖ ^ 2) := by
    intro p hp
    have hnp : 0 < ‖p‖ := lt_trans hLpos hp
    have hinv : (‖p‖)⁻¹ ≤ A := ((inv_lt_comm₀ hnp hA).mpr (lt_of_le_of_lt hL hp)).le
    rw [hid p]
    calc (f p / ‖p‖ ^ 2) * (‖p‖)⁻¹ ≤ (f p / ‖p‖ ^ 2) * A :=
          mul_le_mul_of_nonneg_left hinv (div_nonneg (hf p) (sq_nonneg _))
      _ = A * (f p / ‖p‖ ^ 2) := by ring
  set s : Set (EuclideanSpace ℝ (Fin 3)) := {p | L < ‖p‖} with hsdef
  have hs_meas : MeasurableSet s := (isOpen_lt continuous_const continuous_norm).measurableSet
  -- measurability of the integrand
  have hgm : AEStronglyMeasurable (fun p : EuclideanSpace ℝ (Fin 3) => f p / ‖p‖ ^ 3) volume := by
    have h1 : AEMeasurable (fun p : EuclideanSpace ℝ (Fin 3) => f p / ‖p‖ ^ 2) volume :=
      hint.aestronglyMeasurable.aemeasurable
    have h2 : AEMeasurable (fun p : EuclideanSpace ℝ (Fin 3) => (‖p‖)⁻¹) volume :=
      (continuous_norm.measurable.inv).aemeasurable
    have h3 : AEMeasurable
        (fun p : EuclideanSpace ℝ (Fin 3) => (f p / ‖p‖ ^ 2) * (‖p‖)⁻¹) volume :=
      h1.mul h2
    refine (h3.congr ?_).aestronglyMeasurable
    filter_upwards with p
    exact (hid p).symm
  -- integrability of the integrand on the exterior
  have hgi : Integrable (fun p : EuclideanSpace ℝ (Fin 3) => f p / ‖p‖ ^ 3) (volume.restrict s) := by
    refine Integrable.mono' ((hint.const_mul A).restrict) hgm.restrict ?_
    filter_upwards [self_mem_ae_restrict hs_meas] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hf p) (by positivity))]
    exact hbound p hp
  calc (∫ p in s, f p / ‖p‖ ^ 3)
      ≤ (∫ p in s, A * (f p / ‖p‖ ^ 2)) := by
        refine integral_mono_ae hgi ((hint.const_mul A).restrict) ?_
        filter_upwards [self_mem_ae_restrict hs_meas] with p hp
        exact hbound p hp
    _ = A * (∫ p in s, f p / ‖p‖ ^ 2) := integral_const_mul A _
    _ ≤ A * (∫ p, f p / ‖p‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hA.le
        refine setIntegral_le_integral hint ?_
        filter_upwards with p
        exact div_nonneg (hf p) (sq_nonneg _)
    _ ≤ A * C := mul_le_mul_of_nonneg_left hcou hA.le

end Work.BoseBogFS
