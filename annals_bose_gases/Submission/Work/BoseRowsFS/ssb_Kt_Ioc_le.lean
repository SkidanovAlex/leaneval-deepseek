import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseRowsFS.integral_Kt_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowsFS

open MeasureTheory Set

/-- The time-truncated heat kernel is dominated by its total time-integral: for `z ≠ 0`,

  `∫_{0 < s ≤ 1} Kt s z ds ≤ ∫_{s>0} Kt s z ds = 1/(4π‖z‖)`.

The point is that `s ↦ Kt s z` is nonnegative on `(0,∞)` and that the untruncated
`t`-integral is the Newtonian kernel, by `integral_Kt_eq`.  Integrability over `(0,∞)`
does not need a separate analytic estimate: by `integral_undef` it is forced by the fact
that the integral there is `1/(4π‖z‖) ≠ 0`. -/
theorem ssb_Kt_Ioc_le {z : EuclideanSpace ℝ (Fin 3)} (hz : z ≠ 0) :
    (∫ s in Set.Ioc (0 : ℝ) 1, Kt s z) ≤ 1 / (4 * Real.pi * ‖z‖) := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hInt : IntegrableOn (fun s : ℝ => Kt s z) (Set.Ioi (0 : ℝ)) := by
    by_contra h
    have h0 : (∫ s in Set.Ioi (0 : ℝ), Kt s z) = 0 := integral_undef h
    rw [integral_Kt_eq z hz] at h0
    have : 0 < 1 / (4 * Real.pi * ‖z‖) := by positivity
    linarith
  have hf : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] (fun s : ℝ => Kt s z) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact Kt_nonneg hs z
  have hst : Set.Ioc (0 : ℝ) 1 ≤ᵐ[volume] Set.Ioi (0 : ℝ) :=
    Filter.Eventually.of_forall (fun x hx => hx.1)
  have hle := setIntegral_mono_set hInt hf hst
  rwa [integral_Kt_eq z hz] at hle

end Work.BoseRowsFS
