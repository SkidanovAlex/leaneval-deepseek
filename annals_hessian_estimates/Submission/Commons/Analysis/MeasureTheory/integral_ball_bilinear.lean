import Mathlib
import Submission.Commons.Analysis.MeasureTheory.polar_integral
import Submission.Commons.Analysis.MeasureTheory.integral_radial_mul_homogeneous

namespace Commons.Analysis.MeasureTheory

open Metric Set Filter Function
open _root_.MeasureTheory
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace

set_option linter.style.haveILetI false

/-- Integral of a bilinear form `M` over the Euclidean ball `ball 0 r ⊂ ℝ^n` in terms of its
integral over the unit sphere:

  `∫_{ball 0 r} M z z = (r^(n+2) / (n+2)) * ∫_{‖θ‖=1} M θ θ dθ`.

This is the polar-coordinate identity for the quadratic form `z ↦ M z z`, which is positively
homogeneous of degree `2`: on the sphere of radius `r` the form equals `r^2 M θ θ`, and the radial
weight `volumeIoiPow (n-1)` contributes the exponent `n - 1 + 2 = n + 1`, so the radial integral is
`∫_0^r t^(n+1) dt = r^(n+2)/(n+2)`.  The proof uses the commons polar-coordinate identity
`Commons.Analysis.MeasureTheory.polar_integral` and
`Commons.Analysis.MeasureTheory.integral_volumeIoiPow_eq_integral_Ioi_mul_pow`. -/
theorem integral_ball_bilinear {n : ℕ} (hn : 0 < n)
    (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r, M z z)
      = r ^ (n + 2) / ((n : ℝ) + 2) *
        (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, M θ θ
          ∂MeasureTheory.volume.toSphere) := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let E := EuclideanSpace ℝ (Fin n)
  have hdim : Module.finrank ℝ E = n := finrank_euclideanSpace_fin
  have hcont : Continuous (fun z : E => M z z) := by fun_prop
  set F : E → ℝ := fun z => (Metric.ball (0 : E) r).indicator (fun z => M z z) z with hFdef
  have hFint : Integrable F volume := by
    rw [hFdef]
    rw [integrable_indicator_iff measurableSet_ball]
    exact hcont.continuousOn.integrableOn_of_subset_isCompact (isCompact_closedBall 0 r)
      measurableSet_ball ball_subset_closedBall measure_ball_lt_top.ne
  -- `M (t • θ) (t • θ) = t^2 M θ θ` for the quadratic form
  have hMsmul : ∀ (t : ℝ) (θ : Metric.sphere (0:E) 1),
      M (t • (θ:E)) (t • (θ:E)) = t^2 * M θ θ := by
    intro t θ
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  have hmem : ∀ (t : Ioi (0:ℝ)) (θ : Metric.sphere (0:E) 1),
      (t.1 • (θ:E)) ∈ Metric.ball (0:E) r ↔ (t:ℝ) < r := by
    intro t θ
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
        abs_of_pos t.2, mem_sphere_zero_iff_norm.mp θ.2, mul_one]
  have hFpt : ∀ (t : Ioi (0:ℝ)) (θ : Metric.sphere (0:E) 1),
      F (t.1 • (θ:E)) = (if (t:ℝ) < r then (t:ℝ)^2 else 0) * M θ θ := by
    intro t θ
    change (Metric.ball (0:E) r).indicator (fun z => M z z) (t.1 • (θ:E)) =
      (if (t:ℝ) < r then (t:ℝ)^2 else 0) * M θ θ
    rw [Set.indicator_apply]
    rw [if_congr (hmem t θ) (hMsmul t.1 θ) rfl]
    by_cases h : (t:ℝ) < r
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, zero_mul]
  -- the inner (radial) integral factors out the constant `M θ θ`
  have hinner : ∀ θ : Metric.sphere (0:E) 1,
      ∫ t : Ioi (0:ℝ), F (t.1 • (θ:E)) ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1))
        = (∫ t : Ioi (0:ℝ), (if (t:ℝ) < r then (t:ℝ)^2 else 0)
            ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1))) * M θ θ := by
    intro θ
    rw [← integral_mul_const (M θ θ)
      (fun t : Ioi (0:ℝ) => (if (t:ℝ) < r then (t:ℝ)^2 else 0))]
    apply integral_congr_ae
    filter_upwards with t
    exact hFpt t θ
  -- value of the radial integral
  have hcval : (∫ t : Ioi (0:ℝ), (if (t:ℝ) < r then (t:ℝ)^2 else 0)
      ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1))) = r ^ (n + 2) / ((n:ℝ) + 2) := by
    rw [Commons.Analysis.MeasureTheory.integral_volumeIoiPow_eq_integral_Ioi_mul_pow
        (Module.finrank ℝ E - 1) (fun x => if x < r then x ^ 2 else 0)]
    rw [hdim]
    have hcongr : Set.EqOn (fun x : ℝ => x ^ (n-1) * (if x < r then x^2 else 0))
        (fun x : ℝ => (Set.Ioo (0:ℝ) r).indicator (fun x => x ^ (n+1)) x) (Set.Ioi 0) := by
      intro x hx
      change x ^ (n-1) * (if x < r then x^2 else 0) =
        (Set.Ioo (0:ℝ) r).indicator (fun x => x ^ (n+1)) x
      rw [mem_Ioi] at hx
      by_cases hxr : x < r
      · rw [if_pos hxr, Set.indicator_of_mem (show x ∈ Set.Ioo (0:ℝ) r from ⟨hx, hxr⟩)]
        rw [← pow_add]
        congr 1
        omega
      · rw [if_neg hxr, mul_zero, Set.indicator_of_notMem (fun hh => hxr hh.2)]
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr]
    rw [setIntegral_indicator measurableSet_Ioo]
    rw [inter_eq_right.mpr Ioo_subset_Ioi_self]
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le]
    rw [integral_pow]
    have hpow : r ^ ((n+1) + 1) = r ^ (n + 2) := by congr 1
    have hzero : (0:ℝ) ^ ((n+1) + 1) = 0 := zero_pow (by omega)
    have hden : (((n+1 : ℕ) : ℝ) + 1) = (n:ℝ) + 2 := by push_cast; ring
    rw [hpow, hzero, sub_zero, hden]
  calc (∫ z in Metric.ball (0:E) r, M z z)
      = ∫ z, F z := by
        rw [hFdef]
        simp only
        exact (integral_indicator measurableSet_ball).symm
    _ = ∫ θ : Metric.sphere (0:E) 1, ∫ t : Ioi (0:ℝ),
          F (t.1 • (θ:E)) ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1)) ∂(volume.toSphere) :=
          Commons.Analysis.MeasureTheory.polar_integral E F hFint
    _ = ∫ θ : Metric.sphere (0:E) 1,
          (∫ t : Ioi (0:ℝ), (if (t:ℝ) < r then (t:ℝ)^2 else 0)
            ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1))) * M θ θ ∂(volume.toSphere) := by
          apply integral_congr_ae
          filter_upwards with θ
          exact hinner θ
    _ = (∫ t : Ioi (0:ℝ), (if (t:ℝ) < r then (t:ℝ)^2 else 0)
            ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1))) *
          ∫ θ : Metric.sphere (0:E) 1, M θ θ ∂(volume.toSphere) := integral_const_mul _ _
    _ = r ^ (n + 2) / ((n:ℝ) + 2) *
          ∫ θ : Metric.sphere (0:E) 1, M θ θ ∂(volume.toSphere) := by rw [hcval]

end Commons.Analysis.MeasureTheory
