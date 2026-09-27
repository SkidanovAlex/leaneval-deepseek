import Mathlib
import Submission.Commons.Analysis.Complex.Harmonic.dirichlet_circle_boundary

/-!
# Boundary behaviour of the Poisson integral where the boundary datum is eventually constant

If `g : ℂ → ℝ` is circle integrable on the circle `|z| = r` (`r > 0`) and is constant, equal to
`c`, on a neighbourhood of the boundary point `x` (with `‖x‖ = r`) inside the circle, then the
Poisson integral `w ↦ ⨍ z, poissonKernel 0 w z * g z` tends to `c` as `w → x` through the open
disc `|w| < r`.

The proof is the standard approximate-identity argument for the Poisson kernel: write the average
as the average of `poissonKernel 0 w z * (g z - c)` (the kernel has total mass one), and bound the
latter pointwise on the circle.  On the arc on which `g = c` the integrand vanishes, while off that
arc the kernel is bounded by `8 * r * ‖w - x‖ / θ ^ 2` (`θ` measuring the distance of the arc from
`x`), thanks to `Commons.Analysis.Complex.Harmonic.poissonKernel_offArc_bound`.  Hence the whole
difference is bounded by a constant multiple of `‖w - x‖`.
-/

noncomputable section

open Complex Filter Metric MeasureTheory Real Set
open scoped Topology

namespace Work.Analysis.Poisson

/-- A function `g : ℂ → ℝ` is circle integrable as soon as its complexification is. -/
lemma circleIntegrable_of_ofReal {g : ℂ → ℝ} {c : ℂ} {r : ℝ}
    (hg : CircleIntegrable (fun z : ℂ => (g z : ℂ)) c r) : CircleIntegrable g c r := by
  rw [CircleIntegrable, intervalIntegrable_iff] at hg ⊢
  show MeasureTheory.Integrable (fun θ => g (circleMap c r θ))
      (MeasureTheory.volume.restrict (Set.uIoc 0 (2 * Real.pi)))
  simpa using (MeasureTheory.Integrable.re_im_iff.mpr hg.integrable).1

theorem poissonInt_tendsto_of_eventuallyEq {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r)
    (hg : CircleIntegrable (fun z : ℂ => (g z : ℂ)) 0 r) {x : ℂ} (hx : ‖x‖ = r) {c : ℝ}
    (hconst : ∀ᶠ z in nhdsWithin x (Metric.sphere (0 : ℂ) r), g z = c) :
    Filter.Tendsto (fun w : ℂ => Real.circleAverage (fun z : ℂ => poissonKernel 0 w z * g z) 0 r)
      (nhdsWithin x (Metric.ball (0 : ℂ) r)) (nhds c) := by
  have hgR : CircleIntegrable g 0 r := circleIntegrable_of_ofReal hg
  -- The boundary datum is constant on a spherical neighbourhood of `x`.
  obtain ⟨θ, hθpos, harc⟩ : ∃ θ : ℝ, 0 < θ ∧ ∀ z : ℂ, ‖z‖ = r → ‖z - x‖ < θ → g z = c := by
    rw [eventually_nhdsWithin_iff] at hconst
    rw [Metric.eventually_nhds_iff] at hconst
    obtain ⟨θ, hθpos, hθ⟩ := hconst
    exact ⟨θ, hθpos, fun z hz hzx =>
      hθ (by simpa [dist_eq_norm] using hzx) (by simpa [mem_sphere_iff_norm] using hz)⟩
  -- The pointwise bound on the circle.
  have hmain : ∀ w : ℂ, ‖w‖ < r → ‖w - x‖ ≤ θ / 2 →
      |Real.circleAverage (fun z : ℂ => poissonKernel 0 w z * g z) 0 r - c| ≤
        (8 * r * ‖w - x‖ / θ ^ 2) * Real.circleAverage (fun z : ℂ => |g z - c|) 0 r := by
    intro w hwlt hwxle
    have hPc : ContinuousOn (fun z : ℂ => poissonKernel 0 w z) (sphere (0 : ℂ) r) :=
      Commons.Analysis.Complex.Harmonic.continuousOn_poissonKernel_sphere_r hwlt
    have hPc' : ContinuousOn (fun z : ℂ => poissonKernel 0 w z) (sphere (0 : ℂ) |r|) := by
      simpa [abs_of_pos hr] using hPc
    have hgc_int : CircleIntegrable (fun z : ℂ => g z - c) 0 r :=
      hgR.sub (circleIntegrable_const c 0 r)
    have hPg : CircleIntegrable (fun z : ℂ => poissonKernel 0 w z * g z) 0 r :=
      hgR.continuousOn_mul hPc'
    have hPcst : CircleIntegrable (fun z : ℂ => poissonKernel 0 w z * c) 0 r :=
      (circleIntegrable_const c 0 r).continuousOn_mul hPc'
    have hPabs : CircleIntegrable (fun z : ℂ => poissonKernel 0 w z * |g z - c|) 0 r :=
      hgc_int.abs.continuousOn_mul hPc'
    have hCabs : CircleIntegrable (fun z : ℂ => (8 * r * ‖w - x‖ / θ ^ 2) * |g z - c|) 0 r :=
      hgc_int.abs.continuousOn_mul continuousOn_const
    -- The Poisson kernel has total mass one, so subtracting `c` means multiplying `g - c`.
    have hval : Real.circleAverage (fun z : ℂ => poissonKernel 0 w z * c) 0 r = c := by
      rw [show (fun z : ℂ => poissonKernel 0 w z * c)
          = (fun z : ℂ => c • poissonKernel 0 w z) from by
        funext z; rw [smul_eq_mul, mul_comm]]
      rw [Real.circleAverage_fun_smul,
        Commons.Analysis.Complex.Harmonic.poisson_total_mass_r hr hwlt]
      simp
    have hlin : Real.circleAverage (fun z : ℂ => poissonKernel 0 w z * g z) 0 r - c
        = Real.circleAverage (fun z : ℂ => poissonKernel 0 w z * (g z - c)) 0 r := by
      calc Real.circleAverage (fun z : ℂ => poissonKernel 0 w z * g z) 0 r - c
          = Real.circleAverage (fun z : ℂ => poissonKernel 0 w z * g z) 0 r
              - Real.circleAverage (fun z : ℂ => poissonKernel 0 w z * c) 0 r := by rw [hval]
        _ = Real.circleAverage
              (fun z : ℂ => poissonKernel 0 w z * g z - poissonKernel 0 w z * c) 0 r :=
              (Real.circleAverage_fun_sub hPg hPcst).symm
        _ = Real.circleAverage (fun z : ℂ => poissonKernel 0 w z * (g z - c)) 0 r := by
              congr 1; funext z; ring
    have hzr_of : ∀ z : ℂ, z ∈ sphere (0 : ℂ) |r| → ‖z‖ = r := by
      intro z hz
      have h := mem_sphere_iff_norm.mp hz
      rwa [sub_zero, abs_of_pos hr] at h
    -- Take absolute values inside the average; the kernel is nonnegative on the circle.
    have habs : |Real.circleAverage (fun z : ℂ => poissonKernel 0 w z * (g z - c)) 0 r|
        ≤ Real.circleAverage (fun z : ℂ => poissonKernel 0 w z * |g z - c|) 0 r := by
      have hcongr : Real.circleAverage (fun z : ℂ => |poissonKernel 0 w z * (g z - c)|) 0 r
          = Real.circleAverage (fun z : ℂ => poissonKernel 0 w z * |g z - c|) 0 r :=
        Real.circleAverage_congr_sphere
          (f₁ := fun z : ℂ => |poissonKernel 0 w z * (g z - c)|)
          (f₂ := fun z : ℂ => poissonKernel 0 w z * |g z - c|)
          (fun z hz => by
            have hzr := hzr_of z hz
            show |poissonKernel 0 w z * (g z - c)| = poissonKernel 0 w z * |g z - c|
            rw [abs_mul, abs_of_nonneg
              (Commons.Analysis.Complex.Harmonic.poissonKernel_pos_r hwlt hzr)])
      have habs := Real.abs_circleAverage_le_circleAverage_abs
        (f := fun z : ℂ => poissonKernel 0 w z * (g z - c)) (c := (0 : ℂ)) (R := r)
      exact le_trans habs (le_of_eq hcongr)
    -- Off the arc on which `g = c` the kernel decays linearly in `‖w - x‖`.
    have hmono : Real.circleAverage (fun z : ℂ => poissonKernel 0 w z * |g z - c|) 0 r
        ≤ Real.circleAverage (fun z : ℂ => (8 * r * ‖w - x‖ / θ ^ 2) * |g z - c|) 0 r := by
      refine Real.circleAverage_mono hPabs hCabs ?_
      intro z hz
      have hzr := hzr_of z hz
      by_cases hnear : ‖z - x‖ < θ
      · rw [harc z hzr hnear]; simp
      · have hfar : θ ≤ ‖z - x‖ := le_of_not_gt hnear
        exact mul_le_mul_of_nonneg_right
          (Commons.Analysis.Complex.Harmonic.poissonKernel_offArc_bound
            hwlt hθpos hwxle hx hfar hzr)
          (abs_nonneg _)
    have hsmul : Real.circleAverage (fun z : ℂ => (8 * r * ‖w - x‖ / θ ^ 2) * |g z - c|) 0 r
        = (8 * r * ‖w - x‖ / θ ^ 2) * Real.circleAverage (fun z : ℂ => |g z - c|) 0 r := by
      rw [show (fun z : ℂ => (8 * r * ‖w - x‖ / θ ^ 2) * |g z - c|)
          = (fun z : ℂ => (8 * r * ‖w - x‖ / θ ^ 2) • |g z - c|) from by
        funext z; rw [smul_eq_mul]]
      rw [Real.circleAverage_fun_smul, smul_eq_mul]
    calc |Real.circleAverage (fun z : ℂ => poissonKernel 0 w z * g z) 0 r - c|
        = |Real.circleAverage (fun z : ℂ => poissonKernel 0 w z * (g z - c)) 0 r| := by rw [hlin]
      _ ≤ Real.circleAverage (fun z : ℂ => poissonKernel 0 w z * |g z - c|) 0 r := habs
      _ ≤ Real.circleAverage (fun z : ℂ => (8 * r * ‖w - x‖ / θ ^ 2) * |g z - c|) 0 r := hmono
      _ = (8 * r * ‖w - x‖ / θ ^ 2) * Real.circleAverage (fun z : ℂ => |g z - c|) 0 r := hsmul
  -- Eventually `w` lies in the disc and is close to `x`.
  have hwball : ∀ᶠ w in nhdsWithin x (Metric.ball (0 : ℂ) r), ‖w‖ < r := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    simpa [mem_ball, dist_eq_norm] using hw
  have hwx : ∀ᶠ w in nhdsWithin x (Metric.ball (0 : ℂ) r), ‖w - x‖ ≤ θ / 2 := by
    have hb : Metric.ball x (θ / 2) ∈ nhds x := Metric.ball_mem_nhds x (by linarith)
    have h1 : {w : ℂ | ‖w - x‖ ≤ θ / 2} ∈ nhds x :=
      Filter.mem_of_superset hb (fun w hw => le_of_lt (by simpa [dist_eq_norm] using hw))
    exact nhdsWithin_le_nhds h1
  have hnorm : Filter.Tendsto (fun w : ℂ => ‖w - x‖)
      (nhdsWithin x (Metric.ball (0 : ℂ) r)) (nhds 0) := by
    have h1 : Filter.Tendsto (fun w : ℂ => w - x) (nhds x) (nhds (x - x)) :=
      (continuous_id.sub continuous_const).tendsto x
    have h2 : Filter.Tendsto (fun w : ℂ => w - x)
        (nhdsWithin x (Metric.ball (0 : ℂ) r)) (nhds (x - x)) :=
      h1.mono_left nhdsWithin_le_nhds
    simpa using h2.norm
  have hC : Filter.Tendsto
      (fun w : ℂ => (8 * r * ‖w - x‖ / θ ^ 2)
        * Real.circleAverage (fun z : ℂ => |g z - c|) 0 r)
      (nhdsWithin x (Metric.ball (0 : ℂ) r)) (nhds 0) := by
    have h3 : Filter.Tendsto
        (fun w : ℂ => ‖w - x‖
          * ((8 * r / θ ^ 2) * Real.circleAverage (fun z : ℂ => |g z - c|) 0 r))
        (nhdsWithin x (Metric.ball (0 : ℂ) r)) (nhds 0) := by
      have h := hnorm.mul_const
        ((8 * r / θ ^ 2) * Real.circleAverage (fun z : ℂ => |g z - c|) 0 r)
      simpa using h
    refine h3.congr' (Filter.Eventually.of_forall (fun w => ?_))
    ring
  have hupper : ∀ᶠ w in nhdsWithin x (Metric.ball (0 : ℂ) r),
      |Real.circleAverage (fun z : ℂ => poissonKernel 0 w z * g z) 0 r - c| ≤
        (8 * r * ‖w - x‖ / θ ^ 2) * Real.circleAverage (fun z : ℂ => |g z - c|) 0 r := by
    filter_upwards [hwball, hwx] with w hw hwxle
    exact hmain w hw hwxle
  have h0 := squeeze_zero' (Filter.Eventually.of_forall (fun w : ℂ => abs_nonneg _)) hupper hC
  exact (tendsto_iff_norm_sub_tendsto_zero).mpr (by simpa [Real.norm_eq_abs] using h0)

end Work.Analysis.Poisson
