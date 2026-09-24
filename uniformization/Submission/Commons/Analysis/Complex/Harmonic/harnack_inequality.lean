import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Complex.Harmonic.MeanValue

noncomputable section
open Set Metric Complex InnerProductSpace Filter
open scoped Real Topology

namespace Commons.Analysis.Complex.Harmonic

/-- The Poisson kernel (center `0`, radius `R`) evaluated at a point `z` on the circle of
radius `R` is bounded above by `(R + ‖w‖) / (R - ‖w‖)` whenever `w` lies strictly inside the
circle. -/
private lemma poissonKernel_le_R {w z : ℂ} {R : ℝ} (hz : z ∈ sphere (0 : ℂ) R) (hw : ‖w‖ < R) :
    poissonKernel (0 : ℂ) w z ≤ (R + ‖w‖) / (R - ‖w‖) := by
  have hwball : w ∈ ball (0 : ℂ) R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
  calc
    poissonKernel (0 : ℂ) w z = ((z - 0 + (w - 0)) / (z - 0 - (w - 0))).re := by
      simp [poissonKernel_eq_re_herglotzRieszKernel, herglotzRieszKernel_def]
    _ ≤ (R + ‖w - 0‖) / (R - ‖w - 0‖) := by
      exact re_herglotzRieszKernel_le (c := (0 : ℂ)) hz hwball
    _ = (R + ‖w‖) / (R - ‖w‖) := by simp

/-- The Poisson kernel (center `0`, radius `R`) evaluated at a point `z` on the circle of
radius `R` is bounded below by `(R - ‖w‖) / (R + ‖w‖)` whenever `w` lies strictly inside the
circle. -/
private lemma R_le_poissonKernel {w z : ℂ} {R : ℝ} (hz : z ∈ sphere (0 : ℂ) R) (hw : ‖w‖ < R) :
    (R - ‖w‖) / (R + ‖w‖) ≤ poissonKernel (0 : ℂ) w z := by
  have hwball : w ∈ ball (0 : ℂ) R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
  calc
    (R - ‖w‖) / (R + ‖w‖) = (R - ‖w - 0‖) / (R + ‖w - 0‖) := by simp
    _ ≤ ((z - 0 + (w - 0)) / (z - 0 - (w - 0))).re := by
      exact le_re_herglotzRieszKernel (c := (0 : ℂ)) hz hwball
    _ = poissonKernel (0 : ℂ) w z := by
      simp [poissonKernel_eq_re_herglotzRieszKernel, herglotzRieszKernel_def]

/-- **Harnack's inequality** for non-negative harmonic functions on a closed ball
`closedBall 0 R` (harmonic in a neighborhood of the closed ball, non-negative there).
For every point `w` strictly inside the ball,
`((R - ‖w‖) / (R + ‖w‖)) * f 0 ≤ f w ≤ ((R + ‖w‖) / (R - ‖w‖)) * f 0`.
This follows from the Poisson integral formula for `f` on the circle of radius `R`
(Mathlib `InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul` together with the
Mathlib kernel bounds `re_herglotzRieszKernel_le` / `le_re_herglotzRieszKernel`, using
`poissonKernel_eq_re_herglotzRieszKernel`, positivity of `f`, monotonicity of the circle
average, and the forward mean value property `HarmonicOnNhd.circleAverage_eq`). -/
theorem harnack_inequality {f : ℂ → ℝ} {R : ℝ}
    (hf : InnerProductSpace.HarmonicOnNhd f (closedBall (0 : ℂ) R))
    (hpos : ∀ z : ℂ, ‖z‖ ≤ R → 0 ≤ f z) {w : ℂ} (hw : ‖w‖ < R) :
    ((R - ‖w‖) / (R + ‖w‖)) * f (0 : ℂ) ≤ f w ∧
      f w ≤ ((R + ‖w‖) / (R - ‖w‖)) * f (0 : ℂ) := by
  have hRpos : 0 < R := lt_of_le_of_lt (norm_nonneg w) hw
  have hRge : 0 ≤ R := hRpos.le
  have hwball : w ∈ ball (0 : ℂ) R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hfsphere : ContinuousOn f (sphere (0 : ℂ) R) :=
    hf.continuousOn.mono Metric.sphere_subset_closedBall
  -- the Poisson kernel is continuous on the circle of radius `R`
  have hKcont : ContinuousOn (fun z : ℂ => poissonKernel (0 : ℂ) w z) (sphere (0 : ℂ) R) := by
    have hc : ContinuousOn (herglotzRieszKernel (0 : ℂ) w) (sphere (0 : ℂ) |R|) :=
      continuousOn_herglotzRieszKernel_sphere (c := (0 : ℂ)) (w := w)
        (fun hs => by
          rw [Metric.mem_sphere, dist_zero_right] at hs
          rw [Metric.mem_ball, dist_zero_right] at hwball
          linarith [le_abs_self R])
    have hcre : ContinuousOn (fun z : ℂ => (herglotzRieszKernel (0 : ℂ) w z).re)
        (sphere (0 : ℂ) |R|) := by
      simpa [Function.comp_def] using Complex.continuous_re.comp_continuousOn hc
    have hcp : ContinuousOn (fun z : ℂ => poissonKernel (0 : ℂ) w z) (sphere (0 : ℂ) |R|) := by
      simpa [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_def] using hcre
    simpa [abs_of_nonneg hRge] using hcp
  have hKf_eq : (fun z : ℂ => poissonKernel (0 : ℂ) w z * f z)
      = poissonKernel (0 : ℂ) w • f := by
    ext z
    simp [smul_eq_mul]
  -- Poisson integral representation of `f w` on the circle of radius `R`
  have hrep : Real.circleAverage (fun z : ℂ => poissonKernel (0 : ℂ) w z * f z)
      (0 : ℂ) R = f w := by
    rw [hKf_eq]
    exact InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul hf hwball
  -- forward mean value property at the center
  have hmv : Real.circleAverage f (0 : ℂ) R = f (0 : ℂ) := by
    have hf' : InnerProductSpace.HarmonicOnNhd f (closedBall (0 : ℂ) |R|) := by
      simpa [abs_of_nonneg hRge] using hf
    exact InnerProductSpace.HarmonicOnNhd.circleAverage_eq hf'
  constructor
  · -- lower bound: ((R - ‖w‖) / (R + ‖w‖)) * f 0 ≤ f w
    calc
      ((R - ‖w‖) / (R + ‖w‖)) * f (0 : ℂ)
          = Real.circleAverage (fun z : ℂ => ((R - ‖w‖) / (R + ‖w‖)) * f z) (0 : ℂ) R := by
        rw [← hmv]
        have h : (fun z : ℂ => ((R - ‖w‖) / (R + ‖w‖)) * f z)
            = ((R - ‖w‖) / (R + ‖w‖)) • f := by
          funext z
          simp [smul_eq_mul]
        rw [h]
        simp [Real.circleAverage_smul, smul_eq_mul]
      _ ≤ Real.circleAverage (fun z : ℂ => poissonKernel (0 : ℂ) w z * f z) (0 : ℂ) R := by
        apply Real.circleAverage_mono
        · exact ContinuousOn.circleIntegrable hRge
            ((continuousOn_const.mul hfsphere))
        · exact ContinuousOn.circleIntegrable hRge (hKcont.mul hfsphere)
        · intro z hz
          have hzR : z ∈ sphere (0 : ℂ) R := by simpa [abs_of_nonneg hRge] using hz
          have hnorm : ‖z‖ ≤ R := by
            have hn : ‖z‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hzR
            exact le_of_eq hn
          exact mul_le_mul_of_nonneg_right (R_le_poissonKernel hzR hw) (hpos z hnorm)
      _ = f w := hrep
  · -- upper bound: f w ≤ ((R + ‖w‖) / (R - ‖w‖)) * f 0
    calc
      f w = Real.circleAverage (fun z : ℂ => poissonKernel (0 : ℂ) w z * f z) (0 : ℂ) R := hrep.symm
      _ ≤ Real.circleAverage (fun z : ℂ => ((R + ‖w‖) / (R - ‖w‖)) * f z) (0 : ℂ) R := by
        apply Real.circleAverage_mono
        · exact ContinuousOn.circleIntegrable hRge (hKcont.mul hfsphere)
        · exact ContinuousOn.circleIntegrable hRge
            ((continuousOn_const.mul hfsphere))
        · intro z hz
          have hzR : z ∈ sphere (0 : ℂ) R := by simpa [abs_of_nonneg hRge] using hz
          have hnorm : ‖z‖ ≤ R := by
            have hn : ‖z‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hzR
            exact le_of_eq hn
          exact mul_le_mul_of_nonneg_right (poissonKernel_le_R hzR hw) (hpos z hnorm)
      _ = ((R + ‖w‖) / (R - ‖w‖)) * f (0 : ℂ) := by
        rw [← hmv]
        have h : (fun z : ℂ => ((R + ‖w‖) / (R - ‖w‖)) * f z)
            = ((R + ‖w‖) / (R - ‖w‖)) • f := by
          funext z
          simp [smul_eq_mul]
        rw [h]
        simp [Real.circleAverage_smul, smul_eq_mul]

end Commons.Analysis.Complex.Harmonic