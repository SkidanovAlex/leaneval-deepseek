/-
# ZeroFreeTables/OffAxis/RectC/Facts — small bridges for the `λ₁ ≥ 0.348` assembly
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.RectC.Tiny
import Submission.Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive
import Submission.Commons.Analysis.Complex.exterior_jensen_multiplicity
import Submission.Commons.Analysis.Complex.circleLogDerivContour_bound

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.OffAxis

open Work.LinnikContract Work.LinnikAreas

/-- A `zeroMult` zero of a non-principal character is a zero of the divisor of the completed
`L`-function of the primitive character inducing it. -/
theorem divisor_ne_zero_of_zeroMult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (hχ : χ ≠ 1) {R : ℝ} {u : ℂ}
    (hu : u ∈ Metric.closedBall (0 : ℂ) R) (hzm : zeroMult χ u ≠ 0) :
    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 R)) u ≠ 0 := by
  have hψne : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    have h2 := DirichletCharacter.changeLevel_primitiveCharacter χ
    rw [h, map_one] at h2
    exact h2.symm
  have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 R) :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hψne).analyticAt z
  have hcast : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 R)) u =
      ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) u : ℕ) : ℤ) :=
    Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han hu
  have hnat : analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) u ≠ 0 := by
    revert hzm
    simp only [zeroMult]
    intro h; exact h
  intro h0
  rw [hcast] at h0
  exact hnat (by exact_mod_cast h0)

/-- Conversely, a divisor zero is a `zeroMult` zero. -/
theorem zeroMult_ne_zero_of_divisor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (hχ : χ ≠ 1) {R : ℝ} {u : ℂ}
    (hdiv : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 R)) u ≠ 0) : zeroMult χ u ≠ 0 := by
  have hψne : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    have h2 := DirichletCharacter.changeLevel_primitiveCharacter χ
    rw [h, map_one] at h2
    exact h2.symm
  have hu : u ∈ Metric.closedBall (0 : ℂ) R :=
    Commons.Analysis.Complex.divisor_mem_of_ne_zero hdiv
  have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 R) :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hψne).analyticAt z
  have hcast : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 R)) u =
      ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) u : ℕ) : ℤ) :=
    Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han hu
  have hnat : analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) u ≠ 0 := by
    intro h0
    exact hdiv (by rw [hcast, h0]; rfl)
  revert hnat
  simp only [zeroMult]
  intro h; exact h

/-- For a real `z` the Laplace integral has no cosine factor. -/
theorem Fw_eq_expint {z : ℂ} (hz : z.im = 0) :
    (∫ t in (0:ℝ)..(8/3), Complex.exp (-(z * (t : ℂ))) * ((tf72f (3/4) t : ℝ) : ℂ)).re
      = ∫ t in (0:ℝ)..(8/3), Real.exp (-(z.re * t)) * tf72f (3/4) t := by
  have hcont : ContinuousOn (fun t : ℝ =>
      Complex.exp (-(z * (t : ℂ))) * ((tf72f (3/4) t : ℝ) : ℂ)) (Set.uIcc 0 (8/3)) := by
    refine ContinuousOn.mul ?_ ?_
    · exact (Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).neg)).continuousOn
    · exact Complex.continuous_ofReal.comp_continuousOn tf72f_cont34
  rw [re_intervalIntegral _ hcont.intervalIntegrable]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  have h1 : (-(z * (t : ℂ))).re = -(z.re * t) := by simp [Complex.mul_re]
  have h2 : (-(z * (t : ℂ))).im = 0 := by simp [Complex.mul_im, hz]
  rw [Complex.mul_re, Complex.exp_re, h1, h2, Complex.ofReal_re, Complex.ofReal_im,
    Real.cos_zero, mul_zero, sub_zero]
  ring

/-- Monotonicity of `∫₀^{8/3} e^{a t} f` in `a`. -/
theorem expint_mono {a b : ℝ} (hab : a ≤ b) :
    (∫ t in (0:ℝ)..(8/3), Real.exp (a * t) * tf72f (3/4) t)
      ≤ ∫ t in (0:ℝ)..(8/3), Real.exp (b * t) * tf72f (3/4) t := by
  have hcont1 : ContinuousOn (fun t : ℝ => Real.exp (a * t) * tf72f (3/4) t) (Set.uIcc 0 (8/3)) := by
    refine ContinuousOn.mul ?_ ?_
    · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
    · exact tf72f_cont34
  have hcont2 : ContinuousOn (fun t : ℝ => Real.exp (b * t) * tf72f (3/4) t) (Set.uIcc 0 (8/3)) := by
    refine ContinuousOn.mul ?_ ?_
    · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
    · exact tf72f_cont34
  apply intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 8/3)
    hcont1.intervalIntegrable hcont2.intervalIntegrable
  intro t ht
  have ht0 : 0 ≤ t := ht.1
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith [hab, ht0]))
    (tf72f_nonneg34 t)

end Work.ZeroFreeTables.OffAxis
