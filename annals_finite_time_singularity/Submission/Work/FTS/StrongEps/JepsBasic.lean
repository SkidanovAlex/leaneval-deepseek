/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/JepsBasic.lean` — elementary properties of `J_ε`

The small facts about the log-coordinate mollifier that the limit arguments of `E5` use:

* `Jeps_const` — `J_ε` preserves the constants (mass one);
* `Jeps_nonneg` — `J_ε` preserves nonnegativity;
* `abs_Jeps_le_sup` — `|J_ε f| ≤ sup` of `f` over the shifted region;
* `Jeps_add` — `J_ε` is additive (on integrable profiles).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.Jker_integral_eq_one

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **`J_ε` preserves the constants** (the kernel has mass one). -/
theorem Jeps_const (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε) (c : ℝ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Jeps ρ ε (fun _ _ => c) z θ = c := by
  rw [Jeps_eq_integral ρ ε _ hz hθ,
    show (fun p : ℝ × ℝ => Jker ρ ε p * c) = fun p => c * Jker ρ ε p from
      funext fun p => mul_comm _ _]
  rw [MeasureTheory.integral_const_mul, Jker_integral_eq_one ρ hρ hε, mul_one]

/-- **`J_ε` preserves nonnegativity**. -/
theorem Jeps_nonneg (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {f : Fn} (hf : ∀ z θ, 0 ≤ f z θ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 ≤ Jeps ρ ε f z θ := by
  rw [Jeps_eq_integral ρ ε _ hz hθ]
  refine MeasureTheory.integral_nonneg fun p => ?_
  have hk : 0 ≤ Jker ρ ε p := by
    simp only [Jker]
    exact mul_nonneg (by positivity) (hρ.nonneg _)
  exact mul_nonneg hk (hf _ _)

/-- **`J_ε` is dominated by the sup over the shifted region**: the exact form in which the
mollified quantities are bounded in the limit arguments (`E5`). -/
theorem abs_Jeps_le_sup (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {f : Fn} {z θ M : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hM : ∀ p : ℝ × ℝ, |p.1| ≤ ε → |p.2| ≤ ε → |f (zShift z p.1) (thShift θ p.2)| ≤ M)
    (hM0 : 0 ≤ M) :
    |Jeps ρ ε f z θ| ≤ M := by
  rw [Jeps_eq_integral ρ ε _ hz hθ]
  have hknn : ∀ p : ℝ × ℝ, 0 ≤ Jker ρ ε p := by
    intro p; simp only [Jker]; exact mul_nonneg (by positivity) (hρ.nonneg _)
  have hpt : ∀ᵐ p ∂volume,
      ‖Jker ρ ε p * f (zShift z p.1) (thShift θ p.2)‖ ≤ Jker ρ ε p * M := by
    refine Eventually.of_forall fun p => ?_
    by_cases hp : p ∈ Metric.closedBall (0 : ℝ × ℝ) ε
    · have hp' : max |p.1| |p.2| ≤ ε := by
        simpa only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs]
          using hp
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hknn p)]
      exact mul_le_mul_of_nonneg_left
        (hM p (le_trans (le_max_left _ _) hp') (le_trans (le_max_right _ _) hp')) (hknn p)
    · rw [Jker_eq_zero_of_not_mem hρ hε hp, zero_mul, norm_zero, zero_mul]
  by_cases hint : Integrable (fun p : ℝ × ℝ => Jker ρ ε p * f (zShift z p.1) (thShift θ p.2))
  · have hmaj : Integrable (fun p : ℝ × ℝ => Jker ρ ε p * M) :=
      (Jker_integrable hρ hε).mul_const M
    calc |∫ p : ℝ × ℝ, Jker ρ ε p * f (zShift z p.1) (thShift θ p.2)|
        ≤ ∫ p : ℝ × ℝ, ‖Jker ρ ε p * f (zShift z p.1) (thShift θ p.2)‖ :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ p : ℝ × ℝ, Jker ρ ε p * M := MeasureTheory.integral_mono_ae hint.norm hmaj hpt
      _ = M := by
          rw [show (fun p : ℝ × ℝ => Jker ρ ε p * M) = fun p => M * Jker ρ ε p from
            funext fun p => mul_comm _ _]
          rw [MeasureTheory.integral_const_mul, Jker_integral_eq_one ρ hρ hε, mul_one]
  · rw [MeasureTheory.integral_undef hint, abs_zero]
    exact hM0

end Work.FTS.StrongEps
