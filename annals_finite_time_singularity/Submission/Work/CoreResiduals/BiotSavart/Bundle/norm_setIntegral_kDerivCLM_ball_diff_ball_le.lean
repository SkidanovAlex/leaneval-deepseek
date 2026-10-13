import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.CoreResiduals.BiotSavart.Bundle.integrableOn_and_norm_setIntegral_kDerivCLM_diff_ball
import Submission.Work.CoreResiduals.BiotSavart.integral_kDerivCLM_annulus_eq_zero
import Submission.Work.CoreResiduals.BiotSavart.Bundle.setIntegral_ball_diff_ball_comp_sub_left
import Submission.Work.CoreResiduals.BiotSavart.Bundle.cube_div_mono_le
import Submission.Work.CoreResiduals.BiotSavart.Bundle.cube_div_le_27

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart.Bundle

open MeasureTheory Metric Set
open scoped Topology NNReal ENNReal

/-- **The constant-vector (kernel mass) piece of the Schauder difference estimate.**

Let `δ > 0`, `R' + 2δ < ρ`, and let `x, y : ℝ³` with `‖x - y‖ ≤ δ`, `‖x‖ ≤ R'`, `‖y‖ ≤ R'`.  Then

`‖∫_{B(0,ρ) \ B(y,2δ)} kDerivCLM (x - a) da‖ ≤ (16π/3)((ρ+R')³/(ρ-R')³) + (16π/3)·27`,

a bound *uniform in δ* away from the singularity.

Proof.  Substituting `b = x - a` turns the region into `B(x,ρ) \ B(x-y,2δ)`.  The small ball
`B(0,δ/2)` is contained in both `B(x,ρ)` and `B(x-y,2δ)`: `‖x‖ + δ/2 ≤ R' + δ/2 < R' + 2δ < ρ`,
and `‖x-y‖ + δ/2 ≤ 3δ/2 < 2δ`.  Also `B(x-y,2δ) ⊆ B(x,ρ)` because
`‖x - (x-y)‖ + 2δ = ‖y‖ + 2δ ≤ R' + 2δ < ρ`.  Hence
`∫_{B(x,ρ)\B(x-y,2δ)} = ∫_{B(x,ρ)\B(0,δ/2)} - ∫_{B(x-y,2δ)\B(0,δ/2)}` and each term is bounded by
`integrableOn_and_norm_setIntegral_kDerivCLM_diff_ball`: the first by `(16π/3)((ρ+‖x‖)³/(ρ-‖x‖)³)`,
the second — with `R = 2δ`, `‖c‖ = ‖x-y‖ ≤ δ` — by `(16π/3)((3δ)³/δ³) = (16π/3)·27`. -/
theorem norm_setIntegral_kDerivCLM_ball_diff_ball_le {ρ R' δ : ℝ} (hδ : 0 < δ)
    (hρ : R' + 2 * δ < ρ) {x y : Work.LWP.R3} (hx : ‖x‖ ≤ R') (hy : ‖y‖ ≤ R')
    (hxy : ‖x - y‖ ≤ δ) :
    ‖∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball y (2 * δ)),
        Work.StabilityFar.Decay.kDerivCLM (x - a)‖
      ≤ (16 * Real.pi / 3) * ((ρ + R') ^ 3 / (ρ - R') ^ 3) + (16 * Real.pi / 3) * 27 := by
  classical
  -- **Step 1.**  Substitute `b = x - a`: the region `B(0,ρ) \ B(y,2δ)` becomes
  -- `B(x,ρ) \ B(x-y,2δ)` and the integrand becomes the origin-singular kernel `kDerivCLM b`.
  rw [setIntegral_ball_diff_ball_comp_sub_left Work.StabilityFar.Decay.kDerivCLM ρ (2 * δ) x y]
  have hR'nn : 0 ≤ R' := le_trans (norm_nonneg x) hx
  have hρpos : 0 < ρ := by linarith
  have hR'ρ : R' < ρ := by linarith
  -- **Step 2.**  Containment of the removed small ball `C = B(0,δ/2)`.
  have hCsub2 : Metric.ball (0 : Work.LWP.R3) (δ / 2) ⊆ Metric.ball (x - y) (2 * δ) := by
    intro b hb
    rw [Metric.mem_ball, dist_zero_right] at hb
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖b - (x - y)‖ ≤ ‖b‖ + ‖x - y‖ := norm_sub_le b (x - y)
      _ < δ / 2 + δ := by linarith
      _ = 3 * δ / 2 := by ring
      _ < 2 * δ := by linarith
  -- `B(x - y, 2δ) ⊆ B(x,ρ)`, because `‖y‖ + 2δ ≤ R' + 2δ < ρ`.
  have h21 : Metric.ball (x - y) (2 * δ) ⊆ Metric.ball x ρ := by
    intro b hb
    rw [Metric.mem_ball, dist_eq_norm] at hb
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖b - x‖ ≤ ‖b - (x - y)‖ + ‖(x - y) - x‖ := by
          have he : b - x = (b - (x - y)) + ((x - y) - x) := by abel
          rw [he]; exact norm_add_le _ _
      _ = ‖b - (x - y)‖ + ‖y‖ := by
          rw [show (x - y) - x = -y from by abel, norm_neg]
      _ < 2 * δ + R' := by linarith
      _ = R' + 2 * δ := by ring
      _ < ρ := hρ
  have hCsub1 : Metric.ball (0 : Work.LWP.R3) (δ / 2) ⊆ Metric.ball x ρ := hCsub2.trans h21
  -- **Step 3.**  The region identity `B(x,ρ) \ B(x-y,2δ) = (A₁ \ A₂)` with
  -- `A₁ = B(x,ρ) \ C`, `A₂ = B(x-y,2δ) \ C`.
  have hAeq : (Metric.ball x ρ \ Metric.ball (0 : Work.LWP.R3) (δ / 2))
        \ (Metric.ball (x - y) (2 * δ) \ Metric.ball (0 : Work.LWP.R3) (δ / 2))
      = Metric.ball x ρ \ Metric.ball (x - y) (2 * δ) := by
    ext b
    simp only [Set.mem_sdiff]
    constructor
    · rintro ⟨⟨hb1, hb2⟩, hb3⟩
      exact ⟨hb1, fun h => hb3 ⟨h, hb2⟩⟩
    · rintro ⟨hb1, hb2⟩
      exact ⟨⟨hb1, fun hc => hb2 (hCsub2 hc)⟩, fun h => hb2 h.1⟩
  -- **Step 4.**  Integrability of the kernel on both peeled regions (the Calderón–Zygmund
  -- cancellation lemma), which is what makes the splitting of the integral legitimate.
  have hInt1 : IntegrableOn Work.StabilityFar.Decay.kDerivCLM
      (Metric.ball x ρ \ Metric.ball (0 : Work.LWP.R3) (δ / 2)) volume :=
    (integrableOn_and_norm_setIntegral_kDerivCLM_diff_ball (c := x) (R := ρ) (r := δ / 2)
      hρpos (by linarith) hCsub1).1
  -- **Step 5.**  The two bounds, one from each peeled region.
  have hb1 : ‖∫ b in Metric.ball x ρ \ Metric.ball (0 : Work.LWP.R3) (δ / 2),
        Work.StabilityFar.Decay.kDerivCLM b‖
      ≤ (16 * Real.pi / 3) * ((ρ + R') ^ 3 / (ρ - R') ^ 3) := by
    refine le_trans (integrableOn_and_norm_setIntegral_kDerivCLM_diff_ball (c := x) (R := ρ)
      (r := δ / 2) hρpos (by linarith) hCsub1).2 ?_
    exact mul_le_mul_of_nonneg_left (cube_div_mono_le hR'nn hR'ρ hx) (by positivity)
  have hb2 : ‖∫ b in Metric.ball (x - y) (2 * δ) \ Metric.ball (0 : Work.LWP.R3) (δ / 2),
        Work.StabilityFar.Decay.kDerivCLM b‖
      ≤ (16 * Real.pi / 3) * 27 := by
    refine le_trans (integrableOn_and_norm_setIntegral_kDerivCLM_diff_ball (c := x - y) (R := 2 * δ)
      (r := δ / 2) (by linarith) (by linarith) hCsub2).2 ?_
    exact mul_le_mul_of_nonneg_left (cube_div_le_27 hδ (norm_nonneg _) hxy) (by positivity)
  -- **Step 6.**  Split the integral over `A₁ \ A₂` and apply the triangle inequality.
  have hdec : (∫ b in Metric.ball x ρ \ Metric.ball (x - y) (2 * δ),
          Work.StabilityFar.Decay.kDerivCLM b)
      = (∫ b in Metric.ball x ρ \ Metric.ball (0 : Work.LWP.R3) (δ / 2),
            Work.StabilityFar.Decay.kDerivCLM b)
        - (∫ b in Metric.ball (x - y) (2 * δ) \ Metric.ball (0 : Work.LWP.R3) (δ / 2),
            Work.StabilityFar.Decay.kDerivCLM b) := by
    rw [← hAeq]
    refine MeasureTheory.setIntegral_sdiff ?_ hInt1 ?_
    · exact measurableSet_ball.diff measurableSet_ball
    · rintro b ⟨hb1, hb2⟩; exact ⟨h21 hb1, hb2⟩
  calc ‖∫ b in Metric.ball x ρ \ Metric.ball (x - y) (2 * δ), Work.StabilityFar.Decay.kDerivCLM b‖
      = ‖(∫ b in Metric.ball x ρ \ Metric.ball (0 : Work.LWP.R3) (δ / 2),
              Work.StabilityFar.Decay.kDerivCLM b)
          - (∫ b in Metric.ball (x - y) (2 * δ) \ Metric.ball (0 : Work.LWP.R3) (δ / 2),
              Work.StabilityFar.Decay.kDerivCLM b)‖ := by rw [hdec]
    _ ≤ ‖∫ b in Metric.ball x ρ \ Metric.ball (0 : Work.LWP.R3) (δ / 2),
            Work.StabilityFar.Decay.kDerivCLM b‖
        + ‖∫ b in Metric.ball (x - y) (2 * δ) \ Metric.ball (0 : Work.LWP.R3) (δ / 2),
            Work.StabilityFar.Decay.kDerivCLM b‖ := norm_sub_le _ _
    _ ≤ (16 * Real.pi / 3) * ((ρ + R') ^ 3 / (ρ - R') ^ 3) + (16 * Real.pi / 3) * 27 :=
        add_le_add hb1 hb2

end Work.CoreResiduals.BiotSavart.Bundle
