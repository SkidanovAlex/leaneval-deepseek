import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.CoreResiduals.BiotSavart.norm_bsField_diff_bound
import Submission.Work.FTS.BSSwirl.NewtonPotentialAux
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.QDefs
import Submission.Work.LWP.BiotSavart.nearField_bound
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.StabilityFar.Decay.hasDerivAt_biotSavart
import Submission.Work.StabilityFar.Decay.norm_kDerivCLM_sub_le
import Submission.Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.Bundle.norm_setIntegral_kDerivCLM_ball_diff_ball_le =====
section

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
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.biotSavart_norm_le_of_bounded_supported =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `biotSavart_norm_le_of_bounded_supported`

A *sharp* near-field (indeed everywhere) bound for the Biot–Savart field of a vorticity that is
bounded by `M ≥ 0` and supported in `B(0,R)`: for **every** point `x`,

  `‖biotSavart ω x‖ ≤ M * (‖x‖ + R + 1)`.

The point of the estimate is that the constant is linear in `‖x‖ + R` rather than a fixed
multiple of `R` (as in `Work.LWP.BiotSavart.nearField_bound`, which gives `3 M R`): the support
`B(0,R)` lies in the ball of radius `‖x‖ + R` about `x`, so

  `‖biotSavart ω x‖ ≤ (4π)⁻¹ M ∫_{‖y‖≤R} ‖x-y‖⁻² dy ≤ (4π)⁻¹ M · 4π(‖x‖ + R) = M (‖x‖ + R)`,

using `∫_{B(x,r)} ‖z - x‖⁻² dz = 4π r` (`inv_sq_lintegral_closedBall_shifted_le`), the
dimensional borderline case `s = -2` in which the kernel singularity exactly cancels the
spherical Jacobian.
-/

open MeasureTheory Metric
open scoped Topology ENNReal

namespace Work.CoreResiduals.BiotSavart

/-- **The scalar near-field weight, centred at the origin.**  For a vorticity supported in
`B(0,R)` the singular weight `‖x - y‖⁻²` is integrated against the ball `B(0,R)`, which is
contained in the ball of radius `‖x‖ + R` about `x`; the shifted ball integral
`Work.LWP.BiotSavart.inv_sq_lintegral_closedBall_shifted_le` then bounds it by `4π(‖x‖ + R)`. -/
theorem inv_sq_lintegral_closedBall_origin_le {R : ℝ} (hR : 0 ≤ R) (x : Work.LWP.R3) :
    ∫⁻ y in Metric.closedBall (0 : Work.LWP.R3) R, ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)
      ≤ ENNReal.ofReal (4 * Real.pi * (‖x‖ + R)) := by
  have hsub : Metric.closedBall (0 : Work.LWP.R3) R ⊆ Metric.closedBall x (‖x‖ + R) := by
    intro y hy
    simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hy ⊢
    calc ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ R + ‖x‖ := by linarith
      _ = ‖x‖ + R := by ring
  calc ∫⁻ y in Metric.closedBall (0 : Work.LWP.R3) R, ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)
      = ∫⁻ y in Metric.closedBall (0 : Work.LWP.R3) R,
          ENNReal.ofReal ((‖y - x‖ ^ (2 : ℕ))⁻¹) := by
        apply lintegral_congr
        intro y
        rw [norm_sub_rev]
    _ ≤ ∫⁻ y in Metric.closedBall x (‖x‖ + R), ENNReal.ofReal ((‖y - x‖ ^ (2 : ℕ))⁻¹) :=
        lintegral_mono_set hsub
    _ ≤ ENNReal.ofReal (4 * Real.pi * (‖x‖ + R)) :=
        Work.LWP.BiotSavart.inv_sq_lintegral_closedBall_shifted_le x (by positivity)

/-- **The `L¹` estimate for the Biot–Savart integrand, with a free constant.**  If `ω` is bounded
by `M ≥ 0` and supported in `B(0,R)`, and if the scalar weight `‖x - y‖⁻²` has integral at most
`A` over that ball, then the `ℝ³`-valued integrand has integral at most `M · A`:

  `∫⁻ y, ‖(‖x-y‖³)⁻¹ • (ω y × (x-y))‖ ≤ M · A`.

This is `Work.LWP.BiotSavart.lintegral_bsIntegrand_le` with the particular value `12πR` of `A`
replaced by an arbitrary bound, which is what the linear-in-`‖x‖` estimate requires. -/
theorem lintegral_bsIntegrand_le_mul {ω : Work.LWP.R3 → Work.LWP.R3} {R M A : ℝ} (hM : 0 ≤ M)
    (hω : ∀ y, ‖ω y‖ ≤ M) (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (x : Work.LWP.R3)
    (hscal : ∫⁻ y in Metric.closedBall (0 : Work.LWP.R3) R,
        ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹) ≤ ENNReal.ofReal A) :
    ∫⁻ y, ENNReal.ofReal ‖Work.LWP.BiotSavart.bsIntegrand ω x y‖
      ≤ ENNReal.ofReal (M * A) := by
  classical
  have hsmeas : MeasurableSet (Metric.closedBall (0 : Work.LWP.R3) R) :=
    Metric.isClosed_closedBall.measurableSet
  have hpoint : ∀ y, ENNReal.ofReal ‖Work.LWP.BiotSavart.bsIntegrand ω x y‖
      ≤ (Metric.closedBall (0 : Work.LWP.R3) R).indicator
          (fun y => ENNReal.ofReal M * ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)) y := by
    intro y
    by_cases hy : y ∈ Metric.closedBall (0 : Work.LWP.R3) R
    · rw [Set.indicator_of_mem hy, ← ENNReal.ofReal_mul hM]
      exact ENNReal.ofReal_le_ofReal (Work.LWP.BiotSavart.bsIntegrand_norm_le hM hω x y)
    · rw [Set.indicator_of_notMem hy]
      have hωy : ω y = 0 := by
        by_contra hne
        exact hy (hsupp y hne)
      simp [Work.LWP.BiotSavart.bsIntegrand, hωy]
  have hsplit : (fun y => (Metric.closedBall (0 : Work.LWP.R3) R).indicator
        (fun y => ENNReal.ofReal M * ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)) y)
      = fun y => ENNReal.ofReal M * (Metric.closedBall (0 : Work.LWP.R3) R).indicator
          (fun y => ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)) y := by
    funext y
    by_cases hy : y ∈ Metric.closedBall (0 : Work.LWP.R3) R <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]
  calc ∫⁻ y, ENNReal.ofReal ‖Work.LWP.BiotSavart.bsIntegrand ω x y‖
      ≤ ∫⁻ y, (Metric.closedBall (0 : Work.LWP.R3) R).indicator
          (fun y => ENNReal.ofReal M * ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)) y :=
        lintegral_mono hpoint
    _ = ∫⁻ y, ENNReal.ofReal M * (Metric.closedBall (0 : Work.LWP.R3) R).indicator
          (fun y => ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)) y := by rw [hsplit]
    _ = ENNReal.ofReal M * ∫⁻ y, (Metric.closedBall (0 : Work.LWP.R3) R).indicator
          (fun y => ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)) y :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal M * ∫⁻ y in Metric.closedBall (0 : Work.LWP.R3) R,
          ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹) := by
        rw [lintegral_indicator hsmeas]
    _ ≤ ENNReal.ofReal M * ENNReal.ofReal A := mul_le_mul_right hscal _
    _ = ENNReal.ofReal (M * A) := by rw [← ENNReal.ofReal_mul hM]

theorem biotSavart_norm_le_of_bounded_supported {ω : Work.LWP.R3 → Work.LWP.R3} {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) (hω : ∀ a, ‖ω a‖ ≤ M)
    (hsupp : ∀ a, ω a ≠ 0 → a ∈ Metric.closedBall 0 R)
    (hm : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume) (x : Work.LWP.R3) :
    ‖Work.LWP.biotSavart ω x‖ ≤ M * (‖x‖ + R + 1) := by
  have hR0 : 0 ≤ R := le_of_lt hR
  set A : ℝ := ‖x‖ + R with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hscal : ∫⁻ y in Metric.closedBall (0 : Work.LWP.R3) R,
      ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹) ≤ ENNReal.ofReal (4 * Real.pi * A) := by
    rw [hA]
    exact inv_sq_lintegral_closedBall_origin_le hR0 x
  have hInt := lintegral_bsIntegrand_le_mul (A := 4 * Real.pi * A) hM hω hsupp x hscal
  have h1 : ‖∫ y, Work.LWP.BiotSavart.bsIntegrand ω x y‖
      ≤ (∫⁻ y, ENNReal.ofReal ‖Work.LWP.BiotSavart.bsIntegrand ω x y‖).toReal :=
    norm_integral_le_lintegral_norm _
  have h2 : (∫⁻ y, ENNReal.ofReal ‖Work.LWP.BiotSavart.bsIntegrand ω x y‖).toReal
      ≤ M * (4 * Real.pi * A) :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hInt).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  rw [Work.LWP.BiotSavart.biotSavart_eq_integral, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (4 * Real.pi)⁻¹)]
  calc (4 * Real.pi)⁻¹ * ‖∫ y, Work.LWP.BiotSavart.bsIntegrand ω x y‖
      ≤ (4 * Real.pi)⁻¹ * (M * (4 * Real.pi * A)) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
    _ ≤ M * (‖x‖ + R + 1) := by
        rw [hA]
        have heq : (4 * Real.pi)⁻¹ * (M * (4 * Real.pi * (‖x‖ + R))) = M * (‖x‖ + R) := by
          field_simp
        rw [heq]
        nlinarith [hM, norm_nonneg x]

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.integrableOn_crossL_kf_ball =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Metric

/-- **Integrability of the Biot–Savart integrand on a ball.**

For a time slice `ω · t` of the vorticity which is bounded by `M ≥ 0` and a.e. strongly
measurable, the integrand

  `a ↦ crossL (ω a t) (kf (x - a))`

is Bochner-integrable on the ball `B(0,ρ)`.

The singularity of the kernel `kf` sits at `a = x` and is of size `‖x - a‖⁻²`; in dimension `3`
the exponent `2` is below the integrability threshold `3`, so the singular weight is locally
integrable.  Concretely, the norm of the integrand is dominated by the *integrable* weight
`M ‖kf (x - ·)‖` (`Work.CoreResiduals.BiotSavart.integrableOn_kf_sub`), which gives the claim
through the domination criterion `Work.CoreResiduals.BiotSavart.integrableOn_of_norm_le_ball`;
measurability is `Work.CoreResiduals.BiotSavart.aestronglyMeasurable_crossL_kf`. -/
theorem integrableOn_crossL_kf_ball {ω : Work.LWP.R3 → ℝ → Work.LWP.R3}
    {M ρ : ℝ} {x : Work.LWP.R3} {t : ℝ}
    (hM : 0 ≤ M) (hbdd : ∀ y : Work.LWP.R3, ‖ω y t‖ ≤ M)
    (hmeas : MeasureTheory.AEStronglyMeasurable (ω · t) MeasureTheory.volume) :
    MeasureTheory.IntegrableOn
      (fun a : Work.LWP.R3 =>
        Work.StabilityFar.Decay.crossL (ω a t) (Work.StabilityFar.Decay.kf (x - a)))
      (Metric.ball (0 : Work.LWP.R3) ρ) MeasureTheory.volume := by
  -- Measurability of the integrand.
  have hmeas' : MeasureTheory.AEStronglyMeasurable
      (fun a : Work.LWP.R3 =>
        Work.StabilityFar.Decay.crossL (ω a t) (Work.StabilityFar.Decay.kf (x - a)))
      MeasureTheory.volume :=
    aestronglyMeasurable_crossL_kf hmeas x
  -- The dominating weight `M ‖kf (x - ·)‖` is integrable on the ball.
  have hdom : MeasureTheory.IntegrableOn
      (fun a : Work.LWP.R3 => M * ‖Work.StabilityFar.Decay.kf (x - a)‖)
      (Metric.ball (0 : Work.LWP.R3) ρ) MeasureTheory.volume :=
    ((integrableOn_kf_sub x ρ).norm).const_mul M
  -- Pointwise domination by the weight.
  refine integrableOn_of_norm_le_ball hdom hmeas' (fun a _ => ?_)
  calc ‖Work.StabilityFar.Decay.crossL (ω a t) (Work.StabilityFar.Decay.kf (x - a))‖
      ≤ ‖Work.StabilityFar.Decay.crossL (ω a t)‖ * ‖Work.StabilityFar.Decay.kf (x - a)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖ω a t‖ * ‖Work.StabilityFar.Decay.kf (x - a)‖ :=
        mul_le_mul_of_nonneg_right (Work.StabilityFar.Decay.norm_crossL_le _) (norm_nonneg _)
    _ ≤ M * ‖Work.StabilityFar.Decay.kf (x - a)‖ :=
        mul_le_mul (hbdd a) le_rfl (norm_nonneg _) hM

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.setIntegral_norm_sub_rpow_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Set
open scoped ENNReal

/-- **Translation invariance of the set Lebesgue integral over an open ball.**  Replacing the
centre of a ball by a translate and the integration variable by its difference from the centre
does not change the `lintegral`:
`∫⁻_{B(c,r)} F (y - c) = ∫⁻_{B(0,r)} F`. -/
lemma lintegral_ball_sub_eq (c : Work.LWP.R3) (r : ℝ) (F : Work.LWP.R3 → ℝ≥0∞) :
    ∫⁻ y in Metric.ball c r, F (y - c) = ∫⁻ z in Metric.ball (0 : Work.LWP.R3) r, F z := by
  classical
  have hs : MeasurableSet (Metric.ball c r) := Metric.isOpen_ball.measurableSet
  have hs0 : MeasurableSet (Metric.ball (0 : Work.LWP.R3) r) := Metric.isOpen_ball.measurableSet
  have hmem : ∀ y : Work.LWP.R3, y ∈ Metric.ball c r ↔ y - c ∈ Metric.ball (0 : Work.LWP.R3) r := by
    intro y
    rw [Metric.mem_ball, Metric.mem_ball, dist_eq_norm, dist_eq_norm, sub_zero]
  rw [← lintegral_indicator hs (fun y => F (y - c))]
  have h1 : (fun y => (Metric.ball c r).indicator (fun y => F (y - c)) y)
      = fun y => (Metric.ball (0 : Work.LWP.R3) r).indicator F (y - c) := by
    funext y
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hy : y ∈ Metric.ball c r
    · simp [hy, (hmem y).mp hy]
    · have hy' : y - c ∉ Metric.ball (0 : Work.LWP.R3) r := fun h => hy ((hmem y).mpr h)
      simp [hy, hy']
  rw [h1, lintegral_sub_right_eq_self
    (fun z => (Metric.ball (0 : Work.LWP.R3) r).indicator F z) c]
  rw [lintegral_indicator hs0 F]

/-- **The near-singular Riesz-kernel estimate over a ball.**  For `R > 0`, `α < 1` and any centre
`x ∈ ℝ³`,
`∫_{B(0,R)} ‖x - a‖^{-2-α} da ≤ 4π (‖x‖ + R + 1)^{1-α} / (1 - α)`.

The ball `B(0,R)` is contained in the ball `B(x, ‖x‖+R+1)`; the integrand is a radial power of
the distance to its own singularity, whose integral over a ball is computed by
`lintegral_ball_norm_rpow` (`∫_{B(0,ρ)} ‖z‖^s = 4π ρ^{s+3}/(s+3)` for `s > -3`), together with
translation invariance `lintegral_ball_sub_eq`.  The conversion between the Bochner integral and
the `lintegral` uses `setIntegral_eq_lintegral_of_nonneg`. -/
theorem setIntegral_norm_sub_rpow_le {R α : ℝ} (hR : 0 < R) (hα1 : α < 1) (x : Work.LWP.R3) :
    ∫ a in Metric.closedBall (0 : Work.LWP.R3) R, ‖x - a‖ ^ (-2 - α)
      ≤ 4 * Real.pi * (‖x‖ + R + 1) ^ (1 - α) / (1 - α) := by
  have hs : (-3:ℝ) < -2 - α := by linarith
  have hpos : (0:ℝ) < ‖x‖ + R + 1 := by linarith [norm_nonneg x, hR]
  have hnn : ∀ a : Work.LWP.R3, 0 ≤ ‖x - a‖ ^ (-2 - α) :=
    fun a => Real.rpow_nonneg (norm_nonneg _) _
  have hmeas : AEStronglyMeasurable (fun a : Work.LWP.R3 => ‖x - a‖ ^ (-2 - α)) volume :=
    (show Measurable (fun a : Work.LWP.R3 => ‖x - a‖ ^ (-2 - α)) by
      measurability).aestronglyMeasurable
  have hCnn : 0 ≤ 4 * Real.pi * (‖x‖ + R + 1) ^ (1 - α) / (1 - α) := by
    apply div_nonneg <;> [positivity; linarith]
  have hlin : ∫⁻ a in Metric.closedBall (0 : Work.LWP.R3) R, ENNReal.ofReal (‖x - a‖ ^ (-2 - α))
      ≤ ENNReal.ofReal (4 * Real.pi * (‖x‖ + R + 1) ^ (1 - α) / (1 - α)) := by
    have hsub : Metric.closedBall (0 : Work.LWP.R3) R ⊆ Metric.ball x (‖x‖ + R + 1) := by
      intro a ha
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at ha
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖a - x‖ ≤ ‖a‖ + ‖x‖ := norm_sub_le a x
        _ ≤ R + ‖x‖ := by linarith
        _ < ‖x‖ + R + 1 := by linarith
    calc ∫⁻ a in Metric.closedBall (0 : Work.LWP.R3) R, ENNReal.ofReal (‖x - a‖ ^ (-2 - α))
        ≤ ∫⁻ a in Metric.ball x (‖x‖ + R + 1), ENNReal.ofReal (‖x - a‖ ^ (-2 - α)) :=
          lintegral_mono_set hsub
      _ = ∫⁻ a in Metric.ball x (‖x‖ + R + 1), ENNReal.ofReal (‖a - x‖ ^ (-2 - α)) := by
          apply lintegral_congr; intro a; rw [norm_sub_rev]
      _ = ∫⁻ z in Metric.ball (0 : Work.LWP.R3) (‖x‖ + R + 1),
            ENNReal.ofReal (‖z‖ ^ (-2 - α)) :=
          lintegral_ball_sub_eq x (‖x‖ + R + 1) (fun z => ENNReal.ofReal (‖z‖ ^ (-2 - α)))
      _ = ENNReal.ofReal (4 * Real.pi * (‖x‖ + R + 1) ^ ((-2 - α) + 3) / ((-2 - α) + 3)) :=
          lintegral_ball_norm_rpow (-2 - α) hs (‖x‖ + R + 1) hpos
      _ = ENNReal.ofReal (4 * Real.pi * (‖x‖ + R + 1) ^ (1 - α) / (1 - α)) := by
          have h : (-2 : ℝ) - α + 3 = 1 - α := by ring
          rw [h]
  rw [setIntegral_eq_lintegral_of_nonneg Metric.isClosed_closedBall.measurableSet hmeas hnn]
  exact le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin)
    (le_of_eq (ENNReal.toReal_ofReal hCnn))

end Work.CoreResiduals.BiotSavart
end
