import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.CoreResiduals.BiotSavart.IntegrandDefs
import Submission.Work.CoreResiduals.BiotSavart.integral_ball_sub_norm_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart.Bundle

open MeasureTheory Set Metric Filter

/-! ## Two elementary radial integrability facts

`integral_ball_sub_norm_rpow` computes `∫_{B(z,r)} ‖· - z‖^p` for `p > -3` in terms of its
(positive) value; since a non-integrable function has zero integral, that value being positive
*is* the statement that the radial power is Bochner integrable on the ball.  From that we read off
the monotone-set version used to peel the near-field integral. -/

private lemma integrableOn_rpow_norm_ball (z : Work.LWP.R3) {p r : ℝ} (hp : -3 < p) (hr : 0 < r) :
    IntegrableOn (fun a : Work.LWP.R3 => (‖a - z‖ : ℝ) ^ p) (Metric.ball z r) volume := by
  have hval := integral_ball_sub_norm_rpow z r p hp hr
  by_contra hcon
  have h0 : ∫ a in Metric.ball z r, (‖a - z‖ : ℝ) ^ p = 0 := integral_undef hcon
  rw [hval] at h0
  have hpos : 0 < 4 * Real.pi * r ^ (p + 3) / (p + 3) := by
    apply div_pos
    · exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (Real.rpow_pos_of_pos hr _)
    · linarith
  exact absurd h0 hpos.ne'

private lemma setIntegral_rpow_norm_le_of_subset_ball (z : Work.LWP.R3) {p r : ℝ} (hp : -3 < p)
    (hr : 0 < r) {s : Set Work.LWP.R3} (hs : s ⊆ Metric.ball z r) :
    ∫ a in s, (‖a - z‖ : ℝ) ^ p ≤ 4 * Real.pi * r ^ (p + 3) / (p + 3) := by
  have hInt : IntegrableOn (fun a : Work.LWP.R3 => (‖a - z‖ : ℝ) ^ p) (Metric.ball z r) volume :=
    integrableOn_rpow_norm_ball z hp hr
  have hmono := setIntegral_mono_set (μ := volume) hInt
      (Filter.Eventually.of_forall (fun a => Real.rpow_nonneg (norm_nonneg _) p))
      (Filter.Eventually.of_forall (fun a ha => hs ha))
  rw [integral_ball_sub_norm_rpow z r p hp hr] at hmono
  exact hmono

/-- **The near-field piece of the Schauder difference estimate.**

Let `0 < α`, `C ≥ 0`, and let `g` be `α`-Hölder with constant `C`.  For `0 < δ` and `‖x - y‖ ≤ δ`,
the integral over the overlap `B(0,ρ) ∩ B(y,2δ)` of the difference of the two derivative
integrands `bsIntegrand g x - bsIntegrand g y` is bounded by
`4 C (4π/α) ((3δ)^α + (2δ)^α)`.

Indeed `B(0,ρ) ∩ B(y,2δ) ⊆ B(x,3δ)`, and each peeled integrand obeys
`‖bsIntegrand g z a‖ ≤ 4 C ‖z - a‖^{α-3}` (`norm_bsIntegrand_le`), whose integral over `B(z,r)` is
`4C·4π r^α/α` (`integral_ball_sub_norm_rpow`). -/
theorem norm_setIntegral_bsIntegrand_diff_inter_ball_le {α C δ ρ : ℝ} (hα : 0 < α) (hC : 0 ≤ C)
    {g : Work.LWP.R3 → Work.LWP.R3}
    (hhold : ∀ a b : Work.LWP.R3, ‖g a - g b‖ ≤ C * ‖a - b‖ ^ α)
    {x y : Work.LWP.R3} (hδ : 0 < δ) (hxy : ‖x - y‖ ≤ δ) :
    ‖∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball y (2 * δ)),
        (Work.CoreResiduals.BiotSavart.bsIntegrand g x a
          - Work.CoreResiduals.BiotSavart.bsIntegrand g y a)‖
      ≤ 4 * C * (4 * Real.pi / α) * ((3 * δ) ^ α + (2 * δ) ^ α) := by
  have h3δ : 0 < 3 * δ := by linarith
  have h2δ : 0 < 2 * δ := by linarith
  have hp : (-3 : ℝ) < α - 3 := by linarith
  -- The overlap disc sits inside both `B(x, 3δ)` and `B(y, 2δ)`.
  have hSx : (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball y (2 * δ))
      ⊆ Metric.ball x (3 * δ) := by
    intro a ha
    rw [Set.mem_inter_iff, Metric.mem_ball, Metric.mem_ball] at ha
    rw [Metric.mem_ball]
    have h2 : dist y x ≤ δ := by rw [dist_comm, dist_eq_norm]; exact hxy
    calc dist a x ≤ dist a y + dist y x := dist_triangle a y x
      _ < 2 * δ + δ := add_lt_add_of_lt_of_le ha.2 h2
      _ = 3 * δ := by ring
  have hSy : (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball y (2 * δ))
      ⊆ Metric.ball y (2 * δ) := Set.inter_subset_right
  -- The two dominating radial weights are integrable on the overlap disc.
  have hIx : Integrable (fun a : Work.LWP.R3 => 4 * C * (‖a - x‖ : ℝ) ^ (α - 3))
      (volume.restrict ((Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball y (2 * δ)))) :=
    ((integrableOn_rpow_norm_ball x hp h3δ).mono_set hSx).const_mul (4 * C)
  have hIy : Integrable (fun a : Work.LWP.R3 => 4 * C * (‖a - y‖ : ℝ) ^ (α - 3))
      (volume.restrict ((Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball y (2 * δ)))) :=
    ((integrableOn_rpow_norm_ball y hp h2δ).mono_set hSy).const_mul (4 * C)
  have hg : Integrable (fun a : Work.LWP.R3 =>
      4 * C * (‖a - x‖ : ℝ) ^ (α - 3) + 4 * C * (‖a - y‖ : ℝ) ^ (α - 3))
      (volume.restrict ((Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball y (2 * δ)))) :=
    hIx.add hIy
  -- `norm_bsIntegrand_le` for each peeled integrand and `norm_sub_le`.
  have hpt : ∀ a : Work.LWP.R3,
      ‖Work.CoreResiduals.BiotSavart.bsIntegrand g x a
        - Work.CoreResiduals.BiotSavart.bsIntegrand g y a‖
      ≤ 4 * C * (‖a - x‖ : ℝ) ^ (α - 3) + 4 * C * (‖a - y‖ : ℝ) ^ (α - 3) := by
    intro a
    have h1 := Work.CoreResiduals.BiotSavart.norm_bsIntegrand_le hC hhold x a
    have h2 := Work.CoreResiduals.BiotSavart.norm_bsIntegrand_le hC hhold y a
    rw [norm_sub_rev x a] at h1
    rw [norm_sub_rev y a] at h2
    calc ‖Work.CoreResiduals.BiotSavart.bsIntegrand g x a
          - Work.CoreResiduals.BiotSavart.bsIntegrand g y a‖
        ≤ ‖Work.CoreResiduals.BiotSavart.bsIntegrand g x a‖
          + ‖Work.CoreResiduals.BiotSavart.bsIntegrand g y a‖ := norm_sub_le _ _
      _ ≤ 4 * C * (‖a - x‖ : ℝ) ^ (α - 3) + 4 * C * (‖a - y‖ : ℝ) ^ (α - 3) :=
          add_le_add h1 h2
  have hmain := MeasureTheory.norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall hpt)
  -- The radial weights, evaluated over the two balls by `integral_ball_sub_norm_rpow`.
  have hbx := setIntegral_rpow_norm_le_of_subset_ball x (p := α - 3) (r := 3 * δ) hp h3δ hSx
  rw [show α - 3 + 3 = α by ring] at hbx
  have hby := setIntegral_rpow_norm_le_of_subset_ball y (p := α - 3) (r := 2 * δ) hp h2δ hSy
  rw [show α - 3 + 3 = α by ring] at hby
  have h4C : (0:ℝ) ≤ 4 * C := by positivity
  have hsplit : ∫ a, (4 * C * (‖a - x‖ : ℝ) ^ (α - 3) + 4 * C * (‖a - y‖ : ℝ) ^ (α - 3))
        ∂(volume.restrict ((Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball y (2 * δ))))
      = 4 * C * (∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball y (2 * δ)),
          (‖a - x‖ : ℝ) ^ (α - 3))
        + 4 * C * (∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball y (2 * δ)),
          (‖a - y‖ : ℝ) ^ (α - 3)) := by
    rw [integral_add hIx hIy, integral_const_mul, integral_const_mul]
  calc ‖∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball y (2 * δ)),
        (Work.CoreResiduals.BiotSavart.bsIntegrand g x a
          - Work.CoreResiduals.BiotSavart.bsIntegrand g y a)‖
      ≤ ∫ a, (4 * C * (‖a - x‖ : ℝ) ^ (α - 3) + 4 * C * (‖a - y‖ : ℝ) ^ (α - 3))
          ∂(volume.restrict ((Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball y (2 * δ)))) :=
        hmain
    _ = 4 * C * (∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball y (2 * δ)),
          (‖a - x‖ : ℝ) ^ (α - 3))
        + 4 * C * (∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball y (2 * δ)),
          (‖a - y‖ : ℝ) ^ (α - 3)) := hsplit
    _ ≤ 4 * C * (4 * Real.pi * (3 * δ) ^ α / α) + 4 * C * (4 * Real.pi * (2 * δ) ^ α / α) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hbx h4C) (mul_le_mul_of_nonneg_left hby h4C)
    _ = 4 * C * (4 * Real.pi / α) * ((3 * δ) ^ α + (2 * δ) ^ α) := by
        have hαne : α ≠ 0 := ne_of_gt hα
        field_simp

end Work.CoreResiduals.BiotSavart.Bundle
