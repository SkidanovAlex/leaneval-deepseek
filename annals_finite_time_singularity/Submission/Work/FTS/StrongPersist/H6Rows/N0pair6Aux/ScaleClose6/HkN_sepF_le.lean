import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Construction.H4N_GammaTerm_le
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.T1Defs
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongPersist.L3Aux.acoef_gamCoef_slots_le
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_sq_integrableOn
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.StabilityFar.Decay.hasDerivAt_biotSavart
import Submission.Work.StabilityFar.Decay.hasDerivAt_bsK
import Submission.Work.StabilityFar.Decay.norm_kDerivCLM_sub_le
import Submission.Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall
import Submission.Work.StabilityFar.Holder.holderOnWith_of_norm_le
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.Bundle.norm_setIntegral_bsIntegrand_diff_inter_ball_le =====
section

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
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.Bundle.norm_setIntegral_crossL_kDerivCLM_sub_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

namespace Work.CoreResiduals.BiotSavart.Bundle

open MeasureTheory Set
open Work.StabilityFar.Decay (crossL kDerivCLM)

/-- **The far-field piece of the Schauder difference estimate.**

Let `0 < α < 1`, `C ≥ 0`, let `g` be `α`-Hölder with constant `C`, and let `0 < δ`, `‖x - y‖ ≤ δ`.
Then the integral over `B(0,ρ) \ B(y,2δ)` of `(crossL (g a - g y)).comp (kDerivCLM (x-a) - kDerivCLM (y-a))`
is bounded by `1024 C δ (4π (2δ)^{α-1}/(1-α))`.

On `B(0,ρ) \ B(y,2δ)` one has `‖a - y‖ ≥ 2δ`, so `‖x - a‖, ‖y - a‖ ≥ ‖a-y‖/2`; hence
`‖crossL (g a - g y)‖ ≤ C ‖a-y‖^α` and `‖kDerivCLM (x-a) - kDerivCLM (y-a)‖ ≤ 1024δ/‖a-y‖⁴`
(`norm_kDerivCLM_sub_le_of_two_mul_le`), giving the pointwise bound
`1024 C δ ‖a-y‖^{α-4}`.  The exponent `α - 4 < -3` makes this integrable over the complement of
`B(y,2δ)` with integral `4π (2δ)^{α-1}/(1-α)` (`integral_compl_ball_norm_rpow`). -/
theorem norm_setIntegral_crossL_kDerivCLM_sub_le {α C δ ρ : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hC : 0 ≤ C) {g : Work.LWP.R3 → Work.LWP.R3}
    (hhold : ∀ a b : Work.LWP.R3, ‖g a - g b‖ ≤ C * ‖a - b‖ ^ α)
    {x y : Work.LWP.R3} (hδ : 0 < δ) (hxy : ‖x - y‖ ≤ δ) :
    ‖∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball y (2 * δ)),
        (Work.StabilityFar.Decay.crossL (g a - g y)).comp
          (Work.StabilityFar.Decay.kDerivCLM (x - a)
            - Work.StabilityFar.Decay.kDerivCLM (y - a))‖
      ≤ 1024 * C * δ * (4 * Real.pi * (2 * δ) ^ (α - 1) / (1 - α)) := by
  have hα4 : α - 4 < -3 := by linarith
  have h2δ : 0 < 2 * δ := by linarith
  -- The translation `a ↦ a + y` is a measure-preserving measurable embedding of `ℝ³`.
  have hmp : MeasurePreserving (fun z : Work.LWP.R3 => z + y) volume volume :=
    measurePreserving_add_right volume y
  have hemb : MeasurableEmbedding (fun z : Work.LWP.R3 => z + y) := by
    have h := (MeasurableEquiv.addRight y).measurableEmbedding
    convert h using 1
    ext z; simp [MeasurableEquiv.addRight]
  -- Substitution `a = z + y` turns the exterior of `B(y,2δ)` into the exterior of `B(0,2δ)`.
  have hshift : ∫ a in (Metric.ball y (2 * δ))ᶜ, (‖a - y‖ : ℝ) ^ (α - 4)
      = ∫ z in (Metric.ball (0 : Work.LWP.R3) (2 * δ))ᶜ, (‖z‖ : ℝ) ^ (α - 4) := by
    have hset : (fun z : Work.LWP.R3 => z + y) '' (Metric.ball (0 : Work.LWP.R3) (2 * δ))ᶜ
        = (Metric.ball y (2 * δ))ᶜ := by
      ext a
      simp only [Set.mem_image, Set.mem_compl_iff, Metric.mem_ball, not_lt]
      constructor
      · rintro ⟨z, hz, rfl⟩
        rw [dist_eq_norm]; simpa using hz
      · intro ha
        refine ⟨a - y, ?_, by abel⟩
        simpa [dist_eq_norm, sub_zero] using ha
    have h := hmp.setIntegral_image_emb hemb (fun a : Work.LWP.R3 => (‖a - y‖ : ℝ) ^ (α - 4))
      (Metric.ball (0 : Work.LWP.R3) (2 * δ))ᶜ
    rw [hset] at h
    simpa using h
  have hpre : (fun z : Work.LWP.R3 => z + y) ⁻¹' (Metric.ball y (2 * δ))ᶜ
      = (Metric.ball (0 : Work.LWP.R3) (2 * δ))ᶜ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_compl_iff, Metric.mem_ball, not_lt, dist_eq_norm, sub_zero,
      add_sub_cancel_right]
  -- Integrability of the radial weight on the exterior of the small ball.
  have hint_radial : IntegrableOn (fun a : Work.LWP.R3 => (‖a - y‖ : ℝ) ^ (α - 4))
      (Metric.ball y (2 * δ))ᶜ volume := by
    have h := (hmp.integrableOn_comp_preimage hemb
      (f := fun a : Work.LWP.R3 => (‖a - y‖ : ℝ) ^ (α - 4))
      (s := (Metric.ball y (2 * δ))ᶜ))
    rw [hpre] at h
    refine h.mp ?_
    show IntegrableOn (fun z : Work.LWP.R3 => (‖(z + y) - y‖ : ℝ) ^ (α - 4))
      (Metric.ball (0 : Work.LWP.R3) (2 * δ))ᶜ volume
    simpa using
      Work.CoreResiduals.BiotSavart.integrableOn_compl_ball_norm_rpow (α - 4) hα4 (2 * δ) h2δ
  set s : Set Work.LWP.R3 := (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball y (2 * δ))
    with hsdef
  set t : Set Work.LWP.R3 := (Metric.ball y (2 * δ))ᶜ with htdef
  have hsmeas : MeasurableSet s := measurableSet_ball.diff measurableSet_ball
  have hst : s ⊆ t := by intro a ha; exact ha.2
  set G : Work.LWP.R3 → ℝ := fun a => 1024 * C * δ * (‖a - y‖ : ℝ) ^ (α - 4) with hGdef
  have hIntG : IntegrableOn G t volume := by
    rw [hGdef]
    exact MeasureTheory.Integrable.const_mul hint_radial (1024 * C * δ)
  have hIntGs : IntegrableOn G s volume := hIntG.mono_set hst
  -- The pointwise bound on the region of integration.
  have hpt : ∀ a ∈ s, ‖(crossL (g a - g y)).comp (kDerivCLM (x - a) - kDerivCLM (y - a))‖
      ≤ G a := by
    intro a ha
    have ha' : 2 * δ ≤ ‖a - y‖ := by
      have h : a ∉ Metric.ball y (2 * δ) := ha.2
      rw [Metric.mem_ball, not_lt, dist_eq_norm] at h
      exact h
    rw [hGdef]
    set r : ℝ := ‖a - y‖ with hrdef
    have hr : 0 < r := by rw [hrdef]; linarith
    have h1 : ‖crossL (g a - g y)‖ ≤ C * r ^ α := by
      refine le_trans (Work.StabilityFar.Decay.norm_crossL_le _) ?_
      rw [hrdef]; simpa using hhold a y
    have h2 : ‖kDerivCLM (x - a) - kDerivCLM (y - a)‖ ≤ 1024 * δ / r ^ 4 := by
      refine norm_kDerivCLM_sub_le_of_two_mul_le hδ hxy ?_
      rw [← hrdef]; exact ha'
    have hkey : 1024 * C * δ * r ^ (α - 4) = (C * r ^ α) * (1024 * δ / r ^ 4) := by
      rw [Real.rpow_sub hr α 4]
      rw [show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      field_simp
    calc ‖(crossL (g a - g y)).comp (kDerivCLM (x - a) - kDerivCLM (y - a))‖
        ≤ ‖crossL (g a - g y)‖ * ‖kDerivCLM (x - a) - kDerivCLM (y - a)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (C * r ^ α) * (1024 * δ / r ^ 4) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = 1024 * C * δ * r ^ (α - 4) := hkey.symm
      _ = 1024 * C * δ * ‖a - y‖ ^ (α - 4) := by rw [hrdef]
  calc ‖∫ a in s, (crossL (g a - g y)).comp (kDerivCLM (x - a) - kDerivCLM (y - a))‖
      ≤ ∫ a in s, G a :=
        MeasureTheory.norm_integral_le_of_norm_le (μ := volume.restrict s) hIntGs
          (by filter_upwards [ae_restrict_mem hsmeas] with a ha; exact hpt a ha)
    _ ≤ ∫ a in t, G a :=
        setIntegral_mono_set hIntG
          (Filter.Eventually.of_forall (fun a => by
            rw [hGdef]
            exact mul_nonneg (by positivity) (Real.rpow_nonneg (norm_nonneg _) _)))
          (Filter.Eventually.of_forall (fun a ha => hst ha))
    _ = 1024 * C * δ * ∫ a in t, (‖a - y‖ : ℝ) ^ (α - 4) := by
        rw [hGdef]; rw [MeasureTheory.integral_const_mul]
    _ = 1024 * C * δ * (4 * Real.pi * (2 * δ) ^ (α - 1) / (1 - α)) := by
        congr 1
        rw [htdef, hshift,
          Work.CoreResiduals.BiotSavart.integral_compl_ball_norm_rpow (α - 4) hα4 (2 * δ) h2δ]
        rw [show -((α : ℝ) - 4 + 3) = 1 - α by ring]
        rw [show α - 4 + 3 = α - 1 by ring]

end Work.CoreResiduals.BiotSavart.Bundle
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.continuousAt_bsIntegrand_param =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Metric Filter Topology
open scoped Topology

set_option autoImplicit false

namespace Work.CoreResiduals.BiotSavart

open Work.StabilityFar.Decay

/-- **Joint continuity of the parametrised Biot–Savart derivative integrand.**

For a fixed `a ≠ x₀`, the map `(x,t) ↦ bsIntegrand (ω(·,t)) x a` is continuous at `(x₀,t₀)`,
using joint continuity of `ω` at `(x₀,t₀)`, continuity in `t` at `t₀` for each fixed `a`, and
continuity of `crossL` and of `kDerivCLM` away from the diagonal. -/
theorem continuousAt_bsIntegrand_param {ω : Work.LWP.R3 → ℝ → Work.LWP.R3}
    {x₀ : Work.LWP.R3} {t₀ : ℝ}
    (hjoint : ContinuousAt (fun q : Work.LWP.R3 × ℝ => ω q.1 q.2) (x₀, t₀))
    (htcont : ∀ a : Work.LWP.R3, ContinuousAt (fun t : ℝ => ω a t) t₀)
    {a : Work.LWP.R3} (ha : a ≠ x₀) :
    ContinuousAt (fun q : Work.LWP.R3 × ℝ =>
      bsIntegrand (fun y => ω y q.2) q.1 a) (x₀, t₀) := by
  have hOa : ContinuousAt (fun q : Work.LWP.R3 × ℝ => ω a q.2) (x₀, t₀) :=
    (htcont a).comp continuous_snd.continuousAt
  have h1 : ContinuousAt (fun q : Work.LWP.R3 × ℝ => crossL (ω a q.2 - ω q.1 q.2)) (x₀, t₀) :=
    continuous_crossL.continuousAt.comp (hOa.sub hjoint)
  have hsub : ContinuousAt (fun q : Work.LWP.R3 × ℝ => q.1 - a) (x₀, t₀) :=
    continuous_fst.continuousAt.sub continuousAt_const
  have h2 : ContinuousAt (fun q : Work.LWP.R3 × ℝ => kDerivCLM (q.1 - a)) (x₀, t₀) :=
    ContinuousAt.comp (x := (x₀, t₀)) (f := fun q : Work.LWP.R3 × ℝ => q.1 - a) (g := kDerivCLM)
      (continuousAt_kDerivCLM (b := x₀ - a) (sub_ne_zero.mpr (Ne.symm ha))) hsub
  have hcomp := h1.clm_comp h2
  simpa only [bsIntegrand] using hcomp

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.continuous_bsDerivCLM =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Metric Filter Topology
open scoped Topology

set_option autoImplicit false

namespace Work.CoreResiduals.BiotSavart

open Work.StabilityFar.Decay

/-! ## Elementary consequences of the Hölder hypothesis -/

/-- A `c`-Hölder field with `c > 0` and nonnegative Hölder constant is continuous. -/
theorem continuous_of_holder {ω : R3 → R3} {C c : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hhold : ∀ a b : R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c) : Continuous ω := by
  rw [continuous_iff_continuousAt]
  intro x
  change Tendsto ω (𝓝 x) (𝓝 (ω x))
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (f := fun y : R3 => dist (ω y) (ω x))
    (g := fun y : R3 => C * ‖y - x‖ ^ c) (fun y : R3 => dist_nonneg) (fun y => ?_) ?_
  · simpa only [dist_eq_norm] using hhold y x
  · have h1 : Tendsto (fun y : R3 => ‖y - x‖) (𝓝 x) (𝓝 0) := by
      have hsub : ContinuousAt (fun y : R3 => y - x) x := continuousAt_id.sub continuousAt_const
      have h : Tendsto (fun y : R3 => ‖y - x‖) (𝓝 x) (𝓝 ((fun y : R3 => ‖y - x‖) x)) :=
        (continuous_norm.continuousAt.comp hsub).tendsto
      simpa using h
    have h2 : Tendsto (fun y : R3 => ‖y - x‖ ^ c) (𝓝 x) (𝓝 ((0 : ℝ) ^ c)) :=
      h1.rpow_const (Or.inr hc.le)
    rw [Real.zero_rpow hc.ne'] at h2
    have h3 := h2.const_mul C
    simpa using h3

/-- A point `a` outside the ball `B(x₀,Δ)` is at distance at least `Δ/2` from any point of
`B(x₀,Δ/2)`. -/
lemma le_norm_sub_of_notMem_ball {x₀ x a : R3} {Δ : ℝ} (hx : ‖x - x₀‖ ≤ Δ / 2)
    (ha : a ∉ Metric.ball x₀ Δ) : Δ / 2 ≤ ‖x - a‖ := by
  have h1 : Δ ≤ ‖a - x₀‖ := by
    rw [Metric.mem_ball, not_lt, dist_eq_norm] at ha
    simpa only [norm_sub_rev] using ha
  have h2 : ‖a - x₀‖ ≤ ‖a - x‖ + ‖x - x₀‖ := by
    have heq : a - x₀ = (a - x) + (x - x₀) := by abel
    rw [heq]
    exact norm_add_le _ _
  calc Δ / 2 ≤ ‖a - x₀‖ - ‖x - x₀‖ := by linarith
    _ ≤ ‖a - x‖ := by linarith
    _ = ‖x - a‖ := norm_sub_rev _ _

/-- Membership in `B(x₀,Δ/2)` in terms of the norm. -/
lemma norm_sub_le_of_mem_ball {x₀ x : R3} {Δ : ℝ} (hx : x ∈ Metric.ball x₀ (Δ / 2)) :
    ‖x - x₀‖ ≤ Δ / 2 := by
  rw [Metric.mem_ball, dist_eq_norm] at hx
  exact le_of_lt hx

/-- A point of `B(x₀,Δ/2)` has norm at most `‖x₀‖ + 1` when `Δ ≤ 2`. -/
lemma norm_le_of_mem_ball_half {x₀ x : R3} {Δ : ℝ} (hΔ2 : Δ ≤ 2) (hx : ‖x - x₀‖ ≤ Δ / 2) :
    ‖x‖ ≤ ‖x₀‖ + 1 := by
  have h := norm_add_le (x - x₀) x₀
  rw [sub_add_cancel] at h
  calc ‖x‖ ≤ ‖x - x₀‖ + ‖x₀‖ := h
    _ ≤ ‖x₀‖ + 1 := by linarith

/-- The ball `B(x₀,Δ)` is contained in `B(x,3Δ/2)` for `x ∈ B(x₀,Δ/2)`. -/
lemma ball_subset_ball_three_halves {x₀ x : R3} {Δ : ℝ} (hx : ‖x - x₀‖ ≤ Δ / 2) :
    Metric.ball x₀ Δ ⊆ Metric.ball x (3 * Δ / 2) := by
  intro a ha
  rw [Metric.mem_ball] at ha ⊢
  have h2 : dist x₀ x ≤ Δ / 2 := by simpa only [dist_eq_norm, norm_sub_rev] using hx
  have h3 := dist_triangle a x₀ x
  linarith

/-- `B(0,ρ) ∩ B(x₀,Δ) ⊆ B(x,3Δ/2)` for `x ∈ B(x₀,Δ/2)`. -/
lemma inter_ball_subset_ball_three_halves {x₀ x : R3} {Δ ρ : ℝ}
    (hx : ‖x - x₀‖ ≤ Δ / 2) :
    (Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ) ⊆ Metric.ball x (3 * Δ / 2) :=
  subset_trans Set.inter_subset_right (ball_subset_ball_three_halves hx)

/-! ## Integrability of the singular kernel and of the two pieces of the integral -/

/-- `a ↦ ‖a - x‖ ^ (c - 3)` is integrable on `B(x,R)` when `c > 0`. -/
theorem integrableOn_norm_sub_rpow_ball (x : R3) {c R : ℝ} (hc : 0 < c) (hR : 0 < R) :
    IntegrableOn (fun a : R3 => (‖a - x‖ : ℝ) ^ (c - 3)) (Metric.ball x R) volume := by
  have hΘ : -3 < c - 3 := by linarith
  have hval := integral_ball_sub_norm_rpow x R (c - 3) hΘ hR
  have hpos : 0 < 4 * Real.pi * R ^ ((c - 3) + 3) / ((c - 3) + 3) := by
    rw [show (c - 3) + 3 = c from by ring]
    positivity
  by_contra hcon
  have h0 := integral_undef hcon
  rw [hval] at h0
  exact absurd h0 (ne_of_gt hpos)

/-- The *inner* piece of the integrand is integrable: on `B(0,ρ) ∩ B(x₀,Δ)` it is dominated by
the integrable singular kernel `4C‖· - x‖^{c-3}`. -/
theorem integrableOn_bsIntegrand_inter {ω : R3 → R3} {C c : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hhold : ∀ a b : R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c)
    (x₀ : R3) {Δ ρ : ℝ} (hΔ : 0 < Δ) {x : R3} (hx : ‖x - x₀‖ ≤ Δ / 2) :
    IntegrableOn (bsIntegrand ω x) ((Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ)) volume := by
  have hω : Continuous ω := continuous_of_holder hc hC hhold
  have h3Δ : 0 < 3 * Δ / 2 := by linarith
  have hInt : IntegrableOn (fun a : R3 => 4 * C * (‖a - x‖ : ℝ) ^ (c - 3))
      ((Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ)) volume :=
    ((integrableOn_norm_sub_rpow_ball x hc h3Δ).mono_set
      (inter_ball_subset_ball_three_halves hx)).const_mul (4 * C)
  refine Integrable.mono' hInt ((aestronglyMeasurable_bsIntegrand hω x).mono_measure
    Measure.restrict_le_self) (Filter.Eventually.of_forall fun a => ?_)
  simpa only [norm_sub_rev] using norm_bsIntegrand_le hC hhold x a

/-- **Weighted domination of the outer integrand.**  For `x ∈ B(x₀,Δ/2)` and any `a`, the
truncated integrand `1_{B(0,ρ)\\B(x₀,Δ)} • bsIntegrand ω x` is dominated by the weight
`K(1 + ‖a‖^{c-3})` on `B(0,ρ)`. -/
lemma bsIntegrand_indicator_le {ω : R3 → R3} {C c K Δ ρ : ℝ} {x₀ x : R3} (hC : 0 ≤ C)
    (hhold : ∀ a b : R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c)
    (hK : ∀ x a : R3, ‖x‖ ≤ ‖x₀‖ + 1 → Δ / 2 ≤ ‖x - a‖ →
      4 * C * (‖x - a‖ : ℝ) ^ (c - 3) ≤ K * (1 + (‖a‖ : ℝ) ^ (c - 3)))
    (hK0 : 0 ≤ K) (hΔ2 : Δ ≤ 2) (hx : ‖x - x₀‖ ≤ Δ / 2) (a : R3) :
    ‖((Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ)).indicator (bsIntegrand ω x) a‖ ≤
      (Metric.ball (0 : R3) ρ).indicator (fun a : R3 => K * (1 + (‖a‖ : ℝ) ^ (c - 3))) a := by
  by_cases ha : a ∈ (Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ)
  · rw [Set.indicator_of_mem ha (bsIntegrand ω x),
      Set.indicator_of_mem ha.1 (fun a : R3 => K * (1 + (‖a‖ : ℝ) ^ (c - 3)))]
    exact le_trans (norm_bsIntegrand_le hC hhold x a)
      (hK x a (norm_le_of_mem_ball_half hΔ2 hx) (le_norm_sub_of_notMem_ball hx ha.2))
  · rw [Set.indicator_of_notMem ha (bsIntegrand ω x)]
    by_cases ha1 : a ∈ Metric.ball (0 : R3) ρ
    · rw [Set.indicator_of_mem ha1 (fun a : R3 => K * (1 + (‖a‖ : ℝ) ^ (c - 3)))]
      simpa using mul_nonneg hK0 (add_nonneg (by norm_num : (0 : ℝ) ≤ 1)
        (Real.rpow_nonneg (norm_nonneg a) (c - 3)))
    · rw [Set.indicator_of_notMem ha1 (fun a : R3 => K * (1 + (‖a‖ : ℝ) ^ (c - 3)))]
      simp

theorem integrableOn_bsIntegrand_ssub {ω : R3 → R3} {C c : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hhold : ∀ a b : R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c)
    (x₀ : R3) {Δ ρ : ℝ} (hΔ : 0 < Δ) (hΔ2 : Δ ≤ 2) {x : R3} (hx : ‖x - x₀‖ ≤ Δ / 2) :
    IntegrableOn (bsIntegrand ω x) ((Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ)) volume := by
  have hω : Continuous ω := continuous_of_holder hc hC hhold
  obtain ⟨K, hK0, hK⟩ := exists_rpow_dom_bound (C := C) (c := c) (X := ‖x₀‖ + 1) (δ := Δ / 2)
    hc hC (by positivity) (by linarith)
  have hdom : Integrable
      ((Metric.ball (0 : R3) ρ).indicator fun a : R3 => K * (1 + (‖a‖ : ℝ) ^ (c - 3))) volume :=
    (integrable_indicator_iff measurableSet_ball).mpr
      ((integrableOn_one_add_norm_rpow_ball (c - 3) ρ (by linarith)).const_mul K)
  have hmeas : MeasurableSet ((Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ)) :=
    measurableSet_ball.diff measurableSet_ball
  refine (integrable_indicator_iff hmeas).mp (Integrable.mono' hdom
    ((aestronglyMeasurable_bsIntegrand hω x).indicator hmeas)
    (Filter.Eventually.of_forall fun a => bsIntegrand_indicator_le (K := K) (ρ := ρ) (Δ := Δ)
      (x₀ := x₀) hC hhold hK hK0 hΔ2 hx a))

/-! ## The three estimates -/

/-- **The inner piece is small.**  Uniformly for `x ∈ B(x₀,Δ/2)`, the integral of the integrand
over `B(0,ρ) ∩ B(x₀,Δ)` is bounded by `4C(4π/c)(3Δ/2)^c`, which tends to `0` as `Δ → 0⁺`. -/
theorem norm_setIntegral_le_inner {ω : R3 → R3} {C c : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hhold : ∀ a b : R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c)
    (x₀ : R3) {Δ ρ : ℝ} (hΔ : 0 < Δ) {x : R3} (hx : ‖x - x₀‖ ≤ Δ / 2) :
    ‖∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ), bsIntegrand ω x a‖
      ≤ 4 * C * (4 * Real.pi / c) * (3 * Δ / 2) ^ c := by
  have h3Δ : 0 < 3 * Δ / 2 := by linarith
  have hsub := inter_ball_subset_ball_three_halves (ρ := ρ) hx
  have hIntX : IntegrableOn (fun a : R3 => 4 * C * (‖a - x‖ : ℝ) ^ (c - 3))
      (Metric.ball x (3 * Δ / 2)) volume :=
    (integrableOn_norm_sub_rpow_ball x hc h3Δ).const_mul (4 * C)
  have hint : IntegrableOn (fun a : R3 => 4 * C * (‖a - x‖ : ℝ) ^ (c - 3))
      ((Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ)) volume := hIntX.mono_set hsub
  calc ‖∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ), bsIntegrand ω x a‖
      ≤ ∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ),
          4 * C * (‖a - x‖ : ℝ) ^ (c - 3) :=
        MeasureTheory.norm_integral_le_of_norm_le hint
          (Filter.Eventually.of_forall fun a =>
            (by simpa only [norm_sub_rev] using norm_bsIntegrand_le hC hhold x a))
    _ ≤ ∫ a in Metric.ball x (3 * Δ / 2), 4 * C * (‖a - x‖ : ℝ) ^ (c - 3) :=
        setIntegral_mono_set hIntX
          (Filter.Eventually.of_forall fun a =>
            mul_nonneg (mul_nonneg (by norm_num) hC) (Real.rpow_nonneg (norm_nonneg _) _))
          (Filter.Eventually.of_forall fun a ha => hsub ha)
    _ = 4 * C * ∫ a in Metric.ball x (3 * Δ / 2), (‖a - x‖ : ℝ) ^ (c - 3) := by
        rw [integral_const_mul]
    _ = 4 * C * (4 * Real.pi * (3 * Δ / 2) ^ ((c - 3) + 3) / ((c - 3) + 3)) := by
        rw [integral_ball_sub_norm_rpow x (3 * Δ / 2) (c - 3) (by linarith) h3Δ]
    _ = 4 * C * (4 * Real.pi / c) * (3 * Δ / 2) ^ c := by
        rw [show (c - 3) + 3 = c from by ring]
        field_simp
        try ring

/-- **The outer piece is continuous.**  The integral of the integrand over `B(0,ρ) \ B(x₀,Δ)` is
continuous on `B(x₀,Δ/2)`: away from the singular diagonal it is dominated by an integrable
weight and it is continuous in the parameter at every point `a ≠ x`. -/
theorem continuousOn_outer {ω : R3 → R3} (hω : Continuous ω) {C c : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hhold : ∀ a b : R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c)
    (x₀ : R3) {Δ ρ : ℝ} (hΔ : 0 < Δ) (hΔ2 : Δ ≤ 2) :
    ContinuousOn (fun x : R3 => ∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ),
      bsIntegrand ω x a) (Metric.ball x₀ (Δ / 2)) := by
  obtain ⟨K, hK0, hK⟩ := exists_rpow_dom_bound (C := C) (c := c) (X := ‖x₀‖ + 1) (δ := Δ / 2)
    hc hC (by positivity) (by linarith)
  have hmeas : MeasurableSet ((Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ)) :=
    measurableSet_ball.diff measurableSet_ball
  have key : ContinuousOn (fun x : R3 => ∫ a,
      ((Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ)).indicator (bsIntegrand ω x) a)
      (Metric.ball x₀ (Δ / 2)) := by
    refine MeasureTheory.continuousOn_of_dominated
      (bound := fun a : R3 =>
        (Metric.ball (0 : R3) ρ).indicator (fun a : R3 => K * (1 + (‖a‖ : ℝ) ^ (c - 3))) a)
      (F := fun x a => ((Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ)).indicator
        (bsIntegrand ω x) a)
      (s := Metric.ball x₀ (Δ / 2)) ?_ ?_ ?_ ?_
    · intro x hx
      exact (aestronglyMeasurable_bsIntegrand hω x).indicator hmeas
    · intro x hx
      have hx' : ‖x - x₀‖ ≤ Δ / 2 := norm_sub_le_of_mem_ball hx
      exact Filter.Eventually.of_forall fun a =>
        bsIntegrand_indicator_le (K := K) (ρ := ρ) (Δ := Δ) (x₀ := x₀) hC hhold hK hK0 hΔ2 hx' a
    · exact (integrable_indicator_iff measurableSet_ball).mpr
        ((integrableOn_one_add_norm_rpow_ball (c - 3) ρ (by linarith)).const_mul K)
    · refine Filter.Eventually.of_forall fun a => ?_
      by_cases ha : a ∈ (Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ)
      · have hcont : ContinuousOn (fun x : R3 => bsIntegrand ω x a) (Metric.ball x₀ (Δ / 2)) := by
          intro x hx
          have hx' : ‖x - x₀‖ ≤ Δ / 2 := norm_sub_le_of_mem_ball hx
          have hne : a ≠ x := by
            intro h
            have h2 := le_norm_sub_of_notMem_ball hx' ha.2
            rw [h, sub_self, norm_zero] at h2
            linarith [hΔ]
          exact (continuousAt_bsIntegrand hω hne).continuousWithinAt
        exact ContinuousOn.congr hcont fun x hx => Set.indicator_of_mem ha (bsIntegrand ω x)
      · have hconst : ContinuousOn (fun _ : R3 => (0 : R3 →L[ℝ] R3)) (Metric.ball x₀ (Δ / 2)) :=
          continuousOn_const
        refine ContinuousOn.congr hconst fun x hx => ?_
        exact Set.indicator_of_notMem ha (bsIntegrand ω x)
  simpa only [MeasureTheory.integral_indicator hmeas] using key

/-- **The splitting identity.**  The integral over `B(0,ρ)` is the sum of its parts over
`B(0,ρ) ∩ B(x₀,Δ)` and `B(0,ρ) \ B(x₀,Δ)`. -/
theorem integral_split {ω : R3 → R3} {C c : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hhold : ∀ a b : R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c)
    (x₀ : R3) {Δ ρ : ℝ} (hΔ : 0 < Δ) (hΔ2 : Δ ≤ 2) {x : R3} (hx : ‖x - x₀‖ ≤ Δ / 2) :
    (∫ a in Metric.ball (0 : R3) ρ, bsIntegrand ω x a)
      = (∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ), bsIntegrand ω x a)
        + (∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ), bsIntegrand ω x a) := by
  have hdisj : Disjoint ((Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ))
      ((Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ)) := by
    rw [Set.disjoint_left]
    intro a ha hb
    exact hb.2 ha.2
  have hmeas : MeasurableSet ((Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ)) :=
    measurableSet_ball.diff measurableSet_ball
  have h1 : (∫ a in Metric.ball (0 : R3) ρ, bsIntegrand ω x a)
      = ∫ a in ((Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ))
          ∪ ((Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ)), bsIntegrand ω x a := by
    rw [Set.inter_union_sdiff]
  rw [h1]
  exact setIntegral_union hdisj hmeas (integrableOn_bsIntegrand_inter hc hC hhold x₀ hΔ hx)
    (integrableOn_bsIntegrand_ssub hc hC hhold x₀ hΔ hΔ2 hx)

/-! ## The main theorem -/

/-- **Continuity of the candidate derivative of the Biot–Savart field.**  For a `c`-Hölder
vorticity with `c > 0` and nonnegative Hölder constant, `x ↦ bsDerivCLM ω ρ x` is continuous. -/
theorem continuous_bsDerivCLM_of_nonneg {ω : R3 → R3} {C c : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hhold : ∀ a b : R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c) (ρ : ℝ) :
    Continuous (fun x => bsDerivCLM ω ρ x) := by
  have hω : Continuous ω := continuous_of_holder hc hC hhold
  have hshape : Continuous (fun x : R3 => (4 * Real.pi / 3) • crossL (ω x)) :=
    (continuous_crossL.comp hω).const_smul (4 * Real.pi / 3)
  rw [continuous_iff_continuousAt]
  intro x₀
  change ContinuousAt (fun x : R3 =>
    (∫ a in Metric.ball (0 : R3) ρ, bsIntegrand ω x a) + (4 * Real.pi / 3) • crossL (ω x)) x₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hε4 : (0 : ℝ) < ε / 4 := by linarith
  -- the modulus of the inner piece tends to `0`
  have hlim : ContinuousAt (fun Δ : ℝ => 4 * C * (4 * Real.pi / c) * (3 * Δ / 2) ^ c) 0 := by
    have hlin : ContinuousAt (fun Δ : ℝ => 3 * Δ / 2) 0 := by fun_prop
    have hrpow : ContinuousAt (fun t : ℝ => t ^ c) (3 * 0 / 2) := by
      simpa using Real.continuousAt_rpow_const (0 : ℝ) c (Or.inr hc.le)
    have h1 : ContinuousAt (fun Δ : ℝ => (3 * Δ / 2) ^ c) 0 :=
      (ContinuousAt.comp (x := (0 : ℝ)) (f := fun Δ : ℝ => 3 * Δ / 2)
        (g := fun t : ℝ => t ^ c) hrpow hlin)
    exact h1.const_mul _
  obtain ⟨r, hrpos, hr⟩ := Metric.continuousAt_iff.mp hlim (ε / 4) hε4
  set Δ : ℝ := min 1 (r / 2) with hΔdef
  have hΔpos : 0 < Δ := lt_min one_pos (by linarith)
  have hΔle1 : Δ ≤ 1 := min_le_left _ _
  have hΔle2 : Δ ≤ 2 := by linarith
  have hLnn : 0 ≤ 4 * C * (4 * Real.pi / c) * (3 * Δ / 2) ^ c :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC) (by positivity))
      (Real.rpow_nonneg (by positivity) _)
  have hΔsmall : 4 * C * (4 * Real.pi / c) * (3 * Δ / 2) ^ c < ε / 4 := by
    have hdist : dist Δ 0 < r := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hΔpos]
      exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have h0 : 4 * C * (4 * Real.pi / c) * (3 * 0 / 2) ^ c = 0 := by
      rw [show (3 * 0 / 2 : ℝ) = 0 from by norm_num, Real.zero_rpow hc.ne']
      ring
    have h := hr hdist
    rw [Real.dist_eq, h0, sub_zero, abs_of_nonneg hLnn] at h
    exact h
  -- the outer piece is continuous at `x₀`
  have hOutC : ContinuousOn (fun x : R3 =>
      ∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ), bsIntegrand ω x a)
      (Metric.ball x₀ (Δ / 2)) := continuousOn_outer hω hc hC hhold x₀ hΔpos hΔle2
  have hOutAt := hOutC.continuousAt (Metric.ball_mem_nhds x₀ (by linarith))
  obtain ⟨r₂, hr₂pos, hr₂⟩ := Metric.continuousAt_iff.mp hOutAt (ε / 4) hε4
  obtain ⟨r₃, hr₃pos, hr₃⟩ :=
    Metric.continuousAt_iff.mp (hshape.continuousAt (x := x₀)) (ε / 4) hε4
  refine ⟨min (Δ / 2) (min r₂ r₃), by positivity, fun x hx => ?_⟩
  have hxΔ : ‖x - x₀‖ ≤ Δ / 2 := by
    have h1 : dist x x₀ < Δ / 2 := lt_of_lt_of_le hx (min_le_left _ _)
    rw [dist_eq_norm] at h1
    exact le_of_lt h1
  have hx₂ : dist x x₀ < r₂ := lt_of_lt_of_le hx (le_trans (min_le_right _ _) (min_le_left _ _))
  have hx₃ : dist x x₀ < r₃ := lt_of_lt_of_le hx (le_trans (min_le_right _ _) (min_le_right _ _))
  have hInX := norm_setIntegral_le_inner (ρ := ρ) hc hC hhold x₀ hΔpos hxΔ
  have hInx₀ := norm_setIntegral_le_inner (ρ := ρ) (x := x₀) hc hC hhold x₀ hΔpos
    (by simp only [sub_self, norm_zero]; positivity)
  have hIx := integral_split (ρ := ρ) hc hC hhold x₀ hΔpos hΔle2 hxΔ
  have hIx₀ := integral_split (ρ := ρ) (x := x₀) hc hC hhold x₀ hΔpos hΔle2
    (by simp only [sub_self, norm_zero]; positivity)
  have hOut := hr₂ hx₂
  have hShape := hr₃ hx₃
  have hinner : ‖(∫ a in Metric.ball (0 : R3) ρ, bsIntegrand ω x a)
      - (∫ a in Metric.ball (0 : R3) ρ, bsIntegrand ω x₀ a)‖ < 3 * (ε / 4) := by
    rw [hIx, hIx₀]
    have hOutdiff : ‖(∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ), bsIntegrand ω x a)
        - (∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ), bsIntegrand ω x₀ a)‖
        < ε / 4 := by
      rw [← dist_eq_norm]
      exact hOut
    have hcombine : ((∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ), bsIntegrand ω x a)
          + (∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ), bsIntegrand ω x a))
        - ((∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ), bsIntegrand ω x₀ a)
          + (∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ), bsIntegrand ω x₀ a))
        = ((∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ), bsIntegrand ω x a)
            - (∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ), bsIntegrand ω x₀ a))
          + ((∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ), bsIntegrand ω x a)
            - (∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ), bsIntegrand ω x₀ a)) := by
      abel
    rw [hcombine]
    calc ‖((∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ), bsIntegrand ω x a)
              - (∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ), bsIntegrand ω x₀ a))
            + ((∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ), bsIntegrand ω x a)
              - (∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ), bsIntegrand ω x₀ a))‖
        ≤ ‖(∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ), bsIntegrand ω x a)
            - (∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ), bsIntegrand ω x₀ a)‖
          + ‖(∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ), bsIntegrand ω x a)
            - (∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball x₀ Δ), bsIntegrand ω x₀ a)‖ :=
          norm_add_le _ _
      _ ≤ (‖∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ), bsIntegrand ω x a‖
            + ‖∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ), bsIntegrand ω x₀ a‖)
          + ε / 4 := by
          have h2 := norm_sub_le
            (∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ), bsIntegrand ω x a)
            (∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball x₀ Δ), bsIntegrand ω x₀ a)
          linarith
      _ < 3 * (ε / 4) := by linarith
  have hshape' : ‖(4 * Real.pi / 3) • crossL (ω x)
      - (4 * Real.pi / 3) • crossL (ω x₀)‖ < ε / 4 := by
    rw [← dist_eq_norm]
    exact hShape
  calc dist ((∫ a in Metric.ball (0 : R3) ρ, bsIntegrand ω x a)
          + (4 * Real.pi / 3) • crossL (ω x))
        ((∫ a in Metric.ball (0 : R3) ρ, bsIntegrand ω x₀ a)
          + (4 * Real.pi / 3) • crossL (ω x₀))
      = ‖((∫ a in Metric.ball (0 : R3) ρ, bsIntegrand ω x a)
            + (4 * Real.pi / 3) • crossL (ω x))
          - ((∫ a in Metric.ball (0 : R3) ρ, bsIntegrand ω x₀ a)
            + (4 * Real.pi / 3) • crossL (ω x₀))‖ := dist_eq_norm _ _
    _ ≤ ‖(∫ a in Metric.ball (0 : R3) ρ, bsIntegrand ω x a)
            - (∫ a in Metric.ball (0 : R3) ρ, bsIntegrand ω x₀ a)‖
          + ‖(4 * Real.pi / 3) • crossL (ω x) - (4 * Real.pi / 3) • crossL (ω x₀)‖ := by
        have heq : ((∫ a in Metric.ball (0 : R3) ρ, bsIntegrand ω x a)
              + (4 * Real.pi / 3) • crossL (ω x))
            - ((∫ a in Metric.ball (0 : R3) ρ, bsIntegrand ω x₀ a)
              + (4 * Real.pi / 3) • crossL (ω x₀))
            = ((∫ a in Metric.ball (0 : R3) ρ, bsIntegrand ω x a)
                - (∫ a in Metric.ball (0 : R3) ρ, bsIntegrand ω x₀ a))
              + ((4 * Real.pi / 3) • crossL (ω x) - (4 * Real.pi / 3) • crossL (ω x₀)) := by
          abel
        rw [heq]
        exact norm_add_le _ _
    _ < ε := by linarith

/-- **Continuity of the candidate derivative of the Biot–Savart field** for a bounded Hölder
vorticity.  The case of a negative Hölder constant is reduced to the nonnegative one: then
`ω` is constant (the Hölder inequality would otherwise force a positive norm to be negative),
and then `bsIntegrand` vanishes identically. -/
theorem continuous_bsDerivCLM {ω : Work.LWP.R3 → Work.LWP.R3} {M C c : ℝ} (hc : 0 < c)
    (hbdd : ∀ a, ‖ω a‖ ≤ M) (hhold : ∀ a b : Work.LWP.R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c)
    (ρ : ℝ) : Continuous (fun x => Work.CoreResiduals.BiotSavart.bsDerivCLM ω ρ x) := by
  have hCmax : ∀ a b : Work.LWP.R3, ‖ω a - ω b‖ ≤ max C 0 * ‖a - b‖ ^ c := by
    intro a b
    rcases le_or_gt 0 C with hC | hC
    · simpa only [max_eq_left hC] using hhold a b
    · have hconst : ω a = ω b := by
        by_cases hab : a = b
        · rw [hab]
        · exfalso
          have hpos : 0 < ‖a - b‖ ^ c :=
            Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hab)) c
          have hneg : C * ‖a - b‖ ^ c < 0 := mul_neg_of_neg_of_pos hC hpos
          linarith [norm_nonneg (ω a - ω b), hhold a b]
      rw [hconst, sub_self, norm_zero, max_eq_right (le_of_lt hC)]
      simp
  exact continuous_bsDerivCLM_of_nonneg (C := max C 0) hc (le_max_right _ _) hCmax ρ

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.kf_sub_le_rpow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

namespace Work.CoreResiduals.BiotSavart

/-- `(x ^ n)⁻¹ = x ^ (-(n : ℝ))` for `x ≥ 0`: the integer power `x ^ n` of a nonnegative real is
`x` raised to the *real* exponent `n`, so its inverse is `x` raised to `-n`. -/
lemma inv_pow_eq_rpow_neg (x : ℝ) (hx : 0 ≤ x) (n : ℕ) : (x ^ n)⁻¹ = x ^ (-(n:ℝ)) := by
  rw [← Real.rpow_natCast x n, ← Real.rpow_neg hx (n:ℝ)]

/-- **Far-regime bound for the difference of two kernel values.**  If the increment `h` is at
most half of `‖y‖`, so that the whole segment `[y, y+h]` stays away from the origin, then
`‖kf (y + h) - kf y‖ ≤ 1024 ‖h‖² ‖y‖⁻⁴ + 4 ‖h‖ ‖y‖⁻³`.  This is the second-order Taylor
expansion of `kf` at `y` (`norm_resid_le_far`) plus the operator-norm bound
`‖kDerivCLM y‖ ≤ 4/‖y‖³` (`norm_kDerivCLM_le`). -/
theorem norm_kf_sub_le_far (h y : Work.LWP.R3) (hy : 2 * ‖h‖ ≤ ‖y‖) :
    ‖Work.StabilityFar.Decay.kf (y + h) - Work.StabilityFar.Decay.kf y‖
      ≤ 1024 * ‖h‖ ^ (2:ℝ) * ‖y‖ ^ (-4:ℝ) + 4 * ‖h‖ * ‖y‖ ^ (-3:ℝ) := by
  have hid : Work.StabilityFar.Decay.kf (y + h) - Work.StabilityFar.Decay.kf y
      = resid h y + Work.StabilityFar.Decay.kDerivCLM y h := by
    rw [resid]
    abel
  rw [hid]
  have hres : ‖resid h y‖ ≤ 1024 * ‖h‖ ^ (2:ℝ) * ‖y‖ ^ (-4:ℝ) := by
    have h0 := norm_resid_le_far h y hy
    have h2 : ‖h‖ ^ (2:ℕ) = ‖h‖ ^ (2:ℝ) := (Real.rpow_two ‖h‖).symm
    rwa [h2] at h0
  have hder : ‖Work.StabilityFar.Decay.kDerivCLM y h‖ ≤ 4 * ‖h‖ * ‖y‖ ^ (-3:ℝ) := by
    rcases eq_or_lt_of_le (norm_nonneg y) with hy0 | hypos
    · -- degenerate case `y = 0`: then `h = 0` as well and both sides vanish
      have hy00 : y = 0 := by rw [← norm_eq_zero]; exact hy0.symm
      have hh0 : h = 0 := by
        rw [← norm_eq_zero]
        have h2 : 2 * ‖h‖ ≤ 0 := by rw [← hy0] at hy; exact hy
        linarith [norm_nonneg h]
      rw [hy00, hh0]
      simp [kDerivCLM_zero, Real.zero_rpow (by norm_num : (-3:ℝ) ≠ 0)]
    · have hb := Work.StabilityFar.Decay.norm_kDerivCLM_le y ‖y‖ hypos le_rfl
      calc ‖Work.StabilityFar.Decay.kDerivCLM y h‖
          ≤ ‖Work.StabilityFar.Decay.kDerivCLM y‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (4 / ‖y‖ ^ 3) * ‖h‖ := by gcongr
        _ = 4 * ‖h‖ * ‖y‖ ^ (-3:ℝ) := by
            rw [show (-3:ℝ) = -(↑(3:ℕ) : ℝ) by norm_num, div_eq_mul_inv,
              inv_pow_eq_rpow_neg ‖y‖ (norm_nonneg y) 3]
            ring
  calc ‖resid h y + Work.StabilityFar.Decay.kDerivCLM y h‖
      ≤ ‖resid h y‖ + ‖Work.StabilityFar.Decay.kDerivCLM y h‖ := norm_add_le _ _
    _ ≤ 1024 * ‖h‖ ^ (2:ℝ) * ‖y‖ ^ (-4:ℝ) + 4 * ‖h‖ * ‖y‖ ^ (-3:ℝ) :=
        add_le_add hres hder

/-- **Hölder-type bound for the Newtonian kernel.**  For `0 < α < 1` there is a constant `C`
such that for all `p q`

  `‖kf p - kf q‖ ≤ C ‖p - q‖ ^ α (‖p‖ ^ (-2-α) + ‖q‖ ^ (-2-α))`.

The two regimes of the argument are described in the header; here it only remains to combine
them with the triangle inequality for `‖kf p‖ = ‖p‖⁻²`. -/
theorem kf_sub_le_rpow {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p q : Work.LWP.R3,
      ‖Work.StabilityFar.Decay.kf p - Work.StabilityFar.Decay.kf q‖
        ≤ C * ‖p - q‖ ^ α * (‖p‖ ^ (-2 - α) + ‖q‖ ^ (-2 - α)) := by
  refine ⟨1028, by norm_num, ?_⟩
  -- The statement is symmetric in `p` and `q`, so it suffices to treat `‖p‖ ≤ ‖q‖`.
  have key : ∀ p q : Work.LWP.R3, ‖p‖ ≤ ‖q‖ →
      ‖Work.StabilityFar.Decay.kf p - Work.StabilityFar.Decay.kf q‖
        ≤ 1028 * ‖p - q‖ ^ α * (‖p‖ ^ (-2 - α) + ‖q‖ ^ (-2 - α)) := by
    intro p q hrs
    by_cases hpq : p = q
    · subst hpq
      simp [Real.zero_rpow (ne_of_gt hα)]
    · have hdpos : 0 < ‖p - q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hpq)
      by_cases hfar : 2 * ‖p - q‖ ≤ ‖q‖
      · -- far regime `2‖p - q‖ ≤ ‖q‖`
        have hqpos : 0 < ‖q‖ := by linarith
        have h1 : ‖Work.StabilityFar.Decay.kf p - Work.StabilityFar.Decay.kf q‖
            ≤ 1024 * ‖p - q‖ ^ (2:ℝ) * ‖q‖ ^ (-4:ℝ)
              + 4 * ‖p - q‖ * ‖q‖ ^ (-3:ℝ) := by
          have hh := norm_kf_sub_le_far (p - q) q hfar
          rwa [show q + (p - q) = p by abel] at hh
        have h2 := rpow_far_arith hα hα1 hdpos hqpos (by linarith)
        have h3 : 0 ≤ 1028 * ‖p - q‖ ^ α := by
          have := Real.rpow_nonneg (norm_nonneg (p - q)) α
          linarith
        have h4 : ‖q‖ ^ (-2 - α) ≤ ‖p‖ ^ (-2 - α) + ‖q‖ ^ (-2 - α) := by
          have := Real.rpow_nonneg (norm_nonneg p) (-2 - α)
          linarith
        calc ‖Work.StabilityFar.Decay.kf p - Work.StabilityFar.Decay.kf q‖
            ≤ 1028 * ‖p - q‖ ^ α * ‖q‖ ^ (-2 - α) := h1.trans h2
          _ ≤ 1028 * ‖p - q‖ ^ α * (‖p‖ ^ (-2 - α) + ‖q‖ ^ (-2 - α)) :=
              mul_le_mul_of_nonneg_left h4 h3
      · -- near regime `‖q‖ < 2‖p - q‖`
        have hnear' : ‖q‖ ≤ 2 * ‖p - q‖ := le_of_lt (not_le.mp hfar)
        have h1 : ‖Work.StabilityFar.Decay.kf p - Work.StabilityFar.Decay.kf q‖
            ≤ ‖p‖ ^ (-2:ℝ) + ‖q‖ ^ (-2:ℝ) := by
          calc ‖Work.StabilityFar.Decay.kf p - Work.StabilityFar.Decay.kf q‖
              ≤ ‖Work.StabilityFar.Decay.kf p‖ + ‖Work.StabilityFar.Decay.kf q‖ :=
                norm_sub_le _ _
            _ = ‖p‖ ^ (-2:ℝ) + ‖q‖ ^ (-2:ℝ) := by rw [norm_kf_eq, norm_kf_eq]
        exact h1.trans (rpow_near_arith hα hα1 (norm_nonneg p) hrs hnear')
  intro p q
  rcases le_total ‖p‖ ‖q‖ with hle | hle
  · exact key p q hle
  · -- swap the roles of `p` and `q`; the statement is symmetric
    have hh := key q p hle
    have e1 : ‖q - p‖ = ‖p - q‖ := norm_sub_rev q p
    have e2 : ‖Work.StabilityFar.Decay.kf q - Work.StabilityFar.Decay.kf p‖
        = ‖Work.StabilityFar.Decay.kf p - Work.StabilityFar.Decay.kf q‖ :=
      (norm_sub_rev (Work.StabilityFar.Decay.kf p) (Work.StabilityFar.Decay.kf q)).symm
    have e3 : ‖q‖ ^ (-2 - α) + ‖p‖ ^ (-2 - α)
        = ‖p‖ ^ (-2 - α) + ‖q‖ ^ (-2 - α) := add_comm _ _
    rw [e1, e2, e3] at hh
    exact hh

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.norm_bsIntegrand_le_interp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open Work.StabilityFar.Decay

theorem norm_bsIntegrand_le_interp {α A H : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hA : 0 ≤ A) (hH : 0 ≤ H)
    {g : Work.LWP.R3 → Work.LWP.R3} (hbdd : ∀ a, ‖g a‖ ≤ A)
    (hhold : ∀ a b : Work.LWP.R3, ‖g a - g b‖ ≤ 2 * H * ‖a - b‖ ^ α)
    (x a : Work.LWP.R3) :
    ‖Work.CoreResiduals.BiotSavart.bsIntegrand g x a‖ ≤
      4 * (2 * A) ^ α * (2 * H) ^ (1 - α) * ‖x - a‖ ^ (α * (1 - α) - 3) := by
  rcases eq_or_ne x a with hxa | hxa
  · -- the singular point `x = a`: both sides vanish
    rw [hxa]
    have hz : bsIntegrand g a a = 0 := by
      simp [bsIntegrand, crossL_zero]
    rw [hz, norm_zero, sub_self, norm_zero, Real.zero_rpow]
    · norm_num
    · have h1 : (0 : ℝ) < 1 - α := by linarith
      have h2 : α * (1 - α) < 3 := by nlinarith
      linarith
  · have hr : (0 : ℝ) < ‖x - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxa)
    -- the interpolation of the bounded-ness and Hölder bounds on `g a - g x`
    have hd : ‖g a - g x‖ ≤ (2 * A) ^ α * (2 * H) ^ (1 - α) * ‖x - a‖ ^ (α * (1 - α)) :=
      norm_gSub_le_interp hα hα1 hA hH hbdd hhold x a
    calc ‖bsIntegrand g x a‖
        ≤ ‖crossL (g a - g x)‖ * ‖kDerivCLM (x - a)‖ := by
          rw [bsIntegrand]
          exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖g a - g x‖ * (4 / ‖x - a‖ ^ 3) := by
          gcongr
          · exact norm_crossL_le _
          · exact norm_kDerivCLM_le (x - a) ‖x - a‖ hr le_rfl
      _ ≤ ((2 * A) ^ α * (2 * H) ^ (1 - α) * ‖x - a‖ ^ (α * (1 - α))) *
            (4 / ‖x - a‖ ^ 3) :=
          mul_le_mul_of_nonneg_right hd (by positivity)
      _ = 4 * (2 * A) ^ α * (2 * H) ^ (1 - α) * ‖x - a‖ ^ (α * (1 - α) - 3) := by
          rw [Real.rpow_sub hr, Real.rpow_ofNat]
          ring

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.setIntegral_ball_zero_norm_sub_rpow_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Set
open scoped ENNReal

/-- **Translation invariance of the set Lebesgue integral over an open ball** (centred form):
for any (not necessarily finite) `ℝ≥0∞`-valued function `F`,
`∫⁻_{B(c,r)} F (y - c) = ∫⁻_{B(0,r)} F`. -/
private lemma lintegral_ball_sub_center_eq (c : Work.LWP.R3) (r : ℝ)
    (F : Work.LWP.R3 → ℝ≥0∞) :
    ∫⁻ y in Metric.ball c r, F (y - c) = ∫⁻ z in Metric.ball (0 : Work.LWP.R3) r, F z := by
  classical
  have hs : MeasurableSet (Metric.ball c r) := Metric.isOpen_ball.measurableSet
  have hs0 : MeasurableSet (Metric.ball (0 : Work.LWP.R3) r) :=
    Metric.isOpen_ball.measurableSet
  have hmem : ∀ y : Work.LWP.R3,
      y ∈ Metric.ball c r ↔ y - c ∈ Metric.ball (0 : Work.LWP.R3) r := by
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

/-- **The `B(0,ρ)` norm-power estimate.**  For `ρ ≥ 0`, `s > -3` and any centre `x ∈ ℝ³`,
`∫_{B(0,ρ)} ‖x - a‖^s da ≤ 4π (ρ + ‖x‖)^{s+3} / (s + 3)`.

`B(0,ρ)` is contained in `B(x, ρ + ‖x‖)`; the integrand is a radial power of the distance to its
own singularity, whose integral over a ball is computed by `lintegral_ball_norm_rpow`
(`∫_{B(0,R)} ‖z‖^s = 4π R^{s+3}/(s+3)` for `s > -3`), together with translation invariance
`lintegral_ball_sub_center_eq`.  The conversion between the Bochner integral and the `lintegral`
uses `setIntegral_eq_lintegral_of_nonneg`. -/
theorem setIntegral_ball_zero_norm_sub_rpow_le (x : Work.LWP.R3) {ρ s : ℝ} (hρ : 0 ≤ ρ)
    (hs : -3 < s) :
    ∫ a in Metric.ball (0 : Work.LWP.R3) ρ, ‖x - a‖ ^ s
      ≤ 4 * Real.pi * (ρ + ‖x‖) ^ (s + 3) / (s + 3) := by
  have hs3 : (0 : ℝ) < s + 3 := by linarith
  have hCnn : 0 ≤ 4 * Real.pi * (ρ + ‖x‖) ^ (s + 3) / (s + 3) := by
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
        (Real.rpow_nonneg (by positivity) _)
    · linarith
  rcases eq_or_lt_of_le hρ with hρ0 | hρpos
  · -- `ρ = 0`: the ball is empty, so the integral vanishes.
    have hball : Metric.ball (0 : Work.LWP.R3) ρ = ∅ :=
      Metric.ball_eq_empty.mpr (le_of_eq hρ0.symm)
    rw [hball, setIntegral_empty]
    exact hCnn
  · -- `ρ > 0`: squeeze the ball `B(0,ρ)` into `B(x, ρ + ‖x‖)` and integrate radially.
    have hRpos : 0 < ρ + ‖x‖ := by linarith [norm_nonneg x]
    have hnn : ∀ a : Work.LWP.R3, 0 ≤ ‖x - a‖ ^ s :=
      fun a => Real.rpow_nonneg (norm_nonneg _) s
    have hmeas : AEStronglyMeasurable (fun a : Work.LWP.R3 => ‖x - a‖ ^ s) volume :=
      (show Measurable (fun a : Work.LWP.R3 => ‖x - a‖ ^ s) by
        measurability).aestronglyMeasurable
    have hsub : Metric.ball (0 : Work.LWP.R3) ρ ⊆ Metric.ball x (ρ + ‖x‖) := by
      intro a ha
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at ha
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖a - x‖ ≤ ‖a‖ + ‖x‖ := norm_sub_le a x
        _ < ρ + ‖x‖ := by linarith
    have hlin : ∫⁻ a in Metric.ball (0 : Work.LWP.R3) ρ, ENNReal.ofReal (‖x - a‖ ^ s)
        ≤ ENNReal.ofReal (4 * Real.pi * (ρ + ‖x‖) ^ (s + 3) / (s + 3)) := by
      calc ∫⁻ a in Metric.ball (0 : Work.LWP.R3) ρ, ENNReal.ofReal (‖x - a‖ ^ s)
          ≤ ∫⁻ a in Metric.ball x (ρ + ‖x‖), ENNReal.ofReal (‖x - a‖ ^ s) :=
            lintegral_mono_set hsub
        _ = ∫⁻ a in Metric.ball x (ρ + ‖x‖), ENNReal.ofReal (‖a - x‖ ^ s) := by
            apply lintegral_congr
            intro a
            rw [norm_sub_rev]
        _ = ∫⁻ z in Metric.ball (0 : Work.LWP.R3) (ρ + ‖x‖), ENNReal.ofReal (‖z‖ ^ s) :=
            lintegral_ball_sub_center_eq x (ρ + ‖x‖) (fun z => ENNReal.ofReal (‖z‖ ^ s))
        _ = ENNReal.ofReal (4 * Real.pi * (ρ + ‖x‖) ^ (s + 3) / (s + 3)) :=
            lintegral_ball_norm_rpow s hs (ρ + ‖x‖) hRpos
    rw [setIntegral_eq_lintegral_of_nonneg measurableSet_ball hmeas hnn]
    exact le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin)
      (le_of_eq (ENNReal.toReal_ofReal hCnn))

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.Shim.Fstar_smooth_of_EllHyp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

set_option autoImplicit false



end Work.FTS.EllipticEst.Cert
end
end
-- ===== merged: Submission.Work.FTS.H2.T1EasyBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## The Leibniz summands -/

/-- The `(i,b)`-th `D_z`-slot Leibniz summand of `H4PairInt α (f · D_θ g) g`. -/
def xD (f g : ℝ → ℝ → ℝ) (i b : ℕ) (z θ : ℝ) : ℝ :=
  (i.choose b : ℝ) * (Spaces.DzIter b f z θ * Spaces.mixed (i - b) 1 g z θ
    * Spaces.DzIter i g z θ * (Whz z θ) ^ 2)

/-- The `(i,j,a,b)`-th mixed-slot Leibniz summand of `H4PairInt α (f · D_θ g) g`. -/
def yM (α : ℝ) (f g : ℝ → ℝ → ℝ) (i j a b : ℕ) (z θ : ℝ) : ℝ :=
  ((i.choose a : ℝ) * (j.choose b : ℝ)) *
    (Spaces.mixed b a f z θ * Spaces.mixed (j - b) (i - a + 1) g z θ
      * Spaces.mixed j i g z θ * (Wm α z θ) ^ 2)

/-- The pointwise majorant of `T1Easy`. -/
def EasyMajor (α : ℝ) (f g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ =>
    (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1),
        if i = 4 ∧ b = 0 then 0 else |xD f g i b z θ|)
    + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b z θ|)
         else 0)

/-- The product measure on the closed quadrant `[0,∞) × [0,π/2]`. -/
def pm : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ)

theorem pm_eq : pm = MeasureTheory.volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ) := by
  rw [pm, MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]


theorem ae_pm_mem : ∀ᵐ p ∂pm, p ∈ Spaces.Iz ×ˢ Spaces.Iθ := by
  rw [pm_eq]
  exact MeasureTheory.ae_restrict_mem (measurableSet_Ici.prod measurableSet_Icc)

/-! ## The weight identities -/

/-- `(Whz z θ)² = w(z)² sin(2θ)^{-η}`. -/
theorem Whz_sq (z θ : ℝ) (hs : 0 ≤ Real.sin (2 * θ)) :
    (Whz z θ) ^ 2 = (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
  have h1 : Real.sin (2 * θ) ^ (Spaces.eta / 2) * Real.sin (2 * θ) ^ (Spaces.eta / 2)
      = Real.sin (2 * θ) ^ Spaces.eta := by
    rw [← Real.rpow_add' hs (by norm_num [Spaces.eta])]
    congr 1
    ring
  have h3 : (Real.sin (2 * θ) ^ (Spaces.eta / 2)) ^ 2 = Real.sin (2 * θ) ^ Spaces.eta := by
    rw [pow_two, h1]
  rw [Whz, Real.rpow_neg hs Spaces.eta, div_pow, h3, div_eq_mul_inv]

/-- `(Wm α z θ)² = w(z)² sin(2θ)^{-γ}`. -/
theorem Wm_sq (α : ℝ) (hα : 0 < α) (z θ : ℝ) (hs : 0 ≤ Real.sin (2 * θ)) :
    (Wm α z θ) ^ 2 = (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.gam α) := by
  have h1 : Real.sin (2 * θ) ^ (-(Spaces.gam α / 2)) * Real.sin (2 * θ) ^ (-(Spaces.gam α / 2))
      = Real.sin (2 * θ) ^ (-Spaces.gam α) := by
    rw [← Real.rpow_add' hs (by intro hh; have := Spaces.gam_pos hα; linarith)]
    congr 1
    ring
  have h2 : (Real.sin (2 * θ) ^ (-(Spaces.gam α / 2))) ^ 2
      = Real.sin (2 * θ) ^ (-Spaces.gam α) := by
    rw [pow_two, h1]
  simp only [Wm, Spaces.Wt, Spaces.wTheta, mul_pow, h2]

theorem w_zero : Spaces.w 0 = 0 := by
  simp only [Spaces.w]
  norm_num



/-- On the closed quadrant the `η`-weight is dominated by the `γ`-weight: `Whz ≤ Wm`. -/
theorem Whz_le_Wm (α : ℝ) (hα : 0 < α) {z θ : ℝ} (hθ : θ ∈ Spaces.Iθ) :
    Whz z θ ≤ Wm α z θ := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := Spaces.Slots.sin_two_nonneg_Iθ (θ := θ) hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hw : 0 ≤ Spaces.w z := by simp only [Spaces.w]; positivity
  have hle : Real.sin (2 * θ) ^ (-(Spaces.eta / 2))
      ≤ Real.sin (2 * θ) ^ (-(Spaces.gam α / 2)) := by
    rcases eq_or_lt_of_le hs0 with hs | hs
    · rw [← hs, Real.zero_rpow (by intro h; have := Spaces.eta_pos; linarith),
        Real.zero_rpow (by intro h; have := Spaces.gam_pos hα; linarith)]
    · refine Real.rpow_le_rpow_of_exponent_ge hs hs1 ?_
      have h2 : Spaces.eta ≤ Spaces.gam α := by
        have h1 : Spaces.eta < 1 := Spaces.eta_lt_one
        have h3 : 1 < Spaces.gam α := Spaces.one_lt_gam hα
        linarith
      linarith
  rw [Whz, Wm, Spaces.Wt, Spaces.wTheta, div_eq_mul_inv, ← Real.rpow_neg hs0 (Spaces.eta / 2)]
  exact mul_le_mul_of_nonneg_left hle hw

/-- `Whz² ≤ Wm · Whz` on the closed quadrant. -/
theorem Whz_sq_le_Wm_mul (α : ℝ) (hα : 0 < α) {z θ : ℝ} (hθ : θ ∈ Spaces.Iθ) :
    (Whz z θ) ^ 2 ≤ Wm α z θ * Whz z θ := by
  have h1 : Whz z θ ≤ Wm α z θ := Whz_le_Wm α hα hθ
  have h2 : 0 ≤ Whz z θ := Whz_nonneg hθ
  nlinarith [h1, h2]

/-! ## Pointwise bounds on the low-order derivatives -/





/-! ## Measurability -/

/-- A function continuous on the open quadrant is a.e. strongly measurable for the product
measure on the quadrant. -/
theorem aesm_of_Qd {F : ℝ × ℝ → ℝ} (h : ContinuousOn F Qd) :
    AEStronglyMeasurable F pm :=
  Work.Spaces.aesm_of_continuousOn_Qd F (by simpa only [Qd] using h)







/-! ## The generic Cauchy–Schwarz bound -/

/-- Cauchy–Schwarz bound for a triple product `V · A · B` whose two "slot" factors are
dominated by the `ℋ⁴`-integrands of `u` resp. `v`, and whose first factor is bounded by `K`. -/
theorem slot_pair_bound (α : ℝ) (u v : ℝ → ℝ → ℝ)
    (hmu : Spaces.HkMem α 4 u) (hmv : Spaces.HkMem α 4 v)
    (A B V : ℝ → ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hV : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ, |V z θ| ≤ K)
    (hA0 : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ, 0 ≤ A z θ)
    (hB0 : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ, 0 ≤ B z θ)
    (hA : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ, (A z θ) ^ 2 ≤ Spaces.HkIntegrand α 4 u z θ)
    (hB : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ, (B z θ) ^ 2 ≤ Spaces.HkIntegrand α 4 v z θ)
    (hAmeas : ∀ z ∈ Spaces.Iz,
      AEStronglyMeasurable (fun θ => A z θ) (volume.restrict Spaces.Iθ))
    (hBmeas : ∀ z ∈ Spaces.Iz,
      AEStronglyMeasurable (fun θ => B z θ) (volume.restrict Spaces.Iθ))
    (hVABmeas : AEStronglyMeasurable
      (Function.uncurry (fun z θ => |V z θ * A z θ * B z θ|)) pm) :
    MeasureTheory.Integrable
        (fun z => ∫ θ in Spaces.Iθ, |V z θ * A z θ * B z θ|) (volume.restrict Spaces.Iz) ∧
      ∫ z in Spaces.Iz, (∫ θ in Spaces.Iθ, |V z θ * A z θ * B z θ|)
        ≤ K * Spaces.HkNorm α 4 u * Spaces.HkNorm α 4 v := by
  set Φu : ℝ → ℝ := fun z => ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α 4 u z θ with hΦu
  set Φv : ℝ → ℝ := fun z => ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α 4 v z θ with hΦv
  have hΦu_nn : ∀ z, 0 ≤ Φu z :=
    fun z => integral_nonneg fun θ => Spaces.HkIntegrand_nonneg α 4 u z θ
  have hΦv_nn : ∀ z, 0 ≤ Φv z :=
    fun z => integral_nonneg fun θ => Spaces.HkIntegrand_nonneg α 4 v z θ
  have hA2int : ∀ z ∈ Spaces.Iz, IntegrableOn (fun θ => (A z θ) ^ 2) Spaces.Iθ := by
    intro z hz
    refine MeasureTheory.Integrable.mono' (hmu.1 z hz) ((hAmeas z hz).pow 2) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hA z hz θ hθ
  have hB2int : ∀ z ∈ Spaces.Iz, IntegrableOn (fun θ => (B z θ) ^ 2) Spaces.Iθ := by
    intro z hz
    refine MeasureTheory.Integrable.mono' (hmv.1 z hz) ((hBmeas z hz).pow 2) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hB z hz θ hθ
  have hA2le : ∀ z ∈ Spaces.Iz, ∫ θ in Spaces.Iθ, (A z θ) ^ 2 ≤ Φu z := fun z hz =>
    setIntegral_mono_of_nonneg (fun θ _ => sq_nonneg _) (fun θ hθ => hA z hz θ hθ) (hmu.1 z hz)
  have hB2le : ∀ z ∈ Spaces.Iz, ∫ θ in Spaces.Iθ, (B z θ) ^ 2 ≤ Φv z := fun z hz =>
    setIntegral_mono_of_nonneg (fun θ _ => sq_nonneg _) (fun θ hθ => hB z hz θ hθ) (hmv.1 z hz)
  have hABint : ∀ z ∈ Spaces.Iz, IntegrableOn (fun θ => A z θ * B z θ) Spaces.Iθ := by
    intro z hz
    refine MeasureTheory.Integrable.mono' ((hmu.1 z hz).add (hmv.1 z hz))
      ((hAmeas z hz).mul (hBmeas z hz)) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_of_nonneg (mul_nonneg (hA0 z hz θ hθ) (hB0 z hz θ hθ))]
    have h1 := hA z hz θ hθ
    have h2 := hB z hz θ hθ
    have hn1 : 0 ≤ Spaces.HkIntegrand α 4 u z θ := Spaces.HkIntegrand_nonneg α 4 u z θ
    have hn2 : 0 ≤ Spaces.HkIntegrand α 4 v z θ := Spaces.HkIntegrand_nonneg α 4 v z θ
    have hmain : A z θ * B z θ
        ≤ Spaces.HkIntegrand α 4 u z θ + Spaces.HkIntegrand α 4 v z θ := by
      nlinarith [sq_nonneg (A z θ - B z θ)]
    simpa only [Pi.add_apply] using hmain
  have hMemLpA : ∀ z ∈ Spaces.Iz, MemLp (fun θ => A z θ) 2 (volume.restrict Spaces.Iθ) := by
    intro z hz
    exact (memLp_two_iff_integrable_sq (hAmeas z hz)).mpr (hA2int z hz)
  have hMemLpB : ∀ z ∈ Spaces.Iz, MemLp (fun θ => B z θ) 2 (volume.restrict Spaces.Iθ) := by
    intro z hz
    exact (memLp_two_iff_integrable_sq (hBmeas z hz)).mpr (hB2int z hz)
  have hCSθ : ∀ z ∈ Spaces.Iz,
      ∫ θ in Spaces.Iθ, A z θ * B z θ
        ≤ Real.sqrt (∫ θ in Spaces.Iθ, (A z θ) ^ 2)
          * Real.sqrt (∫ θ in Spaces.Iθ, (B z θ) ^ 2) := by
    intro z hz
    have hA0ae : 0 ≤ᵐ[volume.restrict Spaces.Iθ] (fun θ => A z θ) :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hA0 z hz θ hθ)
    have hB0ae : 0 ≤ᵐ[volume.restrict Spaces.Iθ] (fun θ => B z θ) :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hB0 z hz θ hθ)
    have hABnn : 0 ≤ᵐ[volume.restrict Spaces.Iθ] (fun θ => A z θ * B z θ) := by
      filter_upwards [hA0ae, hB0ae] with θ h1 h2
      exact mul_nonneg h1 h2
    have hg : ∀ᵐ θ ∂(volume.restrict Spaces.Iθ), |A z θ * B z θ| ≤ A z θ * B z θ := by
      filter_upwards [hABnn] with θ h1
      rw [abs_of_nonneg h1]
    have h := CS1D (μ := volume.restrict Spaces.Iθ) (g := fun θ => A z θ * B z θ)
      (A := fun θ => A z θ) (B := fun θ => B z θ) (hMemLpA z hz) (hMemLpB z hz) hA0ae hB0ae hg
    rwa [abs_of_nonneg (integral_nonneg_of_ae hABnn)] at h
  have hinner : ∀ z ∈ Spaces.Iz,
      ∫ θ in Spaces.Iθ, |V z θ * A z θ * B z θ| ≤ K * (Real.sqrt (Φu z) * Real.sqrt (Φv z)) := by
    intro z hz
    have h1 : ∫ θ in Spaces.Iθ, |V z θ * A z θ * B z θ|
        ≤ ∫ θ in Spaces.Iθ, K * (A z θ * B z θ) := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun θ => abs_nonneg _)
        ((hABint z hz).const_mul K) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [abs_mul, abs_mul, abs_of_nonneg (hA0 z hz θ hθ), abs_of_nonneg (hB0 z hz θ hθ)]
      calc |V z θ| * A z θ * B z θ = |V z θ| * (A z θ * B z θ) := by ring
        _ ≤ K * (A z θ * B z θ) :=
            mul_le_mul_of_nonneg_right (hV z hz θ hθ) (mul_nonneg (hA0 z hz θ hθ) (hB0 z hz θ hθ))
    calc ∫ θ in Spaces.Iθ, |V z θ * A z θ * B z θ|
        ≤ ∫ θ in Spaces.Iθ, K * (A z θ * B z θ) := h1
      _ = K * ∫ θ in Spaces.Iθ, A z θ * B z θ := integral_const_mul K _
      _ ≤ K * (Real.sqrt (∫ θ in Spaces.Iθ, (A z θ) ^ 2)
            * Real.sqrt (∫ θ in Spaces.Iθ, (B z θ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (hCSθ z hz) hK
      _ ≤ K * (Real.sqrt (Φu z) * Real.sqrt (Φv z)) := by
          refine mul_le_mul_of_nonneg_left ?_ hK
          exact mul_le_mul (Real.sqrt_le_sqrt (hA2le z hz)) (Real.sqrt_le_sqrt (hB2le z hz))
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hmu_lp : MemLp (fun z => Real.sqrt (Φu z)) 2 (volume.restrict Spaces.Iz) := by
    refine (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hmu.2.aestronglyMeasurable)).mpr ?_
    refine hmu.2.congr ?_
    filter_upwards with z
    rw [Real.sq_sqrt (hΦu_nn z)]
  have hmv_lp : MemLp (fun z => Real.sqrt (Φv z)) 2 (volume.restrict Spaces.Iz) := by
    refine (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hmv.2.aestronglyMeasurable)).mpr ?_
    refine hmv.2.congr ?_
    filter_upwards with z
    rw [Real.sq_sqrt (hΦv_nn z)]
  have hprod_int : Integrable (fun z => Real.sqrt (Φu z) * Real.sqrt (Φv z))
      (volume.restrict Spaces.Iz) := memLp_one_iff_integrable.mp (hmu_lp.mul hmv_lp)
  have houter : ∫ z in Spaces.Iz, (∫ θ in Spaces.Iθ, |V z θ * A z θ * B z θ|)
      ≤ K * ∫ z in Spaces.Iz, (Real.sqrt (Φu z) * Real.sqrt (Φv z)) := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg
      (Eventually.of_forall fun z => integral_nonneg fun θ => abs_nonneg _)
      (hprod_int.const_mul K) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    exact hinner z hz
  have hQu : (∫ z in Spaces.Iz, Real.sqrt (Φu z) ^ 2) = Spaces.HkSq α 4 u := by
    rw [Spaces.HkSq, hΦu]
    exact integral_congr_ae (Eventually.of_forall fun z => Real.sq_sqrt (hΦu_nn z))
  have hQv : (∫ z in Spaces.Iz, Real.sqrt (Φv z) ^ 2) = Spaces.HkSq α 4 v := by
    rw [Spaces.HkSq, hΦv]
    exact integral_congr_ae (Eventually.of_forall fun z => Real.sq_sqrt (hΦv_nn z))
  have hsqrt : ∫ z in Spaces.Iz, (Real.sqrt (Φu z) * Real.sqrt (Φv z))
      ≤ Spaces.HkNorm α 4 u * Spaces.HkNorm α 4 v := by
    have hsq : (∫ z in Spaces.Iz, Real.sqrt (Φu z) * Real.sqrt (Φv z)) ^ 2
        ≤ Spaces.HkSq α 4 u * Spaces.HkSq α 4 v := by
      rw [← hQu, ← hQv]
      exact Work.Spaces.cs_integral hmu_lp hmv_lp
    calc ∫ z in Spaces.Iz, (Real.sqrt (Φu z) * Real.sqrt (Φv z))
        ≤ Real.sqrt (Spaces.HkSq α 4 u * Spaces.HkSq α 4 v) := Real.le_sqrt_of_sq_le hsq
      _ = Real.sqrt (Spaces.HkSq α 4 u) * Real.sqrt (Spaces.HkSq α 4 v) :=
          Real.sqrt_mul (Spaces.HkSq_nonneg α 4 u) _
      _ = Spaces.HkNorm α 4 u * Spaces.HkNorm α 4 v := rfl
  constructor
  · refine MeasureTheory.Integrable.mono' (hprod_int.const_mul K)
      hVABmeas.integral_prod_right' ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => abs_nonneg _)]
    exact hinner z hz
  · calc ∫ z in Spaces.Iz, (∫ θ in Spaces.Iθ, |V z θ * A z θ * B z θ|)
        ≤ K * ∫ z in Spaces.Iz, (Real.sqrt (Φu z) * Real.sqrt (Φv z)) := houter
      _ ≤ K * (Spaces.HkNorm α 4 u * Spaces.HkNorm α 4 v) :=
          mul_le_mul_of_nonneg_left hsqrt hK
      _ = K * Spaces.HkNorm α 4 u * Spaces.HkNorm α 4 v := by ring

/-- The two-dimensional form of `slot_pair_bound`: the integrand is integrable on the
product measure, with the bound expressed as a two-dimensional integral. -/
theorem term_of_slot (α : ℝ) (u v : ℝ → ℝ → ℝ)
    (hmu : Spaces.HkMem α 4 u) (hmv : Spaces.HkMem α 4 v)
    (A B V : ℝ → ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hV : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ, |V z θ| ≤ K)
    (hA0 : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ, 0 ≤ A z θ)
    (hB0 : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ, 0 ≤ B z θ)
    (hA : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ, (A z θ) ^ 2 ≤ Spaces.HkIntegrand α 4 u z θ)
    (hB : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ, (B z θ) ^ 2 ≤ Spaces.HkIntegrand α 4 v z θ)
    (hAmeas : ∀ z ∈ Spaces.Iz,
      AEStronglyMeasurable (fun θ => A z θ) (volume.restrict Spaces.Iθ))
    (hBmeas : ∀ z ∈ Spaces.Iz,
      AEStronglyMeasurable (fun θ => B z θ) (volume.restrict Spaces.Iθ))
    (hVABmeas : AEStronglyMeasurable
      (Function.uncurry (fun z θ => |V z θ * A z θ * B z θ|)) pm) :
    MeasureTheory.Integrable (Function.uncurry (fun z θ => |V z θ * A z θ * B z θ|)) pm ∧
      (∫ p, |V p.1 p.2 * A p.1 p.2 * B p.1 p.2| ∂pm)
        ≤ K * Spaces.HkNorm α 4 u * Spaces.HkNorm α 4 v := by
  obtain ⟨houter, hbd⟩ :=
    slot_pair_bound α u v hmu hmv A B V K hK hV hA0 hB0 hA hB hAmeas hBmeas hVABmeas
  have hslice : ∀ᵐ z ∂(volume.restrict Spaces.Iz),
      Integrable (fun θ => |V z θ * A z θ * B z θ|) (volume.restrict Spaces.Iθ) := by
    filter_upwards [hVABmeas.prodMk_left,
      MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hzmeas hzmem
    have hmain : Integrable (fun θ => Spaces.HkIntegrand α 4 u z θ
        + Spaces.HkIntegrand α 4 v z θ) (volume.restrict Spaces.Iθ) :=
      (hmu.1 z hzmem).add (hmv.1 z hzmem)
    refine MeasureTheory.Integrable.mono' (hmain.const_mul K) hzmeas ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_of_nonneg (abs_nonneg _)]
    have h1 := hA z hzmem θ hθ
    have h2 := hB z hzmem θ hθ
    have hn1 : 0 ≤ Spaces.HkIntegrand α 4 u z θ := Spaces.HkIntegrand_nonneg α 4 u z θ
    have hn2 : 0 ≤ Spaces.HkIntegrand α 4 v z θ := Spaces.HkIntegrand_nonneg α 4 v z θ
    rw [abs_mul, abs_mul, abs_of_nonneg (hA0 z hzmem θ hθ), abs_of_nonneg (hB0 z hzmem θ hθ)]
    have hstep : |V z θ| * A z θ * B z θ ≤ K * (A z θ * B z θ) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (hV z hzmem θ hθ)
        (mul_nonneg (hA0 z hzmem θ hθ) (hB0 z hzmem θ hθ))
    have hAB : A z θ * B z θ ≤ Spaces.HkIntegrand α 4 u z θ + Spaces.HkIntegrand α 4 v z θ := by
      nlinarith [sq_nonneg (A z θ - B z θ)]
    have hK2 : 0 ≤ K := hK
    calc |V z θ| * A z θ * B z θ ≤ K * (A z θ * B z θ) := hstep
      _ ≤ K * (Spaces.HkIntegrand α 4 u z θ + Spaces.HkIntegrand α 4 v z θ) :=
          mul_le_mul_of_nonneg_left hAB hK2
  obtain ⟨h2d, hval⟩ := Work.Spaces.integrable_prod_of_iterated
    (fun z θ => abs_nonneg _) hVABmeas hslice houter
  exact ⟨h2d, by
    rw [show pm = (MeasureTheory.volume.restrict Spaces.Iz).prod
      (MeasureTheory.volume.restrict Spaces.Iθ) from rfl, hval]
    exact hbd⟩

/-! ## The four pointwise estimates for a single Leibniz summand -/






/-! ## The Leibniz expansion of the pairing and of `T1Hard` -/





/-! ## The pointwise majorisation of the individual summands -/



/-! ## The exceptional Leibniz summand `D_z³f · D_θ²g · D_z³D_θg · Wm²`

The single summand of `EasyMajor` in which the `f`-factor carries three `D_z`-derivatives
is estimated by the two `infinity_separated` trade-offs of the paper: the angular supremum
of `D_z³f·w` (the hypothesis `K3`) for the `f`-factor, and the *radial* Hardy inequality
for the `θ`-slice of `D_θ²g` — whose `D_z`-derivative is `mixed 1 2 g`, a single `ℋ⁴`-slot —
for the `g`-factor. -/




/-- Cauchy–Schwarz (Bunyakovsky) for the product measure `pm`, in the form used by the
exceptional summand. -/
theorem cs_pm_of_nonneg {X Y : ℝ × ℝ → ℝ} (hX0 : 0 ≤ᵐ[pm] X) (hY0 : 0 ≤ᵐ[pm] Y)
    (hX : MemLp X 2 pm) (hY : MemLp Y 2 pm) :
    ∫ p, X p * Y p ∂pm
      ≤ Real.sqrt (∫ p, X p ^ 2 ∂pm) * Real.sqrt (∫ p, Y p ^ 2 ∂pm) := by
  have hX2 : MemLp X (ENNReal.ofReal (2 : ℝ)) pm := by
    rwa [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
  have hY2 : MemLp Y (ENNReal.ofReal (2 : ℝ)) pm := by
    rwa [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := pm) (p := 2) (q := 2)
    (by norm_num [Real.holderConjugate_iff]) hX0 hY0 hX2 hY2
  have hXr : ∫ p, X p ^ (2 : ℝ) ∂pm = ∫ p, X p ^ 2 ∂pm :=
    integral_congr_ae (Eventually.of_forall fun p => Real.rpow_natCast (X p) 2)
  have hYr : ∫ p, Y p ^ (2 : ℝ) ∂pm = ∫ p, Y p ^ 2 ∂pm :=
    integral_congr_ae (Eventually.of_forall fun p => Real.rpow_natCast (Y p) 2)
  rw [hXr, hYr, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h
  exact h

/-- The absolute value of an `L²`-function of the plane is again in `L²`. -/
theorem memLp_abs_pm {X : ℝ × ℝ → ℝ} (h : MemLp X 2 pm) : MemLp (fun p => |X p|) 2 pm := by
  have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ => |X p|) pm :=
    h.aestronglyMeasurable.norm.congr (Eventually.of_forall fun p => Real.norm_eq_abs (X p))
  refine (memLp_two_iff_integrable_sq haesm).mpr ?_
  have hint : Integrable (fun p : ℝ × ℝ => X p ^ 2) pm :=
    (memLp_two_iff_integrable_sq h.aestronglyMeasurable).mp h
  exact hint.congr (Eventually.of_forall fun p => (sq_abs (X p)).symm)


/-! ## The integral of the pointwise majorant `EasyMajor`

Every summand of `EasyMajor` is one of the Leibniz terms of the pairing.  Each of them is
estimated by one of `xDKf_bound`, `xDKg_bound`, `yMKf_bound`, `yMKg_bound` — the terms in
which the `f`-factor has order `≤ 2` — or, in the single exceptional case `(a,b) = (0,3)`,
by `T1ExcBoundAux`.  We bound every summand by the same multiple of the total
`Kf·|g|²_{ℋ⁴} + Kg·|f|_{ℋ⁴}|g|_{ℋ⁴} + √K3·|g|²_{ℋ⁴}`, and then sum the finitely many
of them. -/

/-- The total bound of the right-hand side of `T1EasyBound`. -/
abbrev TTot (α : ℝ) (f g : ℝ → ℝ → ℝ) (Kf Kg K3 : ℝ) : ℝ :=
  Kf * Spaces.HkSq α 4 g + Kg * Spaces.HkNorm α 4 f * Spaces.HkNorm α 4 g
    + Real.sqrt K3 * Spaces.HkSq α 4 g

theorem TTot_nonneg (α : ℝ) (f g : ℝ → ℝ → ℝ) (Kf Kg K3 : ℝ)
    (hKf : 0 ≤ Kf) (hKg : 0 ≤ Kg) (hK3 : 0 ≤ K3) : 0 ≤ TTot α f g Kf Kg K3 := by
  have h1 : 0 ≤ Kf * Spaces.HkSq α 4 g := mul_nonneg hKf (Spaces.HkSq_nonneg α 4 g)
  have h2 : 0 ≤ Kg * Spaces.HkNorm α 4 f * Spaces.HkNorm α 4 g :=
    mul_nonneg (mul_nonneg hKg (Spaces.HkNorm_nonneg α 4 f)) (Spaces.HkNorm_nonneg α 4 g)
  have h3 : 0 ≤ Real.sqrt K3 * Spaces.HkSq α 4 g :=
    mul_nonneg (Real.sqrt_nonneg _) (Spaces.HkSq_nonneg α 4 g)
  rw [TTot]
  linarith

theorem le_TTot_Kf (α : ℝ) (f g : ℝ → ℝ → ℝ) (Kf Kg K3 : ℝ)
    (hKg : 0 ≤ Kg) (hK3 : 0 ≤ K3) : Kf * Spaces.HkSq α 4 g ≤ TTot α f g Kf Kg K3 := by
  have h2 : 0 ≤ Kg * Spaces.HkNorm α 4 f * Spaces.HkNorm α 4 g :=
    mul_nonneg (mul_nonneg hKg (Spaces.HkNorm_nonneg α 4 f)) (Spaces.HkNorm_nonneg α 4 g)
  have h3 : 0 ≤ Real.sqrt K3 * Spaces.HkSq α 4 g :=
    mul_nonneg (Real.sqrt_nonneg _) (Spaces.HkSq_nonneg α 4 g)
  rw [TTot]
  linarith

theorem le_TTot_Kg (α : ℝ) (f g : ℝ → ℝ → ℝ) (Kf Kg K3 : ℝ)
    (hKf : 0 ≤ Kf) (hK3 : 0 ≤ K3) :
    Kg * Spaces.HkNorm α 4 f * Spaces.HkNorm α 4 g ≤ TTot α f g Kf Kg K3 := by
  have h1 : 0 ≤ Kf * Spaces.HkSq α 4 g := mul_nonneg hKf (Spaces.HkSq_nonneg α 4 g)
  have h3 : 0 ≤ Real.sqrt K3 * Spaces.HkSq α 4 g :=
    mul_nonneg (Real.sqrt_nonneg _) (Spaces.HkSq_nonneg α 4 g)
  rw [TTot]
  linarith

theorem le_TTot_sqrt (α : ℝ) (f g : ℝ → ℝ → ℝ) (Kf Kg K3 : ℝ)
    (hKf : 0 ≤ Kf) (hKg : 0 ≤ Kg) :
    Real.sqrt K3 * Spaces.HkSq α 4 g ≤ TTot α f g Kf Kg K3 := by
  have h1 : 0 ≤ Kf * Spaces.HkSq α 4 g := mul_nonneg hKf (Spaces.HkSq_nonneg α 4 g)
  have h2 : 0 ≤ Kg * Spaces.HkNorm α 4 f * Spaces.HkNorm α 4 g :=
    mul_nonneg (mul_nonneg hKg (Spaces.HkNorm_nonneg α 4 f)) (Spaces.HkNorm_nonneg α 4 g)
  rw [TTot]
  linarith











/-- The absolute value of an a.e. strongly measurable function of the plane is a.e. strongly
measurable. -/
theorem abs_aesm_pm {F : ℝ × ℝ → ℝ} (h : AEStronglyMeasurable F pm) :
    AEStronglyMeasurable (fun p => |F p|) pm :=
  h.norm.congr (Eventually.of_forall fun p => Real.norm_eq_abs (F p))

theorem choose_le_16 {i b : ℕ} (hi : i ≤ 4) (hb : b ≤ i) : (i.choose b : ℝ) ≤ 16 := by
  have h1 : i.choose b ≤ 2 ^ i := Nat.choose_le_two_pow i b
  have h2 : (2 : ℕ) ^ i ≤ 2 ^ 4 := pow_le_pow_right' (show (1 : ℕ) ≤ 2 by norm_num) hi
  have h3 : i.choose b ≤ 2 ^ 4 := le_trans h1 h2
  have h3' : i.choose b ≤ 16 := by norm_num at h3 ⊢; exact h3
  exact_mod_cast h3'

theorem choose_mul_le_256 {i j a b : ℕ} (hi : i ≤ 4) (hai : a ≤ i) (hj : j ≤ 4) (hbj : b ≤ j) :
    (i.choose a : ℝ) * (j.choose b : ℝ) ≤ 256 := by
  have h1 : (i.choose a : ℝ) ≤ 16 := choose_le_16 hi hai
  have h2 : (j.choose b : ℝ) ≤ 16 := choose_le_16 hj hbj
  have h4 : 0 ≤ (j.choose b : ℝ) := by positivity
  calc (i.choose a : ℝ) * (j.choose b : ℝ) ≤ 16 * 16 :=
        mul_le_mul h1 h2 h4 (by norm_num)
    _ = 256 := by norm_num



/-- Assembly step: a `D_z`-slot summand dominated by `c` times an integrable slot. -/
theorem xD_finish {f g : ℝ → ℝ → ℝ} {i b : ℕ} {c K : ℝ} {S : ℝ × ℝ → ℝ} (hc0 : 0 ≤ c)
    (hslot_int : MeasureTheory.Integrable S pm)
    (hslot_le : ∫ p, S p ∂pm ≤ K)
    (hle : ∀ᵐ p ∂pm, |xD f g i b p.1 p.2| ≤ c * S p)
    (haesm : AEStronglyMeasurable (fun p : ℝ × ℝ => |xD f g i b p.1 p.2|) pm) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => |xD f g i b p.1 p.2|) pm ∧
      ∫ p, |xD f g i b p.1 p.2| ∂pm ≤ c * K := by
  have hint : MeasureTheory.Integrable (fun p : ℝ × ℝ => |xD f g i b p.1 p.2|) pm := by
    refine MeasureTheory.Integrable.mono' (hslot_int.const_mul c) haesm ?_
    filter_upwards [hle] with p hp
    rw [Real.norm_of_nonneg (abs_nonneg _)]
    exact hp
  refine ⟨hint, ?_⟩
  have h1 : ∫ p, |xD f g i b p.1 p.2| ∂pm ≤ ∫ p, c * S p ∂pm := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun p => abs_nonneg _)
      (hslot_int.const_mul c) ?_
    filter_upwards [hle] with p hp
    exact hp
  rw [integral_const_mul] at h1
  exact le_trans h1 (mul_le_mul_of_nonneg_left hslot_le hc0)

/-- Assembly step: a mixed-slot summand dominated by `c` times an integrable slot. -/
theorem yM_finish {α : ℝ} {f g : ℝ → ℝ → ℝ} {i j a b : ℕ} {c K : ℝ} {S : ℝ × ℝ → ℝ}
    (hc0 : 0 ≤ c) (hslot_int : MeasureTheory.Integrable S pm)
    (hslot_le : ∫ p, S p ∂pm ≤ K)
    (hle : ∀ᵐ p ∂pm, |yM α f g i j a b p.1 p.2| ≤ c * S p)
    (haesm : AEStronglyMeasurable (fun p : ℝ × ℝ => |yM α f g i j a b p.1 p.2|) pm) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => |yM α f g i j a b p.1 p.2|) pm ∧
      ∫ p, |yM α f g i j a b p.1 p.2| ∂pm ≤ c * K := by
  have hint : MeasureTheory.Integrable (fun p : ℝ × ℝ => |yM α f g i j a b p.1 p.2|) pm := by
    refine MeasureTheory.Integrable.mono' (hslot_int.const_mul c) haesm ?_
    filter_upwards [hle] with p hp
    rw [Real.norm_of_nonneg (abs_nonneg _)]
    exact hp
  refine ⟨hint, ?_⟩
  have h1 : ∫ p, |yM α f g i j a b p.1 p.2| ∂pm ≤ ∫ p, c * S p ∂pm := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun p => abs_nonneg _)
      (hslot_int.const_mul c) ?_
    filter_upwards [hle] with p hp
    exact hp
  rw [integral_const_mul] at h1
  exact le_trans h1 (mul_le_mul_of_nonneg_left hslot_le hc0)



/-- The `D_z`-slot term of `EasyMajor`. -/
abbrev EMx (f g : ℝ → ℝ → ℝ) (i b : ℕ) (p : ℝ × ℝ) : ℝ :=
  if i = 4 ∧ b = 0 then 0 else |xD f g i b p.1 p.2|

/-- The `(a,b)`-summand of a mixed slot of `EasyMajor` (with the hard terms removed). -/
abbrev EMyA (α : ℝ) (f g : ℝ → ℝ → ℝ) (i j a b : ℕ) (p : ℝ × ℝ) : ℝ :=
  if 1 ≤ i ∧ i + j ≤ 4 then
    (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b p.1 p.2|)
  else 0

/-- The `(i,j)`-summand of the mixed part of `EasyMajor`. -/
abbrev EMy (α : ℝ) (f g : ℝ → ℝ → ℝ) (i j : ℕ) (p : ℝ × ℝ) : ℝ :=
  ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), EMyA α f g i j a b p

/-- `EasyMajor` as a function of the plane variable. -/
abbrev EMS (α : ℝ) (f g : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1), EMx f g i b p)
    + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, EMy α f g i j p

/-- `EMS` is `EasyMajor` evaluated at the pair. -/
theorem EasyMajor_eq_EMS (α : ℝ) (f g : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    EasyMajor α f g p.1 p.2 = EMS α f g p := by
  simp only [EasyMajor, EMS, EMx, EMy, EMyA]
  rw [add_right_inj]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hc : 1 ≤ i ∧ i + j ≤ 4
  · simp only [if_pos hc]
  · simp only [if_neg hc, Finset.sum_const_zero]

theorem sum_range_range_le_25 (c : ℝ) (hc : 0 ≤ c) :
    (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1), c) ≤ 25 * c := by
  calc (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1), c)
      ≤ ∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range 5, c := by
        refine Finset.sum_le_sum fun i hi => ?_
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun b _ _ => hc)
        exact Finset.range_subset_range.mpr (by have := Finset.mem_range.mp hi; omega)
    _ = 25 * c := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

theorem sum_le_25_of_le4 (c : ℝ) (hc : 0 ≤ c) (i j : ℕ) (hi : i ≤ 4) (hj : j ≤ 4) :
    (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), c) ≤ 25 * c := by
  have hsub1 : Finset.range (i + 1) ⊆ Finset.range 5 :=
    Finset.range_subset_range.mpr (by omega)
  have hsub2 : Finset.range (j + 1) ⊆ Finset.range 5 :=
    Finset.range_subset_range.mpr (by omega)
  calc (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), c)
      ≤ ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range 5, c := by
        refine Finset.sum_le_sum fun a ha => ?_
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun b _ _ => hc)
    _ ≤ ∑ a ∈ Finset.range 5, ∑ b ∈ Finset.range 5, c := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub1 (fun a _ _ => ?_)
        exact Finset.sum_nonneg fun b _ => hc
    _ = 25 * c := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring


/-! ## Continuity of `T1Easy` on the open quadrant (used for measurability) -/











end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.H2.ZibpLimit =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

/-! ## Auxiliary lemmas for `ZibpLimit`

The primitive `u z = ∫_θ ZG α f g z θ` satisfies the pointwise bound
`|u z| ≤ (M/2) z w(z)² V(z)` with `V(z) = ∫_θ ZU α g z θ` (`abs_ZibpU_le`), and a function
dominated below by `c/z` on a ray `[Z,∞)` or near `0⁺`, with `c > 0`, cannot be integrable on
`[0,∞)` (`not_integrableOn_Ici_of_le_inv_atTop`, `not_integrableOn_Ici_of_le_inv_nearZero`).
Both facts use the divergence of `∫ z⁻¹`: the function `log` is differentiable with
`deriv log = 1/z` and `‖log z‖ → ∞` along the relevant filter, so Mathlib's
`not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter` applies as soon as the
dominating lower bound shows `deriv log = O F`. -/








end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6.HkN_sepF_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

/-! ## The `ℋ^k`-integrand of a separated `a(z)·ψ(θ)` against a `z`-core and a `θ`-core

This is the "core" computation of `Work.Construction.HkN_GammaTerm_sep_le_aux`, freed
from the two concrete factors `Kfac α` and `rhoR`: for an arbitrary radial profile `a`
satisfying the `z`-core hypothesis

`|(D_z^j a)(z)·w(z)| ≤ M/(1+z)`  (`j ≤ k`)

and the angular core hypothesis on `ψ = psiA α`

`|(D_θ^i ψ)(θ)| ≤ D·Γ(θ)·(sin(2θ)² + α)`  (`1 ≤ i ≤ k`),

the `ℋ^k`-integrand of the separated function `F = a·ψ` is dominated by the separable
majorant `(M/(1+z))²·(4(k+1)·sin(2θ)^{-η} + 2(k+1)²D²(sin(2θ)^{-η} + α²sin(2θ)^{2α/3-γ}))`.

The pure `D_z`-slots contribute `4(k+1)·sin(2θ)^{-η}` (each term is `≤ (M/(1+z))²·4·sin^{-η}`
by `sq_mul_div_sin` + `|ψ| ≤ 2`), the mixed slots contribute `2(k+1)²D²(...)` each (by
`bt_Wt_sq` + `mixed_angle_le`), and there are `k+1` resp. `(k+1)²` of them.  At the angular
boundary `sin(2θ) = 0` everything vanishes (`HkIntegrand_eq_zero_of_sin_two_eq_zero`). -/
theorem HkN_sepF_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {a : ℝ → ℝ} {M D : ℝ}
    (hM : 0 < M) (hD : 0 < D) (k : ℕ)
    (hMr : ∀ j : ℕ, j ≤ k → ∀ z : ℝ, 0 ≤ z →
      |(Work.Spaces.Zop^[j] a) z * Work.Spaces.w z| ≤ M / (1 + z))
    (hDl : ∀ i : ℕ, 1 ≤ i → i ≤ k → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |(Work.Spaces.Lop^[i] (Work.Construction.psiA α)) θ|
        ≤ D * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α)) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (Work.Construction.sepF a (Work.Construction.psiA α)) z θ
        ≤ (M / (1 + z)) ^ 2
          * (4 * ((k : ℝ) + 1) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + 2 * ((k : ℝ) + 1) ^ 2 * D ^ 2
                * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                    + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) := by
  intro z hz θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) := Work.Construction.sin_two_nonneg_of_mem_Iθ hθ
  have h1z : 0 < 1 + z := by have hz0 : (0 : ℝ) ≤ z := hz; linarith
  by_cases hθi : θ ∈ Set.Ioo 0 (Real.pi / 2)
  · -- interior of the angular interval: bound the pure and the mixed slots termwise
    have hbnd : ∀ j : ℕ, j ≤ k →
        ((Work.Spaces.Zop^[j] a) z * Work.Spaces.w z) ^ 2 ≤ (M / (1 + z)) ^ 2 := by
      intro j hj
      have hb := hMr j hj z hz
      have hMnn : (0 : ℝ) ≤ M / (1 + z) := div_nonneg hM.le h1z.le
      rw [sq_le_sq, abs_of_nonneg hMnn]
      exact hb
    have hψ2 : (Work.Construction.psiA α θ) ^ 2 ≤ 4 := by
      have h := mul_self_le_mul_self (abs_nonneg (Work.Construction.psiA α θ))
        (Work.Construction.psiA_abs_le_two hα hθ)
      have h2 := sq_abs (Work.Construction.psiA α θ)
      nlinarith [h, h2]
    have hpure : ∀ i : ℕ, i ≤ k →
        (Work.Spaces.DzIter i (Work.Construction.sepF a (Work.Construction.psiA α)) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ (M / (1 + z)) ^ 2 * (4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
      intro i hi
      have hsep : Work.Spaces.DzIter i
            (Work.Construction.sepF a (Work.Construction.psiA α)) z θ
          = (Work.Spaces.Zop^[i] a) z * Work.Construction.psiA α θ := by
        rw [Work.Construction.sepF_DzIter]
        rfl
      have hsq := hbnd i hi
      calc (Work.Spaces.DzIter i (Work.Construction.sepF a (Work.Construction.psiA α)) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          = ((Work.Spaces.Zop^[i] a) z * Work.Spaces.w z) ^ 2
              * (Work.Construction.psiA α θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
            rw [hsep]
            rw [Work.Elliptic.sq_mul_div_sin (z := z) (θ := θ)
              (a := (Work.Spaces.Zop^[i] a) z * Work.Construction.psiA α θ) hθ]
            ring
        _ ≤ (M / (1 + z)) ^ 2 * 4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul hsq hψ2 (sq_nonneg _) (sq_nonneg _))
              (Real.rpow_nonneg hs0 _)
        _ = (M / (1 + z)) ^ 2 * (4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by ring
    have hmixed : ∀ i j : ℕ, 1 ≤ i → i + j ≤ k →
        (Work.Spaces.mixed j i (Work.Construction.sepF a (Work.Construction.psiA α)) z θ
            * Work.Spaces.Wt α z θ) ^ 2
          ≤ (M / (1 + z)) ^ 2
            * (2 * D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) := by
      intro i j hi hij
      have hsep : Work.Spaces.mixed j i
            (Work.Construction.sepF a (Work.Construction.psiA α)) z θ
          = (Work.Spaces.Zop^[j] a) z * (Work.Spaces.Lop^[i] (Work.Construction.psiA α)) θ := by
        rw [Work.Construction.sepF_mixed]
        rfl
      have hsq := hbnd j (by omega)
      have hcore := hDl i hi (by omega) θ hθi
      have hang := Work.Construction.mixed_angle_le hα hα1 hD.le hθ hcore
      calc (Work.Spaces.mixed j i (Work.Construction.sepF a (Work.Construction.psiA α)) z θ
            * Work.Spaces.Wt α z θ) ^ 2
          = ((Work.Spaces.Zop^[j] a) z * Work.Spaces.w z) ^ 2
              * (((Work.Spaces.Lop^[i] (Work.Construction.psiA α)) θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
            rw [hsep, mul_pow, Work.Spaces.bt_Wt_sq α z θ hα hθ]
            ring
        _ ≤ (M / (1 + z)) ^ 2
              * (2 * D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                  + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) :=
            mul_le_mul hsq hang
              (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)) (sq_nonneg _)
    rw [Work.Spaces.HkIntegrand]
    have hZsum : (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i (Work.Construction.sepF a (Work.Construction.psiA α)) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ (M / (1 + z)) ^ 2
            * (4 * ((k : ℝ) + 1) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
      calc ∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i (Work.Construction.sepF a (Work.Construction.psiA α)) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ ∑ _i ∈ Finset.range (k + 1),
              ((M / (1 + z)) ^ 2 * (4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) :=
            Finset.sum_le_sum fun i hi =>
              hpure i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
        _ = (M / (1 + z)) ^ 2
              * (4 * ((k : ℝ) + 1) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    have hMsum : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (Work.Construction.sepF a (Work.Construction.psiA α)) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ (M / (1 + z)) ^ 2
            * (2 * ((k : ℝ) + 1) ^ 2 * D ^ 2
                * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                    + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) := by
      set Y : ℝ := (M / (1 + z)) ^ 2
          * (2 * D ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) with hYdef
      have hYnn : 0 ≤ Y := by
        rw [hYdef]
        exact mul_nonneg (sq_nonneg _)
          (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg D))
            (add_nonneg (Real.rpow_nonneg hs0 _)
              (mul_nonneg (sq_nonneg α) (Real.rpow_nonneg hs0 _))))
      calc ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i (Work.Construction.sepF a (Work.Construction.psiA α)) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0)
          ≤ ∑ _i ∈ Finset.range (k + 1), ∑ _j ∈ Finset.range (k + 1), Y :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
              by_cases hc : 1 ≤ i ∧ i + j ≤ k
              · rw [if_pos hc]; exact hmixed i j hc.1 hc.2
              · rw [if_neg hc]; exact hYnn
        _ = (M / (1 + z)) ^ 2
              * (2 * ((k : ℝ) + 1) ^ 2 * D ^ 2
                  * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                      + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
              Finset.sum_const, Finset.card_range, nsmul_eq_mul, hYdef]
            push_cast
            ring
    calc ∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i (Work.Construction.sepF a (Work.Construction.psiA α)) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i (Work.Construction.sepF a (Work.Construction.psiA α)) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ ((M / (1 + z)) ^ 2
              * (4 * ((k : ℝ) + 1) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
          + ((M / (1 + z)) ^ 2
              * (2 * ((k : ℝ) + 1) ^ 2 * D ^ 2
                  * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                      + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)))) :=
          add_le_add hZsum hMsum
      _ = (M / (1 + z)) ^ 2
            * (4 * ((k : ℝ) + 1) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + 2 * ((k : ℝ) + 1) ^ 2 * D ^ 2
                  * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                      + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) := by
          ring
  · -- angular boundary: `sin(2θ) = 0`, and every term of the integrand vanishes
    have hs : Real.sin (2 * θ) = 0 :=
      Work.Spaces.sin_two_mul_eq_zero_of_mem_Iθ_of_not_mem_Ioo hθ hθi
    rw [Work.Construction.HkIntegrand_eq_zero_of_sin_two_eq_zero hα hs]
    have h0 : (4 * ((k : ℝ) + 1) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        + 2 * ((k : ℝ) + 1) ^ 2 * D ^ 2
          * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))) = 0 := by
      rw [hs,
        Real.zero_rpow (by linarith [Work.Spaces.eta_pos] :
          (-(Work.Spaces.eta)) ≠ 0),
        Real.zero_rpow (by rw [Work.Spaces.gam]; intro hh; linarith :
          (2 * α / 3 - Work.Spaces.gam α) ≠ 0)]
      ring
    rw [h0]
    simp

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6
end
