import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.dzSelf2dW
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.dzSelf2d
import Submission.Work.StabilityFar.Decay.hasDerivAt_biotSavart
import Submission.Work.StabilityFar.Decay.hasDerivAt_bsK
import Submission.Work.StabilityFar.Decay.norm_kDerivCLM_sub_le
import Submission.Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Metric Filter
open scoped Topology
open Work.StabilityFar.Decay (kf kDerivCLM crossL)

/-! ## Auxiliary lemmas for the difference-quotient estimate

These are the elementary integrability, measurability and shape-term facts on which the
assembly of `norm_bsField_diff_bound` rests.  They are stated in the vocabulary of
`Work.StabilityFar.Decay` (`kf`, `kDerivCLM`, `crossL`) and of `bsIntegrand`/`resid`. -/

/-- Centred radial power integral. -/
lemma integrableOn_norm_rpow_ball_zero (s : ℝ) (hs : -3 < s) (r : ℝ) :
    IntegrableOn (fun a : Work.LWP.R3 => (‖a‖ : ℝ) ^ s) (Metric.ball (0 : Work.LWP.R3) r)
      volume := by
  rcases le_or_gt r 0 with hr | hr
  · rw [Metric.ball_eq_empty.mpr hr]; exact integrableOn_empty
  · by_contra hcon
    have h0 := integral_undef hcon
    have hval := radial_rpow_integral s hs r hr
    rw [hval] at h0
    have hpos : 0 < 4 * Real.pi * r ^ (s + 3) / (s + 3) :=
      div_pos (mul_pos (by positivity) (Real.rpow_pos_of_pos hr _)) (by linarith)
    exact absurd h0 (ne_of_gt hpos)

/-- Shifted radial power integral on a ball centred at the origin. -/
lemma integrableOn_norm_sub_rpow_ball_origin (y : Work.LWP.R3) (s : ℝ) (hs : -3 < s) (ρ : ℝ) :
    IntegrableOn (fun a : Work.LWP.R3 => (‖y - a‖ : ℝ) ^ s) (Metric.ball (0 : Work.LWP.R3) ρ)
      volume := by
  rcases le_or_gt ρ 0 with hρ | hρ
  · rw [Metric.ball_eq_empty.mpr hρ]; exact integrableOn_empty
  have hbig : IntegrableOn (fun b : Work.LWP.R3 => (‖b‖ : ℝ) ^ s)
      (Metric.ball (0 : Work.LWP.R3) (ρ + ‖y‖)) volume :=
    integrableOn_norm_rpow_ball_zero s hs (ρ + ‖y‖)
  have hmono : IntegrableOn (fun b : Work.LWP.R3 => (‖b‖ : ℝ) ^ s) (Metric.ball y ρ) volume :=
    hbig.mono_set (fun b hb => by
      have h2 : ‖b - y‖ < ρ := by
        rw [Metric.mem_ball, dist_eq_norm] at hb
        exact hb
      rw [Metric.mem_ball, dist_zero_right]
      calc ‖b‖ = ‖(b - y) + y‖ := by rw [sub_add_cancel]
        _ ≤ ‖b - y‖ + ‖y‖ := norm_add_le _ _
        _ < ρ + ‖y‖ := by linarith)
  have hmp : MeasurePreserving (fun a : Work.LWP.R3 => y - a) volume volume :=
    MeasureTheory.Measure.measurePreserving_sub_left volume y
  have hemb : MeasurableEmbedding (fun a : Work.LWP.R3 => y - a) :=
    (MeasurableEquiv.subLeft y).measurableEmbedding
  have hpre : (fun a : Work.LWP.R3 => y - a) ⁻¹' (Metric.ball y ρ)
      = Metric.ball (0 : Work.LWP.R3) ρ := by
    ext a
    simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, sub_zero]
    rw [show (y - a) - y = -a by abel, norm_neg]
  rw [← hpre]
  have hfin := (hmp.integrableOn_comp_preimage hemb
    (f := fun b : Work.LWP.R3 => (‖b‖ : ℝ) ^ s) (s := Metric.ball y ρ)).mpr hmono
  simpa [Function.comp_def] using hfin

/-- Domination criterion for integrability on a ball. -/
lemma integrableOn_of_norm_le_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Work.LWP.R3 → E} {g : Work.LWP.R3 → ℝ} {ρ : ℝ}
    (hg : IntegrableOn g (Metric.ball (0 : Work.LWP.R3) ρ) volume)
    (hf : AEStronglyMeasurable f volume)
    (h : ∀ a ∈ Metric.ball (0 : Work.LWP.R3) ρ, ‖f a‖ ≤ g a) :
    IntegrableOn f (Metric.ball (0 : Work.LWP.R3) ρ) volume := by
  refine Integrable.mono' hg (hf.mono_measure Measure.restrict_le_self) ?_
  rw [MeasureTheory.ae_restrict_iff' measurableSet_ball]
  exact Filter.Eventually.of_forall fun a ha => h a ha

/-! ## Algebraic and analytic helpers -/

/-- `crossL u w = crossL (u - v) w + crossL v w`. -/
lemma crossL_omega_split (u v w : Work.LWP.R3) : crossL u w = crossL (u - v) w + crossL v w := by
  rw [← add_apply, ← Work.StabilityFar.Decay.crossL_add, sub_add_cancel]

/-- `‖b‖ ^ c * ‖b‖ ^ (-3) = ‖b‖ ^ (c - 3)` for `c ≠ 0`. -/
lemma rpow_mul_rpow_neg_three (b : Work.LWP.R3) {c : ℝ} (hc : c ≠ 0) (hc3 : c ≠ 3) :
    (‖b‖ : ℝ) ^ c * (‖b‖ : ℝ) ^ (-3:ℝ) = (‖b‖ : ℝ) ^ (c - 3) := by
  rcases eq_or_lt_of_le (norm_nonneg b) with h0 | hpos
  · rw [← h0, Real.zero_rpow hc, Real.zero_rpow (by norm_num : (-3:ℝ) ≠ 0),
      Real.zero_rpow (sub_ne_zero.mpr hc3), mul_zero]
  · rw [← Real.rpow_add hpos, show c + (-3) = c - 3 by ring]

/-- A `c`-Hölder field with `c > 0` and nonnegative Hölder constant is continuous. -/
theorem continuous_of_holder' {ω : Work.LWP.R3 → Work.LWP.R3} {C c : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hhold : ∀ a b : Work.LWP.R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c) : Continuous ω := by
  rw [Metric.continuous_iff]
  intro a ε hε
  by_cases hC0 : C = 0
  · refine ⟨1, one_pos, fun b _ => ?_⟩
    have hsub : ‖ω b - ω a‖ ≤ 0 := by
      calc ‖ω b - ω a‖ ≤ C * ‖b - a‖ ^ c := hhold b a
        _ = 0 := by rw [hC0]; ring
    rw [dist_eq_norm, le_antisymm hsub (norm_nonneg _)]
    simpa using hε
  · have hCpos : 0 < C := lt_of_le_of_ne' hC hC0
    have hbase : 0 < ε / C := by positivity
    refine ⟨(ε / C) ^ (1 / c), Real.rpow_pos_of_pos hbase _, fun b hb => ?_⟩
    rw [dist_eq_norm] at hb ⊢
    have hbc : ‖b - a‖ ^ c < ε / C := by
      have h := Real.rpow_lt_rpow (norm_nonneg _) hb (by positivity : (0:ℝ) < c)
      rwa [← Real.rpow_mul (le_of_lt hbase), one_div_mul_cancel hc.ne', Real.rpow_one] at h
    calc ‖ω b - ω a‖ ≤ C * ‖b - a‖ ^ c := hhold b a
      _ < C * (ε / C) := mul_lt_mul_of_pos_left hbc hCpos
      _ = ε := by field_simp

/-- Measurability of `a ↦ crossL (u a) (kf (y - a))`. -/
lemma aestronglyMeasurable_crossL_kf {u : Work.LWP.R3 → Work.LWP.R3}
    (hu : AEStronglyMeasurable u volume) (y : Work.LWP.R3) :
    AEStronglyMeasurable (fun a : Work.LWP.R3 => crossL (u a) (kf (y - a))) volume := by
  have h := Work.LWP.BiotSavart.aestronglyMeasurable_bsK hu y
  exact h.congr (Filter.Eventually.of_forall
    (fun a => Work.StabilityFar.Decay.bsK_eq_crossL u y a))

/-- `a ↦ kf (y - a)` is integrable on any ball centred at the origin. -/
lemma integrableOn_kf_sub (y : Work.LWP.R3) (ρ : ℝ) :
    IntegrableOn (fun a : Work.LWP.R3 => kf (y - a)) (Metric.ball (0 : Work.LWP.R3) ρ)
      volume := by
  have hg : IntegrableOn (fun a : Work.LWP.R3 => (‖y - a‖ : ℝ) ^ (-2:ℝ))
      (Metric.ball (0 : Work.LWP.R3) ρ) volume :=
    integrableOn_norm_sub_rpow_ball_origin y (-2) (by norm_num) ρ
  have hmeas : AEStronglyMeasurable (fun a : Work.LWP.R3 => kf (y - a)) volume := by
    have h1 : AEStronglyMeasurable (fun a : Work.LWP.R3 => (‖y - a‖ ^ (3:ℕ))⁻¹) volume :=
      (Measurable.inv (by fun_prop : Measurable fun a : Work.LWP.R3 => ‖y - a‖ ^ (3:ℕ))).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun a : Work.LWP.R3 => y - a) volume :=
      (continuous_const.sub continuous_id).aestronglyMeasurable
    have h3 : AEStronglyMeasurable
        (fun a : Work.LWP.R3 => (‖y - a‖ ^ (3:ℕ))⁻¹ • (y - a)) volume := h1.smul h2
    simpa [Work.StabilityFar.Decay.kf] using h3
  refine integrableOn_of_norm_le_ball hg hmeas (fun a _ => ?_)
  rw [norm_kf_eq]

/-- `a ↦ kf (y - a) - kf (z - a)` is integrable on any ball centred at the origin. -/
lemma integrableOn_kf_diff (y z : Work.LWP.R3) (ρ : ℝ) :
    IntegrableOn (fun a : Work.LWP.R3 => kf (y - a) - kf (z - a)) (Metric.ball (0 : Work.LWP.R3) ρ)
      volume :=
  (integrableOn_kf_sub y ρ).sub (integrableOn_kf_sub z ρ)

/-- The shape-term identity: `∫_{B(0,ρ)} (kf (x+h-a) - kf (x-a)) = (4π/3) • h`. -/
lemma integral_kf_diff_ball {x h : Work.LWP.R3} {ρ : ℝ} (hx : ‖x‖ < ρ) (hxh : ‖x + h‖ < ρ) :
    ∫ a in Metric.ball (0 : Work.LWP.R3) ρ, (kf (x + h - a) - kf (x - a))
      = (4 * Real.pi / 3) • h := by
  have hρ : 0 < ρ := lt_of_le_of_lt (norm_nonneg x) hx
  have hI1 : IntegrableOn (fun a : Work.LWP.R3 => kf (x + h - a)) (Metric.ball (0 : Work.LWP.R3) ρ) volume :=
    integrableOn_kf_sub (x + h) ρ
  have hI2 : IntegrableOn (fun a : Work.LWP.R3 => kf (x - a)) (Metric.ball (0 : Work.LWP.R3) ρ) volume :=
    integrableOn_kf_sub x ρ
  rw [integral_sub hI1 hI2, integral_kf_sub_left ρ (x + h), integral_kf_sub_left ρ x,
    kf_ball_integral ρ hρ (x + h) hxh, kf_ball_integral ρ hρ x hx, smul_add]
  abel

/-- Integrability of the derivative integrand on a ball. -/
lemma integrableOn_bsIntegrand_ball {ω : Work.LWP.R3 → Work.LWP.R3} {C c : ℝ} (hc : 0 < c)
    (hC : 0 ≤ C) (hhold : ∀ a b : Work.LWP.R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c)
    (x : Work.LWP.R3) (ρ : ℝ) :
    IntegrableOn (bsIntegrand ω x) (Metric.ball (0 : Work.LWP.R3) ρ) volume := by
  have hω : Continuous ω := continuous_of_holder' hc hC hhold
  have hg : IntegrableOn (fun a : Work.LWP.R3 => 4 * C * (‖x - a‖ : ℝ) ^ (c - 3))
      (Metric.ball (0 : Work.LWP.R3) ρ) volume :=
    MeasureTheory.Integrable.const_mul
      (integrableOn_norm_sub_rpow_ball_origin x (c - 3) (by linarith) ρ) (4 * C)
  exact integrableOn_of_norm_le_ball hg (aestronglyMeasurable_bsIntegrand hω x)
    (fun a _ => norm_bsIntegrand_le hC hhold x a)


/-- **The difference-quotient estimate for `bsField`.**  For a vorticity `ω` which is bounded by
`M`, supported in `closedBall 0 R` and Hölder of exponent `c ∈ (0,1)`, the difference
`bsField ω ρ (x+h) - bsField ω ρ x` is approximated by `(bsDerivCLM ω ρ x) h` with an error of
order `‖h‖^{1+c}`, *uniformly* in `ρ`, `x` and `h` (`ρ > R + ‖x‖ + ‖h‖`).

Proof: `bsField_sub` turns the difference into `∫_{B(0,ρ)} crossL (ω a) (kf(x+h-a) - kf(x-a))`.
Splitting `crossL (ω a) = crossL (ω a - ω x) + crossL (ω x)`, the second piece equals
`crossL (ω x) ((4π/3)•h)` by `integral_kf_sub_left` + `kf_ball_integral`, which is exactly the
shape term of `bsDerivCLM`; the first piece splits into the linear term
`∫ crossL (ω a - ω x) (kDerivCLM (x-a) h)` (whose CLM integral is the definition of
`bsDerivCLM`'s first summand) plus the Taylor remainder, bounded by `norm_taylor_error_le`. -/
theorem norm_bsField_diff_bound {ω : Work.LWP.R3 → Work.LWP.R3} {R M C c : ℝ} (hR : 0 < R)
    (hM : 0 ≤ M) (hc : 0 < c) (hc1 : c < 1) (hC : 0 ≤ C) (hbdd : ∀ a, ‖ω a‖ ≤ M)
    (hs : ∀ a, ω a ≠ 0 → a ∈ Metric.closedBall 0 R)
    (hm : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume)
    (hhold : ∀ a b : Work.LWP.R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ρ : ℝ) (x h : Work.LWP.R3), R + ‖x‖ + ‖h‖ < ρ →
      ‖Work.CoreResiduals.BiotSavart.bsField ω ρ (x + h) - Work.CoreResiduals.BiotSavart.bsField ω ρ x
        - Work.CoreResiduals.BiotSavart.bsDerivCLM ω ρ x h‖ ≤ K * ‖h‖ ^ (1 + c) := by
  obtain ⟨K, hK0, hK⟩ := norm_taylor_error_le (ω := ω) hc hc1 hC hhold
  refine ⟨K, hK0, fun ρ x h hρ => ?_⟩
  by_cases hh : h = 0
  · subst hh
    have hzero : bsField ω ρ (x + 0) - bsField ω ρ x - bsDerivCLM ω ρ x 0 = 0 := by
      rw [add_zero, ContinuousLinearMap.map_zero, sub_zero, sub_self]
    have h0 : (0:ℝ) ^ (1 + c) = 0 := Real.zero_rpow (by linarith : (1:ℝ) + c ≠ 0)
    simp only [hzero, h0, norm_zero, mul_zero, le_refl]
  have hxρ : ‖x‖ < ρ := by
    have h1 : (0:ℝ) ≤ ‖h‖ := norm_nonneg h
    have h2 : (0:ℝ) ≤ ‖x‖ := norm_nonneg x
    linarith
  have hxhρ : ‖x + h‖ < ρ := by
    have h1 : ‖x + h‖ ≤ ‖x‖ + ‖h‖ := norm_add_le x h
    linarith
  have hωc : Continuous ω := continuous_of_holder' hc hC hhold
  have hu : AEStronglyMeasurable (fun b : Work.LWP.R3 => ω b - ω x) volume :=
    hm.sub aestronglyMeasurable_const
  have hDnn : (0:ℝ) ≤ ρ + ‖x‖ := by
    have : 0 < ρ := lt_of_le_of_lt (norm_nonneg x) hxρ
    positivity
  have hwbound : ∀ a ∈ Metric.ball (0 : Work.LWP.R3) ρ,
      ‖ω a - ω x‖ ≤ C * (ρ + ‖x‖) ^ c := by
    intro a ha
    have h1 : ‖a - x‖ ≤ ρ + ‖x‖ := by
      rw [Metric.mem_ball, dist_zero_right] at ha
      calc ‖a - x‖ ≤ ‖a‖ + ‖x‖ := norm_sub_le a x
        _ ≤ ρ + ‖x‖ := by linarith [le_of_lt ha]
    calc ‖ω a - ω x‖ ≤ C * ‖a - x‖ ^ c := hhold a x
      _ ≤ C * (ρ + ‖x‖) ^ c :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) h1 hc.le) hC
  -- integrability of the four pieces
  have hΔint : IntegrableOn (fun a : Work.LWP.R3 => kf (x + h - a) - kf (x - a))
      (Metric.ball (0 : Work.LWP.R3) ρ) volume := integrableOn_kf_diff (x + h) x ρ
  have hbsIint : IntegrableOn (bsIntegrand ω x) (Metric.ball (0 : Work.LWP.R3) ρ) volume :=
    integrableOn_bsIntegrand_ball hc hC hhold x ρ
  have hf2int : IntegrableOn (fun a : Work.LWP.R3 =>
      crossL (ω a - ω x) (kf (x + h - a) - kf (x - a))) (Metric.ball (0 : Work.LWP.R3) ρ) volume := by
    have hmeas : AEStronglyMeasurable (fun a : Work.LWP.R3 =>
        crossL (ω a - ω x) (kf (x + h - a) - kf (x - a))) volume := by
      have h2 := aestronglyMeasurable_crossL_kf hu (x + h)
      have h3 := aestronglyMeasurable_crossL_kf hu x
      have h4 := h2.sub h3
      have hfun : ((fun a : Work.LWP.R3 => crossL (ω a - ω x) (kf (x + h - a)))
            - (fun a : Work.LWP.R3 => crossL (ω a - ω x) (kf (x - a))))
          = (fun a : Work.LWP.R3 => crossL (ω a - ω x) (kf (x + h - a) - kf (x - a))) := by
        funext a
        simp only [Pi.sub_apply, map_sub]
      simpa only [hfun] using h4
    have hG : IntegrableOn (fun a : Work.LWP.R3 => (C * (ρ + ‖x‖) ^ c) *
        (‖x + h - a‖ ^ (-2:ℝ) + ‖x - a‖ ^ (-2:ℝ))) (Metric.ball (0 : Work.LWP.R3) ρ) volume :=
      MeasureTheory.Integrable.const_mul
        ((integrableOn_norm_sub_rpow_ball_origin (x + h) (-2) (by norm_num) ρ).add
          (integrableOn_norm_sub_rpow_ball_origin x (-2) (by norm_num) ρ)) _
    refine integrableOn_of_norm_le_ball hG hmeas (fun a ha => ?_)
    have h1 : ‖kf (x + h - a) - kf (x - a)‖
        ≤ ‖x + h - a‖ ^ (-2:ℝ) + ‖x - a‖ ^ (-2:ℝ) := by
      calc ‖kf (x + h - a) - kf (x - a)‖ ≤ ‖kf (x + h - a)‖ + ‖kf (x - a)‖ := norm_sub_le _ _
        _ = ‖x + h - a‖ ^ (-2:ℝ) + ‖x - a‖ ^ (-2:ℝ) := by rw [norm_kf_eq, norm_kf_eq]
    calc ‖crossL (ω a - ω x) (kf (x + h - a) - kf (x - a))‖
        ≤ ‖crossL (ω a - ω x)‖ * ‖kf (x + h - a) - kf (x - a)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖ω a - ω x‖ * ‖kf (x + h - a) - kf (x - a)‖ := by
          gcongr
          exact Work.StabilityFar.Decay.norm_crossL_le _
      _ ≤ (C * (ρ + ‖x‖) ^ c) * (‖x + h - a‖ ^ (-2:ℝ) + ‖x - a‖ ^ (-2:ℝ)) :=
          mul_le_mul (hwbound a ha) h1 (norm_nonneg _)
            (mul_nonneg hC (Real.rpow_nonneg hDnn c))
  have hf3int : IntegrableOn (fun a : Work.LWP.R3 =>
      crossL (ω x) (kf (x + h - a) - kf (x - a))) (Metric.ball (0 : Work.LWP.R3) ρ) volume := by
    have hmeas : AEStronglyMeasurable (fun a : Work.LWP.R3 =>
        crossL (ω x) (kf (x + h - a) - kf (x - a))) volume := by
      have h2 := aestronglyMeasurable_crossL_kf (u := fun _ : Work.LWP.R3 => ω x)
        aestronglyMeasurable_const (x + h)
      have h3 := aestronglyMeasurable_crossL_kf (u := fun _ : Work.LWP.R3 => ω x)
        aestronglyMeasurable_const x
      have h4 := h2.sub h3
      have hfun : ((fun a : Work.LWP.R3 => crossL (ω x) (kf (x + h - a)))
            - (fun a : Work.LWP.R3 => crossL (ω x) (kf (x - a))))
          = (fun a : Work.LWP.R3 => crossL (ω x) (kf (x + h - a) - kf (x - a))) := by
        funext a
        simp only [Pi.sub_apply, map_sub]
      simpa only [hfun] using h4
    have hG : IntegrableOn (fun a : Work.LWP.R3 => ‖ω x‖ *
        (‖x + h - a‖ ^ (-2:ℝ) + ‖x - a‖ ^ (-2:ℝ))) (Metric.ball (0 : Work.LWP.R3) ρ) volume :=
      MeasureTheory.Integrable.const_mul
        ((integrableOn_norm_sub_rpow_ball_origin (x + h) (-2) (by norm_num) ρ).add
          (integrableOn_norm_sub_rpow_ball_origin x (-2) (by norm_num) ρ)) _
    refine integrableOn_of_norm_le_ball hG hmeas (fun a _ => ?_)
    have h1 : ‖kf (x + h - a) - kf (x - a)‖
        ≤ ‖x + h - a‖ ^ (-2:ℝ) + ‖x - a‖ ^ (-2:ℝ) := by
      calc ‖kf (x + h - a) - kf (x - a)‖ ≤ ‖kf (x + h - a)‖ + ‖kf (x - a)‖ := norm_sub_le _ _
        _ = ‖x + h - a‖ ^ (-2:ℝ) + ‖x - a‖ ^ (-2:ℝ) := by rw [norm_kf_eq, norm_kf_eq]
    calc ‖crossL (ω x) (kf (x + h - a) - kf (x - a))‖
        ≤ ‖crossL (ω x)‖ * ‖kf (x + h - a) - kf (x - a)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖ω x‖ * ‖kf (x + h - a) - kf (x - a)‖ := by
          gcongr
          exact Work.StabilityFar.Decay.norm_crossL_le _
      _ ≤ ‖ω x‖ * (‖x + h - a‖ ^ (-2:ℝ) + ‖x - a‖ ^ (-2:ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  have hf4meas : AEStronglyMeasurable (fun a : Work.LWP.R3 => bsIntegrand ω x a h) volume :=
    (by fun_prop : Continuous fun L : Work.LWP.R3 →L[ℝ] Work.LWP.R3 => L h).comp_aestronglyMeasurable
      (aestronglyMeasurable_bsIntegrand hωc x)
  have hf4int : IntegrableOn (fun a : Work.LWP.R3 => bsIntegrand ω x a h)
      (Metric.ball (0 : Work.LWP.R3) ρ) volume := by
    have hg : IntegrableOn (fun a : Work.LWP.R3 => ‖h‖ * ‖bsIntegrand ω x a‖)
        (Metric.ball (0 : Work.LWP.R3) ρ) volume :=
      MeasureTheory.Integrable.const_mul hbsIint.norm ‖h‖
    refine integrableOn_of_norm_le_ball hg hf4meas (fun a _ => ?_)
    calc ‖bsIntegrand ω x a h‖ ≤ ‖bsIntegrand ω x a‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖h‖ * ‖bsIntegrand ω x a‖ := mul_comm _ _
  have hf5int : IntegrableOn (fun a : Work.LWP.R3 => crossL (ω a - ω x) (resid h (x - a)))
      (Metric.ball (0 : Work.LWP.R3) ρ) volume := by
    have hmeas : AEStronglyMeasurable (fun a : Work.LWP.R3 =>
        crossL (ω a - ω x) (resid h (x - a))) volume := by
      have h1 : AEStronglyMeasurable (fun a : Work.LWP.R3 =>
          crossL (ω a - ω x) (kf (x + h - a))) volume := aestronglyMeasurable_crossL_kf hu (x + h)
      have h2 : AEStronglyMeasurable (fun a : Work.LWP.R3 =>
          crossL (ω a - ω x) (kf (x - a))) volume := aestronglyMeasurable_crossL_kf hu x
      have h4 : AEStronglyMeasurable (fun a : Work.LWP.R3 =>
          crossL (ω a - ω x) (kDerivCLM (x - a) h)) volume := by
        have hfun : (fun a : Work.LWP.R3 => crossL (ω a - ω x) (kDerivCLM (x - a) h))
            = fun a : Work.LWP.R3 => bsIntegrand ω x a h := by
          funext a
          rw [bsIntegrand_apply]
        rw [hfun]
        exact hf4meas
      have h5 := (h1.sub h2).sub h4
      have hfun : (((fun a : Work.LWP.R3 => crossL (ω a - ω x) (kf (x + h - a)))
            - (fun a : Work.LWP.R3 => crossL (ω a - ω x) (kf (x - a))))
            - (fun a : Work.LWP.R3 => crossL (ω a - ω x) (kDerivCLM (x - a) h)))
          = (fun a : Work.LWP.R3 => crossL (ω a - ω x) (resid h (x - a))) := by
        funext a
        simp only [Pi.sub_apply, ← resid_shift x h a, map_sub]
      simpa only [hfun] using h5
    have hG : IntegrableOn (fun a : Work.LWP.R3 => (C * (ρ + ‖x‖) ^ c) *
        (‖x + h - a‖ ^ (-2:ℝ) + ‖x - a‖ ^ (-2:ℝ)) + (4 * C * ‖h‖) * ‖x - a‖ ^ (c - 3))
        (Metric.ball (0 : Work.LWP.R3) ρ) volume :=
      (MeasureTheory.Integrable.const_mul
        ((integrableOn_norm_sub_rpow_ball_origin (x + h) (-2) (by norm_num) ρ).add
          (integrableOn_norm_sub_rpow_ball_origin x (-2) (by norm_num) ρ))
        (C * (ρ + ‖x‖) ^ c)).add
        (MeasureTheory.Integrable.const_mul
          (integrableOn_norm_sub_rpow_ball_origin x (c - 3) (by linarith) ρ) (4 * C * ‖h‖))
    refine integrableOn_of_norm_le_ball hG hmeas (fun a ha => ?_)
    have h1 : ‖resid h (x - a)‖
        ≤ (‖x + h - a‖ ^ (-2:ℝ) + ‖x - a‖ ^ (-2:ℝ)) + 4 * ‖x - a‖ ^ (-3:ℝ) * ‖h‖ := by
      have hcr := norm_resid_le_crude h (x - a)
      have heq : (x - a) + h = x + h - a := by abel
      rw [heq] at hcr
      linarith
    have hCD : 0 ≤ C * (ρ + ‖x‖) ^ c := mul_nonneg hC (Real.rpow_nonneg hDnn c)
    calc ‖crossL (ω a - ω x) (resid h (x - a))‖
        ≤ ‖crossL (ω a - ω x)‖ * ‖resid h (x - a)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖ω a - ω x‖ * ‖resid h (x - a)‖ := by
          gcongr
          exact Work.StabilityFar.Decay.norm_crossL_le _
      _ ≤ ‖ω a - ω x‖ * ((‖x + h - a‖ ^ (-2:ℝ) + ‖x - a‖ ^ (-2:ℝ))
            + 4 * ‖x - a‖ ^ (-3:ℝ) * ‖h‖) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = ‖ω a - ω x‖ * (‖x + h - a‖ ^ (-2:ℝ) + ‖x - a‖ ^ (-2:ℝ))
            + ‖ω a - ω x‖ * (4 * ‖x - a‖ ^ (-3:ℝ) * ‖h‖) := by ring
      _ ≤ (C * (ρ + ‖x‖) ^ c) * (‖x + h - a‖ ^ (-2:ℝ) + ‖x - a‖ ^ (-2:ℝ))
            + (4 * C * ‖h‖) * ‖x - a‖ ^ (c - 3) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul (hwbound a ha) (le_refl _) (by positivity) hCD
          · have hb : ‖a - x‖ = ‖x - a‖ := norm_sub_rev a x
            calc ‖ω a - ω x‖ * (4 * ‖x - a‖ ^ (-3:ℝ) * ‖h‖)
                ≤ (C * ‖a - x‖ ^ c) * (4 * ‖x - a‖ ^ (-3:ℝ) * ‖h‖) :=
                  mul_le_mul_of_nonneg_right (hhold a x) (by positivity)
              _ = 4 * C * ‖h‖ * ((‖x - a‖ : ℝ) ^ c * (‖x - a‖ : ℝ) ^ (-3:ℝ)) := by
                  rw [hb]; ring
              _ = (4 * C * ‖h‖) * ‖x - a‖ ^ (c - 3) := by
                  rw [rpow_mul_rpow_neg_three (x - a) hc.ne' (by linarith : c ≠ 3)]
  -- the residual identity
  have hmain : bsField ω ρ (x + h) - bsField ω ρ x - bsDerivCLM ω ρ x h
      = ∫ a in Metric.ball (0 : Work.LWP.R3) ρ, crossL (ω a - ω x) (resid h (x - a)) := by
    rw [bsField_sub hM hbdd hs hm ρ x h]
    have hA : (∫ a in Metric.ball (0 : Work.LWP.R3) ρ, crossL (ω a) (kf (x + h - a) - kf (x - a)))
        = (∫ a in Metric.ball (0 : Work.LWP.R3) ρ,
              crossL (ω a - ω x) (kf (x + h - a) - kf (x - a)))
          + ∫ a in Metric.ball (0 : Work.LWP.R3) ρ,
              crossL (ω x) (kf (x + h - a) - kf (x - a)) := by
      rw [← MeasureTheory.integral_add hf2int hf3int]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with a
      exact crossL_omega_split (ω a) (ω x) _
    have hB : (∫ a in Metric.ball (0 : Work.LWP.R3) ρ,
          crossL (ω a - ω x) (kf (x + h - a) - kf (x - a)))
        = (∫ a in Metric.ball (0 : Work.LWP.R3) ρ, bsIntegrand ω x a h)
          + ∫ a in Metric.ball (0 : Work.LWP.R3) ρ,
              crossL (ω a - ω x) (resid h (x - a)) := by
      rw [← MeasureTheory.integral_add hf4int hf5int]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with a
      rw [bsIntegrand_apply, ← map_add, ← resid_shift x h a]
      congr 1
      abel
    have hI3 : (∫ a in Metric.ball (0 : Work.LWP.R3) ρ,
          crossL (ω x) (kf (x + h - a) - kf (x - a)))
        = (4 * Real.pi / 3) • crossL (ω x) h := by
      rw [ContinuousLinearMap.integral_comp_comm (crossL (ω x)) hΔint,
        integral_kf_diff_ball hxρ hxhρ, ContinuousLinearMap.map_smul]
    have hC1 : bsDerivCLM ω ρ x h
        = (∫ a in Metric.ball (0 : Work.LWP.R3) ρ, bsIntegrand ω x a h)
          + (4 * Real.pi / 3) • crossL (ω x) h := by
      have happ : (∫ a in Metric.ball (0 : Work.LWP.R3) ρ, bsIntegrand ω x a) h
          = ∫ a in Metric.ball (0 : Work.LWP.R3) ρ, bsIntegrand ω x a h :=
        ContinuousLinearMap.integral_apply hbsIint h
      rw [Work.CoreResiduals.BiotSavart.bsDerivCLM.eq_def, add_apply, smul_apply,
        show (∫ a in Metric.ball (0 : Work.LWP.R3) ρ,
              (crossL (ω a - ω x)).comp (kDerivCLM (x - a))) h
            = (∫ a in Metric.ball (0 : Work.LWP.R3) ρ, bsIntegrand ω x a) h from rfl,
        happ]
    rw [hA, hB, hI3, hC1]
    abel
  rw [hmain]
  calc ‖∫ a in Metric.ball (0 : Work.LWP.R3) ρ, crossL (ω a - ω x) (resid h (x - a))‖
      ≤ ∫ a in Metric.ball (0 : Work.LWP.R3) ρ, ‖crossL (ω a - ω x) (resid h (x - a))‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ a in Metric.ball (0 : Work.LWP.R3) ρ,
          ‖crossL (ω a - ω x) (kf (x + h - a) - kf (x - a) - kDerivCLM (x - a) h)‖ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with a
        rw [resid_shift x h a]
    _ ≤ K * ‖h‖ ^ (1 + c) := hK ρ x h hh


end Work.CoreResiduals.BiotSavart
