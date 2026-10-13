import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.CoreResiduals.BiotSavart.biotSavart_contDiff_one
import Submission.Work.CoreResiduals.BiotSavart.DerivDefs
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.StabilityFar.Decay.biotSavart_sub
import Submission.Work.CoreResiduals.BiotSavart.norm_bsField_diff_bound
import Submission.Work.CoreResiduals.BiotSavart.TaylorDefs
import Submission.Work.CoreResiduals.BiotSavart.biotSavart_norm_le_of_bounded_supported
import Submission.Work.CoreResiduals.BiotSavart.setIntegral_norm_sub_rpow_le
import Submission.Work.CoreResiduals.BiotSavart.kf_sub_le_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Metric
open scoped Topology
open Work.StabilityFar.Decay (kf kDerivCLM crossL)

/-- **The order-`(-1)` estimates for the Biot–Savart operator, with constants uniform over all bounded supported fields.**

For a field `h` with `‖h‖_∞ ≤ G` supported in `closedBall 0 R` (`R > 0`) and ae-strongly-measurable,
and `0 < α < 1`, there is `K ≥ 0` depending only on `α, R, R'` with

`‖BS h x‖ ≤ K * G` and `‖BS h x - BS h y‖ ≤ K * G * ‖x - y‖^α` for all `x, y` with `‖x‖, ‖y‖ ≤ R'`.

No regularity of `h` beyond boundedness/measurability is needed: the kernel `kf b = ‖b‖⁻³ • b` has
`‖kf b‖ = ‖b‖⁻²`, locally integrable in `ℝ³` (`∫_{B(0,R)}‖x-a‖⁻² ≤ 4π(R+R')` uniformly for `‖x‖ ≤ R'`),
and the difference estimate is the classical `δ log(1/δ) ≤ C(α) δ^α` for `0 < α < 1`
(`‖kf (x-a) - kf (y-a)‖ ≤ min(2‖x-a‖⁻², ‖x-y‖ sup ‖D kf‖)`). -/
theorem biotSavart_holder_le_sup {R R' α : ℝ} (hR : 0 < R) (hα : 0 < α) (hα1 : α < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (h : Work.LWP.R3 → Work.LWP.R3) (G : ℝ), 0 ≤ G →
      (∀ a, ‖h a‖ ≤ G) → (∀ a, h a ≠ 0 → a ∈ Metric.closedBall 0 R) →
      MeasureTheory.AEStronglyMeasurable h MeasureTheory.volume →
      (∀ x : Work.LWP.R3, ‖x‖ ≤ R' → ‖Work.LWP.biotSavart h x‖ ≤ K * G) ∧
      (∀ x y : Work.LWP.R3, ‖x‖ ≤ R' → ‖y‖ ≤ R' →
        ‖Work.LWP.biotSavart h x - Work.LWP.biotSavart h y‖ ≤ K * G * ‖x - y‖ ^ α) := by
  -- the pointwise Hölder bound for the Newtonian kernel `kf` (order `-2`, exponent `-2-α`)
  obtain ⟨Ck, hCk0, hCk⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ p q : Work.LWP.R3,
      ‖kf p - kf q‖ ≤ C * ‖p - q‖ ^ α * (‖p‖ ^ (-2 - α) + ‖q‖ ^ (-2 - α)) :=
    kf_sub_le_rpow hα hα1
  -- the order-`(-1)` sup-norm bound (uniform, explicit constant)
  have hsup_lem : ∀ (ω : Work.LWP.R3 → Work.LWP.R3) (M : ℝ), 0 ≤ M → (∀ a, ‖ω a‖ ≤ M) →
      (∀ a, ω a ≠ 0 → a ∈ Metric.closedBall 0 R) →
      MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume → ∀ x : Work.LWP.R3,
      ‖Work.LWP.biotSavart ω x‖ ≤ M * (‖x‖ + R + 1) :=
    fun ω M hM hb hs hm x => biotSavart_norm_le_of_bounded_supported hR hM hb hs hm x
  -- the sub-critical radial weight integrated over `closedBall 0 R`
  have hrad_lem : ∀ z : Work.LWP.R3,
      ∫ a in Metric.closedBall (0 : Work.LWP.R3) R, ‖z - a‖ ^ (-2 - α)
        ≤ 4 * Real.pi * (‖z‖ + R + 1) ^ (1 - α) / (1 - α) :=
    fun z => setIntegral_norm_sub_rpow_le hR hα1 z
  rcases lt_or_ge R' 0 with hR'neg | hR'nn
  · refine ⟨0, le_refl 0, fun h G hG hbdd hsupp hm => ⟨?_, ?_⟩⟩
    · intro x hx
      have h1 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
      linarith
    · intro x y hx hy
      have h1 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
      linarith
  set ρ : ℝ := R' + R + 1 with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; linarith
  have hαlt : 0 < 1 - α := by linarith
  have hρpow : 0 ≤ ρ ^ (1 - α) := Real.rpow_nonneg hρpos.le _
  have hTnn : 0 ≤ (2 * Ck * ρ ^ (1 - α)) / (1 - α) := by positivity
  set K : ℝ := 2 * ρ + (2 * Ck * ρ ^ (1 - α)) / (1 - α) + 1 with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; linarith
  have hK1 : ρ ≤ K := by rw [hKdef]; linarith
  have hK2 : 2 * ρ ≤ K := by rw [hKdef]; linarith
  have hK3 : 2 * Ck * ρ ^ (1 - α) / (1 - α) ≤ K := by rw [hKdef]; linarith
  refine ⟨K, hKnn, ?_⟩
  intro h G hG hbdd hsupp hm
  constructor
  · -- the sup-norm bound
    intro x hx
    have h1 : ‖Work.LWP.biotSavart h x‖ ≤ G * (‖x‖ + R + 1) :=
      hsup_lem h G hG hbdd hsupp hm x
    have h2 : ‖x‖ + R + 1 ≤ ρ := by rw [hρdef]; linarith
    calc ‖Work.LWP.biotSavart h x‖ ≤ G * (‖x‖ + R + 1) := h1
      _ ≤ G * ρ := by gcongr
      _ ≤ K * G := by
          have h3 : G * ρ = ρ * G := by ring
          rw [h3]
          exact mul_le_mul_of_nonneg_right hK1 hG
  · -- the Hölder bound
    intro x y hx hy
    by_cases hxy : x = y
    · subst hxy
      rw [sub_self, norm_zero, sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero]
    have hδpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    rcases lt_or_ge 1 ‖x - y‖ with hδ1 | hδ1
    · -- far field: both sup bounds and `‖x-y‖^α ≥ 1`
      have h1 : ‖Work.LWP.biotSavart h x‖ ≤ G * (‖x‖ + R + 1) :=
        hsup_lem h G hG hbdd hsupp hm x
      have h2 : ‖Work.LWP.biotSavart h y‖ ≤ G * (‖y‖ + R + 1) :=
        hsup_lem h G hG hbdd hsupp hm y
      have hxρ : ‖x‖ + R + 1 ≤ ρ := by rw [hρdef]; linarith
      have hyρ : ‖y‖ + R + 1 ≤ ρ := by rw [hρdef]; linarith
      have hone : 1 ≤ ‖x - y‖ ^ α := Real.one_le_rpow (le_of_lt hδ1) hα.le
      have hKG : 0 ≤ K * G := mul_nonneg hKnn hG
      calc ‖Work.LWP.biotSavart h x - Work.LWP.biotSavart h y‖
          ≤ ‖Work.LWP.biotSavart h x‖ + ‖Work.LWP.biotSavart h y‖ := norm_sub_le _ _
        _ ≤ G * (‖x‖ + R + 1) + G * (‖y‖ + R + 1) := add_le_add h1 h2
        _ ≤ G * ρ + G * ρ := by
            exact add_le_add (mul_le_mul_of_nonneg_left hxρ hG)
              (mul_le_mul_of_nonneg_left hyρ hG)
        _ = (2 * ρ) * G := by ring
        _ ≤ K * G := mul_le_mul_of_nonneg_right hK2 hG
        _ = K * G * 1 := (mul_one _).symm
        _ ≤ K * G * ‖x - y‖ ^ α := mul_le_mul_of_nonneg_left hone hKG
    · -- near field: integrate the kernel difference
      have hsub : Metric.closedBall (0 : Work.LWP.R3) R ⊆ Metric.ball (0 : Work.LWP.R3) (R + 1) := by
        intro a ha
        rw [Metric.mem_closedBall, dist_zero_right] at ha
        rw [Metric.mem_ball, dist_zero_right]
        linarith
      have hIx : IntegrableOn (fun a : Work.LWP.R3 => ‖x - a‖ ^ (-2 - α))
          (Metric.closedBall (0 : Work.LWP.R3) R) volume :=
        (integrableOn_norm_sub_rpow_ball_origin x (-2 - α) (by linarith) (R + 1)).mono_set hsub
      have hIy : IntegrableOn (fun a : Work.LWP.R3 => ‖y - a‖ ^ (-2 - α))
          (Metric.closedBall (0 : Work.LWP.R3) R) volume :=
        (integrableOn_norm_sub_rpow_ball_origin y (-2 - α) (by linarith) (R + 1)).mono_set hsub
      have hS : MeasurableSet (Metric.closedBall (0 : Work.LWP.R3) R) :=
        Metric.isClosed_closedBall.measurableSet
      have hcle : ∀ z : Work.LWP.R3, ‖z‖ ≤ R' →
          ∫ a in Metric.closedBall (0 : Work.LWP.R3) R, ‖z - a‖ ^ (-2 - α)
            ≤ 4 * Real.pi * ρ ^ (1 - α) / (1 - α) := by
        intro z hz
        refine (hrad_lem z).trans ?_
        have h1 : ‖z‖ + R + 1 ≤ ρ := by rw [hρdef]; linarith
        have h2 : (‖z‖ + R + 1) ^ (1 - α) ≤ ρ ^ (1 - α) :=
          Real.rpow_le_rpow (by positivity) h1 hαlt.le
        calc 4 * Real.pi * (‖z‖ + R + 1) ^ (1 - α) / (1 - α)
            = 4 * Real.pi * ((‖z‖ + R + 1) ^ (1 - α) / (1 - α)) := by ring
          _ ≤ 4 * Real.pi * (ρ ^ (1 - α) / (1 - α)) :=
              mul_le_mul_of_nonneg_left
                (div_le_div_of_nonneg_right h2 hαlt.le)
                (by positivity : (0 : ℝ) ≤ 4 * Real.pi)
          _ = 4 * Real.pi * ρ ^ (1 - α) / (1 - α) := by ring
      have hbk : ∀ a, Work.LWP.BiotSavart.bsK h x a - Work.LWP.BiotSavart.bsK h y a
          = crossL (h a) (kf (x - a) - kf (y - a)) := by
        intro a
        rw [Work.StabilityFar.Decay.bsK_eq_crossL, Work.StabilityFar.Decay.bsK_eq_crossL]
        exact (ContinuousLinearMap.map_sub (crossL (h a)) (kf (x - a)) (kf (y - a))).symm
      have hpt : ∀ a : Work.LWP.R3, ‖crossL (h a) (kf (x - a) - kf (y - a))‖
          ≤ Ck * ‖x - y‖ ^ α * G * (‖x - a‖ ^ (-2 - α) + ‖y - a‖ ^ (-2 - α)) := by
        intro a
        have h1 : ‖crossL (h a) (kf (x - a) - kf (y - a))‖
            ≤ ‖h a‖ * ‖kf (x - a) - kf (y - a)‖ := by
          calc ‖crossL (h a) (kf (x - a) - kf (y - a))‖
              ≤ ‖crossL (h a)‖ * ‖kf (x - a) - kf (y - a)‖ :=
                ContinuousLinearMap.le_opNorm _ _
            _ ≤ ‖h a‖ * ‖kf (x - a) - kf (y - a)‖ :=
                mul_le_mul_of_nonneg_right (Work.StabilityFar.Decay.norm_crossL_le _)
                  (norm_nonneg _)
        have h2 := hCk (x - a) (y - a)
        have h3 : ‖(x - a) - (y - a)‖ = ‖x - y‖ := by
          rw [show (x - a) - (y - a) = x - y by abel]
        rw [h3] at h2
        have h4 : ‖h a‖ * ‖kf (x - a) - kf (y - a)‖
            ≤ G * (Ck * ‖x - y‖ ^ α * (‖x - a‖ ^ (-2 - α) + ‖y - a‖ ^ (-2 - α))) :=
          mul_le_mul (hbdd a) h2 (norm_nonneg _) hG
        calc ‖crossL (h a) (kf (x - a) - kf (y - a))‖
            ≤ ‖h a‖ * ‖kf (x - a) - kf (y - a)‖ := h1
          _ ≤ G * (Ck * ‖x - y‖ ^ α * (‖x - a‖ ^ (-2 - α) + ‖y - a‖ ^ (-2 - α))) := h4
          _ = Ck * ‖x - y‖ ^ α * G * (‖x - a‖ ^ (-2 - α) + ‖y - a‖ ^ (-2 - α)) := by ring
      have hmaj : IntegrableOn (fun a : Work.LWP.R3 =>
          Ck * ‖x - y‖ ^ α * G * (‖x - a‖ ^ (-2 - α) + ‖y - a‖ ^ (-2 - α)))
          (Metric.closedBall (0 : Work.LWP.R3) R) volume :=
        (hIx.add hIy).const_mul (Ck * ‖x - y‖ ^ α * G)
      have hFint : Integrable (Work.LWP.BiotSavart.bsK h x) volume :=
        Work.StabilityFar.Decay.integrable_bsK_supported hG hbdd hsupp hm x
      have hGint : Integrable (Work.LWP.BiotSavart.bsK h y) volume :=
        Work.StabilityFar.Decay.integrable_bsK_supported hG hbdd hsupp hm y
      have hdiff : Work.LWP.biotSavart h x - Work.LWP.biotSavart h y
          = (4 * Real.pi)⁻¹ •
              ∫ a, (Work.LWP.BiotSavart.bsK h x a - Work.LWP.BiotSavart.bsK h y a) := by
        rw [Work.LWP.BiotSavart.biotSavart_apply, Work.LWP.BiotSavart.biotSavart_apply,
          ← smul_sub, ← MeasureTheory.integral_sub hFint hGint]
      have step1 : ‖∫ a, (Work.LWP.BiotSavart.bsK h x a - Work.LWP.BiotSavart.bsK h y a)‖
          ≤ ∫ a in Metric.closedBall (0 : Work.LWP.R3) R,
              ‖crossL (h a) (kf (x - a) - kf (y - a))‖ := by
        have e1 : (∫ a, (Work.LWP.BiotSavart.bsK h x a - Work.LWP.BiotSavart.bsK h y a))
            = ∫ a, crossL (h a) (kf (x - a) - kf (y - a)) :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hbk)
        rw [e1]
        calc ‖∫ a, crossL (h a) (kf (x - a) - kf (y - a))‖
            ≤ ∫ a, ‖crossL (h a) (kf (x - a) - kf (y - a))‖ :=
              MeasureTheory.norm_integral_le_integral_norm _
          _ = ∫ a in Metric.closedBall (0 : Work.LWP.R3) R,
                ‖crossL (h a) (kf (x - a) - kf (y - a))‖ := by
              rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
              intro a ha
              have ha0 : h a = 0 := by
                by_contra hne
                exact ha (hsupp a hne)
              rw [ha0, Work.CoreResiduals.BiotSavart.crossL_zero,
                zero_apply, norm_zero]
      have step2 : (∫ a in Metric.closedBall (0 : Work.LWP.R3) R,
              ‖crossL (h a) (kf (x - a) - kf (y - a))‖)
          ≤ ∫ a in Metric.closedBall (0 : Work.LWP.R3) R,
              Ck * ‖x - y‖ ^ α * G * (‖x - a‖ ^ (-2 - α) + ‖y - a‖ ^ (-2 - α)) := by
        have h := MeasureTheory.norm_integral_le_of_norm_le (μ := volume.restrict
          (Metric.closedBall (0 : Work.LWP.R3) R)) hmaj
          (Filter.Eventually.of_forall (fun a => by
            rw [Real.norm_of_nonneg (norm_nonneg (crossL (h a) (kf (x - a) - kf (y - a))))]
            exact hpt a))
        rwa [Real.norm_of_nonneg (setIntegral_nonneg hS (fun a _ => norm_nonneg _))] at h
      have step3 : (∫ a in Metric.closedBall (0 : Work.LWP.R3) R,
              Ck * ‖x - y‖ ^ α * G * (‖x - a‖ ^ (-2 - α) + ‖y - a‖ ^ (-2 - α)))
          = Ck * ‖x - y‖ ^ α * G *
              ((∫ a in Metric.closedBall (0 : Work.LWP.R3) R, ‖x - a‖ ^ (-2 - α))
                + (∫ a in Metric.closedBall (0 : Work.LWP.R3) R, ‖y - a‖ ^ (-2 - α))) := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hIx hIy]
      have step4 : Ck * ‖x - y‖ ^ α * G *
            ((∫ a in Metric.closedBall (0 : Work.LWP.R3) R, ‖x - a‖ ^ (-2 - α))
              + (∫ a in Metric.closedBall (0 : Work.LWP.R3) R, ‖y - a‖ ^ (-2 - α)))
          ≤ Ck * ‖x - y‖ ^ α * G * (2 * (4 * Real.pi * ρ ^ (1 - α) / (1 - α))) := by
        have h1 := hcle x hx
        have h2 := hcle y hy
        have h3 : (∫ a in Metric.closedBall (0 : Work.LWP.R3) R, ‖x - a‖ ^ (-2 - α))
            + (∫ a in Metric.closedBall (0 : Work.LWP.R3) R, ‖y - a‖ ^ (-2 - α))
            ≤ 2 * (4 * Real.pi * ρ ^ (1 - α) / (1 - α)) := by linarith
        have h4 : 0 ≤ Ck * ‖x - y‖ ^ α * G :=
          mul_nonneg (mul_nonneg hCk0 (Real.rpow_nonneg (norm_nonneg _) _)) hG
        exact mul_le_mul_of_nonneg_left h3 h4
      have hchain : ‖∫ a, (Work.LWP.BiotSavart.bsK h x a - Work.LWP.BiotSavart.bsK h y a)‖
          ≤ Ck * ‖x - y‖ ^ α * G * (2 * (4 * Real.pi * ρ ^ (1 - α) / (1 - α))) :=
        step1.trans (step2.trans (step3.le.trans step4))
      calc ‖Work.LWP.biotSavart h x - Work.LWP.biotSavart h y‖
          = (4 * Real.pi)⁻¹ *
              ‖∫ a, (Work.LWP.BiotSavart.bsK h x a - Work.LWP.BiotSavart.bsK h y a)‖ := by
            rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        _ ≤ (4 * Real.pi)⁻¹ *
              (Ck * ‖x - y‖ ^ α * G * (2 * (4 * Real.pi * ρ ^ (1 - α) / (1 - α)))) :=
            mul_le_mul_of_nonneg_left hchain (by positivity)
        _ = 2 * Ck * G * ‖x - y‖ ^ α * ρ ^ (1 - α) / (1 - α) := by
            field_simp
        _ ≤ K * G * ‖x - y‖ ^ α := by
            have h4 : 0 ≤ G * ‖x - y‖ ^ α :=
              mul_nonneg hG (Real.rpow_nonneg (norm_nonneg _) _)
            calc 2 * Ck * G * ‖x - y‖ ^ α * ρ ^ (1 - α) / (1 - α)
                = (2 * Ck * ρ ^ (1 - α) / (1 - α)) * (G * ‖x - y‖ ^ α) := by ring
              _ ≤ K * (G * ‖x - y‖ ^ α) := mul_le_mul_of_nonneg_right hK3 h4
              _ = K * G * ‖x - y‖ ^ α := by ring

end Work.CoreResiduals.BiotSavart
