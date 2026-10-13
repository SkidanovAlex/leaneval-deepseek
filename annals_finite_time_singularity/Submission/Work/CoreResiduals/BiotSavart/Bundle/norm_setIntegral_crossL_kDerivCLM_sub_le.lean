import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.CoreResiduals.BiotSavart.IntegrandDefs
import Submission.Work.CoreResiduals.BiotSavart.Bundle.norm_kDerivCLM_sub_le_of_two_mul_le
import Submission.Work.CoreResiduals.BiotSavart.lintegral_exterior_norm_rpow

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
