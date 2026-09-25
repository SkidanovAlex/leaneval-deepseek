/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The fixed-disc Cauchy potential in a fibre of `ℂⁿ`

This file sets up the operator used to build the `(0,2)`-homotopy for the flat `∂̄`-problem on a
polydisc, the *fixed-disc* Cauchy potential in the `j`-th fibre:

  `fiberPot R j u z = -(1/π) ∫_{‖w‖ < R} u (z with z j replaced by w) / (w - z j) dw`.

Unlike the translation invariant potential `Work.CR.Flat.Cauchy.dbarTransform` (integration over a
disc *centred at* `z`), the domain here is the fixed disc `‖w‖ < R` in the `j`-th coordinate and
the pole is at `z j`; this is what makes the classical identity

  `∂̄_j (fiberPot R j u) = u`   for `‖z j‖ < R`

hold for *arbitrary* (not necessarily supported) data `u`, see
`Work.NN.Core.fiberPot_dbarCoord_self`.

The structural theory proved here is deliberately elementary: integrability of the integrand and
linearity of the potential.  The analytic content (the `∂̄`-identity, the commutation with the other
`∂̄`-operators, and the Schauder estimates) lives in companion modules.
-/
import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy.cauchyTransform_eq_unsub

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Set

namespace Work.NN.Core

/-- Integrability of the shifted Cauchy kernel `w ↦ (w - ζ)⁻¹` on a disc.  The singularity sits at
`ζ`, so this is reduced to the centred statement by the measure preserving reflection
`t ↦ ζ - t` and monotonicity of the integral for positive integrands. -/
lemma integrableOn_sub_inv_ball (R : ℝ) (ζ : ℂ) :
    IntegrableOn (fun w : ℂ => (w - ζ)⁻¹) (Metric.ball 0 R) := by
  have hmp : MeasurePreserving (fun t : ℂ => ζ - t) (volume : Measure ℂ) volume :=
    MeasureTheory.Measure.measurePreserving_sub_left volume ζ
  have hemb : MeasurableEmbedding (fun t : ℂ => ζ - t) :=
    MeasurableEquiv.measurableEmbedding
      ((MeasurableEquiv.neg ℂ).trans (MeasurableEquiv.addLeft ζ))
  have himg : (fun t : ℂ => ζ - t) '' Metric.ball 0 R = Metric.ball ζ R := by
    ext u
    simp only [Metric.mem_ball, Set.mem_image, dist_eq_norm]
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
    · intro hu
      refine ⟨ζ - u, ?_, ?_⟩
      · simpa [norm_sub_rev] using hu
      · ring
  have hcen : IntegrableOn (fun u : ℂ => u⁻¹) (Metric.ball ζ R) := by
    refine (Work.CR.Flat.Cauchy.integrableOn_inv_ball (R + ‖ζ‖)).mono_set ?_
    intro u hu
    rw [Metric.mem_ball, dist_eq_norm] at hu
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖u - 0‖ = ‖u‖ := by rw [sub_zero]
      _ ≤ ‖u - ζ‖ + ‖ζ‖ := by simpa [sub_add_cancel] using norm_add_le (u - ζ) ζ
      _ < R + ‖ζ‖ := by linarith
  have h := (MeasurePreserving.integrableOn_image hmp hemb
    (f := fun u : ℂ => u⁻¹) (s := Metric.ball 0 R)).mp (by rwa [himg])
  have h2 : IntegrableOn (fun t : ℂ => (ζ - t)⁻¹) (Metric.ball 0 R) := h
  have h3 : IntegrableOn (fun t : ℂ => - (ζ - t)⁻¹) (Metric.ball 0 R) := h2.neg
  have h4 : (fun t : ℂ => - (ζ - t)⁻¹) = fun w : ℂ => (w - ζ)⁻¹ := by
    funext w
    rw [show w - ζ = -(ζ - w) from by ring, inv_neg]
  rwa [h4] at h3

/-- Continuity of `w ↦ Function.update z j w`. -/
lemma continuous_update {n : ℕ} (z : Fin n → ℂ) (j : Fin n) :
    Continuous fun w : ℂ => Function.update z j w := by
  rw [continuous_pi_iff]
  intro l
  by_cases hl : l = j
  · rw [hl]
    have hfun : (fun w : ℂ => Function.update z j w j) = fun w : ℂ => w := by
      funext w; rw [Function.update_self]
    rw [hfun]
    exact continuous_id
  · have hfun : (fun w : ℂ => Function.update z j w l) = fun _ : ℂ => z l := by
      funext w; rw [Function.update_of_ne hl]
    rw [hfun]
    exact continuous_const

/-- The integrand of the fixed-disc potential is integrable, for continuous data. -/
lemma integrableOn_fiberIntegrand {n : ℕ} (R : ℝ) (j : Fin n) {u : (Fin n → ℂ) → ℂ}
    (hu : Continuous u) (z : Fin n → ℂ) :
    IntegrableOn (fun w : ℂ => u (Function.update z j w) / (w - z j)) (Metric.ball 0 R) := by
  rcases le_or_gt R 0 with hR | hR
  · rw [Metric.ball_eq_empty.mpr hR]
    exact integrableOn_empty
  have hcont : Continuous fun w : ℂ => u (Function.update z j w) := hu.comp (continuous_update z j)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ((integrableOn_sub_inv_ball R (z j)).norm.const_mul M).mono' ?_ ?_
  · exact ((hcont.measurable.div (measurable_id.sub measurable_const)).aestronglyMeasurable)
  · filter_upwards [self_mem_ae_restrict measurableSet_ball] with w hw
    have hb : ‖u (Function.update z j w)‖ ≤ M := hM _ (Metric.ball_subset_closedBall hw)
    calc ‖u (Function.update z j w) / (w - z j)‖
        = ‖u (Function.update z j w)‖ * ‖(w - z j)⁻¹‖ := by
          rw [norm_div, norm_inv, div_eq_mul_inv]
      _ ≤ M * ‖(w - z j)⁻¹‖ :=
          mul_le_mul_of_nonneg_right hb (by positivity)

/-- **The fixed-disc Cauchy potential in the `j`-th fibre**:
`fiberPot R j u z = -(1/π) ∫_{‖w‖ < R} u (z with z j replaced by w) / (w - z j) dw`. -/
noncomputable def fiberPot {n : ℕ} (R : ℝ) (j : Fin n) (u : (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) : ℂ :=
  -((Real.pi : ℂ))⁻¹ *
    ∫ w in Metric.ball (0 : ℂ) R, u (Function.update z j w) / (w - z j)

@[simp] lemma fiberPot_apply {n : ℕ} (R : ℝ) (j : Fin n) (u : (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) :
    fiberPot R j u z
      = -((Real.pi : ℂ))⁻¹ *
        ∫ w in Metric.ball (0 : ℂ) R, u (Function.update z j w) / (w - z j) := rfl

lemma fiberPot_zero {n : ℕ} (R : ℝ) (j : Fin n) (z : Fin n → ℂ) :
    fiberPot R j 0 z = 0 := by
  simp [fiberPot]

lemma fiberPot_add {n : ℕ} (R : ℝ) (j : Fin n) {u v : (Fin n → ℂ) → ℂ} (hu : Continuous u)
    (hv : Continuous v) (z : Fin n → ℂ) :
    fiberPot R j (fun w => u w + v w) z = fiberPot R j u z + fiberPot R j v z := by
  have h1 : IntegrableOn (fun w : ℂ => u (Function.update z j w) / (w - z j))
      (Metric.ball 0 R) := integrableOn_fiberIntegrand R j hu z
  have h2 : IntegrableOn (fun w : ℂ => v (Function.update z j w) / (w - z j))
      (Metric.ball 0 R) := integrableOn_fiberIntegrand R j hv z
  have h3 : (fun w : ℂ => (fun w => u w + v w) (Function.update z j w) / (w - z j))
      = fun w : ℂ => u (Function.update z j w) / (w - z j)
          + v (Function.update z j w) / (w - z j) := by
    funext w; rw [add_div]
  rw [fiberPot_apply, fiberPot_apply, fiberPot_apply, h3, integral_add h1 h2, mul_add]

lemma fiberPot_neg {n : ℕ} (R : ℝ) (j : Fin n) (u : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    fiberPot R j (fun w => - u w) z = - fiberPot R j u z := by
  have h3 : (fun w : ℂ => (fun w => - u w) (Function.update z j w) / (w - z j))
      = fun w : ℂ => - (u (Function.update z j w) / (w - z j)) := by
    funext w; rw [neg_div]
  rw [fiberPot_apply, fiberPot_apply, h3, integral_neg]
  ring

lemma fiberPot_smul {n : ℕ} (R : ℝ) (j : Fin n) (c : ℂ) (u : (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) :
    fiberPot R j (fun w => c * u w) z = c * fiberPot R j u z := by
  have h3 : (fun w : ℂ => (fun w => c * u w) (Function.update z j w) / (w - z j))
      = fun w : ℂ => c • (u (Function.update z j w) / (w - z j)) := by
    funext w; rw [smul_eq_mul, mul_div_assoc]
  rw [fiberPot_apply, fiberPot_apply, h3, integral_smul]
  simp only [smul_eq_mul]
  ring

end Work.NN.Core
