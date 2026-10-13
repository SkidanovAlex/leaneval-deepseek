import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.FTS.EllSol.slice_zero_slot_finite
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.FlatFT

/-- **A bounded slice against a nonnegative weight.**

If `u` is a.e. strongly measurable for the restriction of Lebesgue measure to `Iθ`, if the
weight `σ` is integrable and nonnegative on `Iθ`, and if `u θ ^ 2 ≤ B` for every interior angle
`θ ∈ (0, π/2)`, then `u θ ^ 2 * σ θ` is integrable on `Iθ` and its integral is at most
`B ∫_{Iθ} σ`.

The point is that the hypothesis on `u` is only assumed on the *open* interval, whereas the
integral runs over the closed `Iθ`; the two differ by the null set `{0, π/2}`, which is handled
by `ae_restrict_Icc_of_forall_Ioo`.  The bound `‖u θ ^ 2 * σ θ‖ ≤ B * σ θ` then follows from
`u θ ^ 2 ≥ 0` and `σ θ ≥ 0`. -/
private lemma slice_integral_le_of_pointwise {u σ : ℝ → ℝ} {B : ℝ}
    (hu : MeasureTheory.AEStronglyMeasurable u (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hσ : MeasureTheory.IntegrableOn σ Work.Spaces.Iθ)
    (hσnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ σ θ)
    (hpt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), u θ ^ 2 ≤ B) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => u θ ^ 2 * σ θ) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, u θ ^ 2 * σ θ) ≤ B * (∫ θ in Work.Spaces.Iθ, σ θ) := by
  -- interior angles belong to the closed interval
  have hmem : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), θ ∈ Work.Spaces.Iθ :=
    fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  -- the pointwise domination, a.e. on `Iθ`
  have hbound : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖u θ ^ 2 * σ θ‖ ≤ B * σ θ := by
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
    have hσn : 0 ≤ σ θ := hσnn θ (hmem θ hθ)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hσn)]
    exact mul_le_mul_of_nonneg_right (hpt θ hθ) hσn
  -- hence integrability, against the integrable majorant `B * σ`
  have hInt : MeasureTheory.IntegrableOn (fun θ : ℝ => u θ ^ 2 * σ θ) Work.Spaces.Iθ :=
    (hσ.const_mul B).mono' ((hu.pow 2).mul hσ.aestronglyMeasurable) hbound
  refine ⟨hInt, ?_⟩
  have hle : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      u θ ^ 2 * σ θ ≤ B * σ θ := by
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
    exact mul_le_mul_of_nonneg_right (hpt θ hθ) (hσnn θ (hmem θ hθ))
  calc (∫ θ in Work.Spaces.Iθ, u θ ^ 2 * σ θ)
      ≤ ∫ θ in Work.Spaces.Iθ, B * σ θ :=
        MeasureTheory.integral_mono_ae hInt (hσ.const_mul B) hle
    _ = B * (∫ θ in Work.Spaces.Iθ, σ θ) := MeasureTheory.integral_const_mul B σ

/-- **A pointwise bound on a slice bounds the weighted slice integral.**

If `u θ ^ 2 ≤ C` on the interior of the angular interval and `u` is a.e. strongly measurable
there, then the zero-th angular slot `u θ ^ 2 * sin(2θ)^{-η}` is integrable on `Iθ` and its
integral is at most `C` times the integral of the weight `sin(2θ)^{-η}` itself (which is finite
by `Work.Spaces.sin_two_rpow`).

The hypothesis `0 ≤ C` is used at the very end to replace the a priori bound `|C|` by `C`. -/
theorem sliceIntegralPointwise {u : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hu : MeasureTheory.AEStronglyMeasurable u (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hpt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), u θ ^ 2 ≤ C) :
    MeasureTheory.IntegrableOn (fun θ : ℝ =>
        u θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, u θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        ≤ C * (∫ θ in Work.Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  obtain ⟨hInt, hineq⟩ := slice_integral_le_of_pointwise
    (σ := fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) hu
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by norm_num [Work.Spaces.eta])
      (by norm_num [Work.Spaces.eta])).1
    (fun θ hθ => Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc (x := 2 * θ)
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _)
    (fun θ hθ => hpt θ hθ)
  refine ⟨hInt, ?_⟩
  calc (∫ θ in Work.Spaces.Iθ, u θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ |C| * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
        le_trans hineq (le_of_eq (by rw [abs_of_nonneg hC]))
    _ = C * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
        by rw [abs_of_nonneg hC]

end Work.FTS.EllSol.FlatFT
