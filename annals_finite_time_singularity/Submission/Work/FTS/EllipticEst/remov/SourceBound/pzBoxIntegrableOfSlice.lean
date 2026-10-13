import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.remov.SourceBound.pzSliceFtcBound
import Submission.Work.FTS.EllipticEst.remov.SourceBound.aesmPzMulSinCos2Box

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SourceBound

open scoped Real Topology Interval
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Box integrability of `θ ↦ pz Ψ z θ * sinCos2 θ` from one honest slice.**

Let `Ψ : ℝ → ℝ → ℝ` be smooth on the open quadrant, `0 < a ≤ b`, `z₀ ∈ [a, b]`.  Assume that the
`z`-derivative slices of the second `z`-derivative are product-integrable,
`(z, θ) ↦ pzIter 2 Ψ z θ * sinCos2 θ ∈ L¹((a,b] × Iθ)`, and that the single slice
`θ ↦ pz Ψ z₀ θ * sinCos2 θ` is integrable on `Iθ`.  Then
`(z, θ) ↦ pz Ψ z θ * sinCos2 θ ∈ L¹((a,b] × Iθ)`.

Proof sketch.  For `z > 0` and `θ ∈ (0, π/2)`, the FTC along the `z`-variable gives
`pz Ψ z θ = pz Ψ z₀ θ + ∫ s in z₀..z, pzIter 2 Ψ s θ`, so
`‖pz Ψ z θ * sinCos2 θ‖ ≤ ‖pz Ψ z₀ θ * sinCos2 θ‖
 + (∫ s in a..b, ‖pzIter 2 Ψ s θ * sinCos2 θ‖)`; the first summand is integrable on the box
because `z ↦ ‖pz Ψ z₀ θ‖` is bounded by a constant on `[a,b]` and the slice at `z₀` is integrable,
the second by Tonelli from the box integrability hypothesis.  A.e. measurability comes from the
smoothness of `Ψ` on the open quadrant. -/
theorem pzBoxIntegrableOfSlice {Ψ : ℝ → ℝ → ℝ} {a b z₀ : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hz₀ : z₀ ∈ Set.Icc a b)
    (hsmooth : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hbox2 : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hsl : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ) :
    MeasureTheory.Integrable
      (Function.uncurry (fun z θ => Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- `Ψ` is smooth on the open quadrant in the packaged form used by the slice lemmas.
  have hSO : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsmooth
  -- The `z`-measure of the box is finite (it is the restricted Lebesgue measure of `(a,b]`).
  haveI : IsFiniteMeasure (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Ioc]
        exact ENNReal.ofReal_lt_top⟩
  -- The dominating function, depending on `θ` alone: the honest slice at `z₀` plus the
  -- `θ`-slice of the `L¹`-bound of Tonelli applied to `∂_z²Ψ · sinCos2`.
  let D : ℝ → ℝ := fun θ => ‖Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ‖ +
    ∫ z, ‖Function.uncurry (fun z θ => Work.Spaces.pzIter 2 Ψ z θ
      * Work.Elliptic.sinCos2 θ) (z, θ)‖
      ∂(MeasureTheory.volume.restrict (Set.Ioc a b))
  have hDint : MeasureTheory.Integrable D (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h1 : MeasureTheory.Integrable
        (fun θ => ‖Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ‖)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      have h := hsl
      rw [MeasureTheory.IntegrableOn] at h
      exact h.norm
    have h2 : MeasureTheory.Integrable
        (fun θ => ∫ z, ‖Function.uncurry (fun z θ => Work.Spaces.pzIter 2 Ψ z θ
            * Work.Elliptic.sinCos2 θ) (z, θ)‖
          ∂(MeasureTheory.volume.restrict (Set.Ioc a b)))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      hbox2.norm.integral_prod_right
    exact h1.add h2
  have hDnonneg : ∀ θ, 0 ≤ D θ := by
    intro θ
    exact add_nonneg (norm_nonneg _) (MeasureTheory.integral_nonneg (fun _ => norm_nonneg _))
  -- Pointwise domination at every point of the box, from the `z`-FTC bound at interior angles
  -- and `sinCos2 θ = 0` at the two endpoints of `Iθ`.
  have hbound : ∀ z θ, z ∈ Set.Ioc a b → θ ∈ Work.Spaces.Iθ →
      ‖Function.uncurry (fun z θ => Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) (z, θ)‖
        ≤ D θ := by
    intro z θ hz hθ
    rcases eq_or_lt_of_le hθ.1 with h0 | hpos
    · have hsin : Work.Elliptic.sinCos2 θ = 0 := by
        rw [← h0, Work.Elliptic.sinCos2]
        simp
      rw [show Function.uncurry
            (fun z θ => Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) (z, θ)
          = Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ from rfl, hsin, mul_zero,
        norm_zero]
      exact hDnonneg θ
    · rcases eq_or_lt_of_le hθ.2 with h1 | hlt
      · have hsin : Work.Elliptic.sinCos2 θ = 0 := by
          rw [h1, Work.Elliptic.sinCos2]
          simp [Real.cos_pi_div_two]
        rw [show Function.uncurry
              (fun z θ => Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) (z, θ)
            = Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ from rfl, hsin, mul_zero,
          norm_zero]
        exact hDnonneg θ
      · have hθint : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hpos, hlt⟩
        have hftc := pzSliceFtcBound ha hab hz₀ hSO hz hθint
        -- Turn the interval integral into the `z`-integral against the restricted measure.
        have hconv : (∫ s in a..b, ‖Work.Spaces.pzIter 2 Ψ s θ * Work.Elliptic.sinCos2 θ‖) =
            ∫ z, ‖Function.uncurry (fun z θ => Work.Spaces.pzIter 2 Ψ z θ
                * Work.Elliptic.sinCos2 θ) (z, θ)‖
              ∂(MeasureTheory.volume.restrict (Set.Ioc a b)) := by
          rw [intervalIntegral.integral_of_le hab]
          rfl
        calc ‖Function.uncurry (fun z θ => Work.Spaces.pz Ψ z θ
                * Work.Elliptic.sinCos2 θ) (z, θ)‖
            = ‖Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ‖ := rfl
          _ ≤ ‖Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ‖ +
                ∫ s in a..b, ‖Work.Spaces.pzIter 2 Ψ s θ * Work.Elliptic.sinCos2 θ‖ := hftc
          _ = D θ := by
              rw [hconv]
  -- Integrability of the dominator on the product box, and the `L¹` criterion.
  have hdom : MeasureTheory.Integrable (fun p : ℝ × ℝ => D p.2)
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    hDint.comp_snd _
  have hAE : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun z θ => Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    aesmPzMulSinCos2Box hSO ha
  refine MeasureTheory.Integrable.mono' hdom hAE ?_
  -- The box is a null-set modification of the open quadrant, so almost every point of the
  -- product measure lies in `(a,b] × Iθ`, where the pointwise bound holds.
  have hEq : ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))
      = (volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
          (Set.Ioc a b ×ˢ Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.prod_restrict]
    rfl
  rw [hEq]
  filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Icc)]
    with p hp
  exact hbound p.1 p.2 hp.1 hp.2

end Work.FTS.EllipticEst.remov.SourceBound
