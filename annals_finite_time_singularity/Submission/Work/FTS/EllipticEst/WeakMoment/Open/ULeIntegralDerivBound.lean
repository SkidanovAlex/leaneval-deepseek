import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.TT.SliceCoercDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `|u θ| ≤ (π/2) · A` from `u 0 = 0` and `|u'| ≤ A`

Elementary integral form of the mean value inequality on the angular interval:

if `u` is `C^∞` on the open interval `(0, π/2)`, continuous on `Iθ = [0, π/2]`, vanishes at
`θ = 0`, and `|u'| ≤ A` on `(0, π/2)`, then `|u θ| ≤ (π/2) · A` for every `θ ∈ (0, π/2)`.

Proof: Newton–Leibniz on `[0, θ]` (`∫_0^θ u' = u θ - u 0 = u θ`, the derivative being
integrable there because it is continuous on `(0, θ]` and bounded by `A`), followed by the
standard bound `|∫_0^θ u'| ≤ A · θ ≤ A · (π/2)`.
-/

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.WeakMoment.Open

theorem ULeIntegralDerivBound {u : ℝ → ℝ} {A : ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hcont : ContinuousOn u Work.Spaces.Iθ) (h0 : u 0 = 0) (hA0 : 0 ≤ A)
    (hA : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv u θ| ≤ A) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |u θ| ≤ (Real.pi / 2) * A := by
  intro θ hθ
  have hθ0 : (0 : ℝ) < θ := hθ.1
  have hθπ : θ < Real.pi / 2 := hθ.2
  -- `u` is continuous on the closed interval `[0, π/2]`.
  have hcont' : ContinuousOn u (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
    simpa only [Work.Spaces.Iθ] using hcont
  have hcontIcc : ContinuousOn u (Set.Icc 0 θ) :=
    hcont'.mono (fun x hx => ⟨hx.1, le_of_lt (lt_of_le_of_lt hx.2 hθπ)⟩)
  -- `u` is differentiable on `(0, θ)` with derivative `deriv u`.
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) θ, HasDerivAt u (deriv u x) x := by
    intro x hx
    have hxπ : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hx.1, lt_trans hx.2 hθπ⟩
    have hnhds : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 x := isOpen_Ioo.mem_nhds hxπ
    have hd : DifferentiableAt ℝ u x :=
      ((hsm 1).differentiableOn (by norm_num) x hxπ).differentiableAt hnhds
    exact hd.hasDerivAt
  -- `deriv u` is continuous on `(0, θ]` (it is `C¹` on `(0, π/2)`).
  have hderivCont : ContinuousOn (deriv u) (Set.Ioc 0 θ) := by
    have hcd : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (hsm 2).deriv_of_isOpen isOpen_Ioo (by norm_num)
    exact hcd.continuousOn.mono (fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hθπ⟩)
  -- hence it is integrable there (bounded by `A`, and the interval has finite measure).
  have hIntOn : IntegrableOn (deriv u) (Set.Ioc (0 : ℝ) θ) := by
    refine IntegrableOn.of_bound ?_
      (hderivCont.aestronglyMeasurable (μ := volume) measurableSet_Ioc) A ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    · rw [ae_restrict_iff' measurableSet_Ioc]
      refine Eventually.of_forall (fun x hx => ?_)
      have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hx.1, lt_of_le_of_lt hx.2 hθπ⟩
      simpa [Real.norm_eq_abs] using hA x hx'
  have hint : IntervalIntegrable (deriv u) volume (0 : ℝ) θ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hθ0.le).mpr hIntOn
  -- Newton–Leibniz on `[0, θ]`.
  have hFTC : ∫ x in (0 : ℝ)..θ, deriv u x = u θ - u 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hθ0.le hcontIcc hderiv hint
  -- the triangle inequality for the integral, with the pointwise bound `|u'| ≤ A`.
  have hnorm : ‖u θ‖ ≤ A * θ := by
    have hb : ∀ x ∈ Set.uIoc (0 : ℝ) θ, ‖deriv u x‖ ≤ A := by
      intro x hx
      rw [uIoc_of_le hθ0.le] at hx
      have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hx.1, lt_of_le_of_lt hx.2 hθπ⟩
      simpa [Real.norm_eq_abs] using hA x hx'
    have h1 : ‖∫ x in (0 : ℝ)..θ, deriv u x‖ ≤ A * |θ - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [hFTC, h0, sub_zero] at h1
    rwa [sub_zero, abs_of_pos hθ0] at h1
  have h2 : |u θ| ≤ A * θ := by
    rw [← Real.norm_eq_abs]; exact hnorm
  have h3 : A * θ ≤ (Real.pi / 2) * A := by
    have := mul_le_mul_of_nonneg_left (le_of_lt hθπ) hA0
    linarith
  linarith

end Work.FTS.EllipticEst.WeakMoment.Open
