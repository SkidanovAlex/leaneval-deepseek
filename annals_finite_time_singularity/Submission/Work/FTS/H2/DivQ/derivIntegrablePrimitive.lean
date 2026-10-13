import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of the derivative and the primitive form, from a `sin(2θ)^{-η}` weight

Let `h : ℝ → ℝ` be `C^∞` on `(0, π/2)`, tending to `0` at `0⁺`, and suppose
`(h')² sin(2·)^{-η}` is integrable on `Iθ = [0, π/2]`.  Then for every
`θ ∈ (0, π/2)` the derivative `h'` and its square are integrable on `(0, θ]`, and
`h θ = ∫_0^θ h'`.

The only point where the weight is used is that

`1 ≤ sin(2x)^{-η}`  for `x ∈ (0, θ]`

(since `0 < sin(2x) ≤ 1` and `η ≥ 0`), which turns the hypothesis into integrability
of `(h')²` on the (fixed, bounded) interval `(0, θ]`; the function `h'` itself is then
dominated by `(h')² + 1` and the constant `1` is integrable on a bounded interval.
The primitive form is `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto`,
with the right-hand endpoint value supplied by continuity at the interior point `θ`
and the left-hand one by the hypothesis on the limit at `0`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.H2.DivQ

theorem derivIntegrablePrimitive {h : ℝ → ℝ} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)))
    (hten : Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hint : MeasureTheory.IntegrableOn
      (fun x : ℝ => (deriv h x) ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun x : ℝ => (deriv h x) ^ 2) (Set.Ioc 0 θ) ∧
    MeasureTheory.IntegrableOn (deriv h) (Set.Ioc 0 θ) ∧
    IntervalIntegrable (deriv h) MeasureTheory.volume 0 θ ∧
    IntervalIntegrable (fun x : ℝ => (deriv h x) ^ 2) MeasureTheory.volume 0 θ ∧
    h θ = ∫ x in (0:ℝ)..θ, deriv h x := by
  have hθ0 : (0:ℝ) < θ := hθ.1
  have hθ2 : θ < Real.pi / 2 := hθ.2
  -- `(0, θ] ⊆ [0, π/2]`, so the hypothesis restricts to `(0, θ]`
  have hsub : Set.Ioc 0 θ ⊆ Work.Spaces.Iθ := by
    intro x hx
    exact ⟨le_of_lt hx.1, le_of_lt (lt_of_le_of_lt hx.2 hθ2)⟩
  -- the key pointwise fact: `1 ≤ sin(2x)^{-η}` on `(0, θ]`, since `sin(2x) ∈ (0, 1]`
  have hone_le_rpow : ∀ x ∈ Set.Ioc 0 θ,
      (1:ℝ) ≤ (Real.sin (2 * x)) ^ (-(Work.Spaces.eta)) := by
    intro x hx
    have hsin_pos : 0 < Real.sin (2 * x) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · linarith [hx.1]
      · linarith [hx.2, hθ2]
    have heta_nn : (0:ℝ) ≤ Work.Spaces.eta := by
      unfold Work.Spaces.eta; norm_num
    have hpow_le : (Real.sin (2 * x)) ^ (Work.Spaces.eta) ≤ 1 :=
      Real.rpow_le_one (le_of_lt hsin_pos) (Real.sin_le_one _) heta_nn
    rw [Real.rpow_neg (le_of_lt hsin_pos)]
    simpa [one_div] using
      one_le_one_div (Real.rpow_pos_of_pos hsin_pos Work.Spaces.eta) hpow_le
  -- integrability of `(h')²` on `(0, θ]`, dominated by the hypothesis
  have hsq : IntegrableOn (fun x : ℝ => (deriv h x) ^ 2) (Set.Ioc 0 θ) := by
    have hg : IntegrableOn
        (fun x : ℝ => (deriv h x) ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta)))
        (Set.Ioc 0 θ) := hint.mono_set hsub
    refine Integrable.mono' hg
      ((measurable_deriv h).pow_const 2).aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hone_le_rpow x hx, sq_nonneg (deriv h x)]
  -- integrability of the constant on the bounded interval `(0, θ]`
  have hone : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Set.Ioc 0 θ) := by
    apply integrableOn_const
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
    · simp
  -- integrability of `h'`, dominated by `(h')² + 1`
  have hd : IntegrableOn (deriv h) (Set.Ioc 0 θ) := by
    have hg : IntegrableOn (fun x : ℝ => (deriv h x) ^ 2 + 1) (Set.Ioc 0 θ) := hsq.add hone
    refine Integrable.mono' hg ((measurable_deriv h).aestronglyMeasurable.restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (deriv h x), sq_abs (deriv h x), sq_nonneg (|deriv h x| - 1)]
  have hII : IntervalIntegrable (deriv h) MeasureTheory.volume 0 θ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt hθ0)).2 hd
  have hIIsq : IntervalIntegrable (fun x : ℝ => (deriv h x) ^ 2) MeasureTheory.volume 0 θ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt hθ0)).2 hsq
  -- the primitive form, via the fundamental theorem of calculus with limits at both ends
  have hdiffOn : DifferentiableOn ℝ h (Set.Ioo 0 (Real.pi / 2)) :=
    hsm.differentiableOn (by simp)
  have hderiv : ∀ x ∈ Set.Ioo 0 θ, HasDerivAt h (deriv h x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hx.1, lt_trans hx.2 hθ.2⟩
    exact (hdiffOn.differentiableAt (isOpen_Ioo.mem_nhds hx')).hasDerivAt
  have hb : Tendsto h (𝓝[<] θ) (𝓝 (h θ)) :=
    (hdiffOn.continuousOn.continuousAt (isOpen_Ioo.mem_nhds hθ)).mono_left nhdsWithin_le_nhds
  have hFTC : ∫ x in (0:ℝ)..θ, deriv h x = h θ - 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hθ0 hderiv hII hten hb
  exact ⟨hsq, hd, hII, hIIsq, by linarith [hFTC]⟩

end Work.FTS.H2.DivQ
