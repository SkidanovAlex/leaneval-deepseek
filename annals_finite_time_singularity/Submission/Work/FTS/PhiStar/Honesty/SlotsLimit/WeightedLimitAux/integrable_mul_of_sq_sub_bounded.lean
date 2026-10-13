import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.L1Space.Integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.SlotsLimit.WeightedLimitAux

open scoped MeasureTheory ENNReal Topology
open MeasureTheory Filter

/-- **Key pointwise inequality.** For nonnegative reals `a b`, `a * b ≤ a ^ 2 + b ^ 2`
(because `a ^ 2 + b ^ 2 - a * b = ((a - b) ^ 2 + a ^ 2 + b ^ 2) / 2 ≥ 0`).  Here stated for
the extended norms of real numbers. -/
private lemma enorm_mul_le_sq_add_sq (a b : ℝ) : ‖a * b‖ₑ ≤ ‖a‖ₑ ^ 2 + ‖b‖ₑ ^ 2 := by
  rw [enorm_mul, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
    ← ENNReal.ofReal_mul (abs_nonneg a), ← ENNReal.ofReal_pow (abs_nonneg a),
    ← ENNReal.ofReal_pow (abs_nonneg b), ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (by
    nlinarith [sq_nonneg (|a| - |b|), sq_nonneg (|a| + |b|)])

/-- If `h` vanishes off a finite-measure set `s` and is bounded by `M`, and `(F - G) ^ 2` is
integrable, then `(F - G) * h` is integrable: pointwise, `‖(F-G)h‖ ≤ ‖F-G‖^2 + ‖h‖^2`, and
both summands have finite integral (`s` has finite measure and `‖h‖ ≤ M` on it). -/
private theorem hasFiniteIntegral_sub_mul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F G h : α → ℝ} {s : Set α} {M : ℝ}
    (hs : MeasurableSet s) (hμs : μ s < ∞)
    (hsup : ∀ x, h x ≠ 0 → x ∈ s)
    (hbd : ∀ x, |h x| ≤ M)
    (hsub : Integrable (fun x => (F x - G x) ^ 2) μ) :
    HasFiniteIntegral (fun x => (F x - G x) * h x) μ := by
  have hM2 : ENNReal.ofReal M ^ 2 < ∞ := by
    rw [pow_two]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  -- `(F - G) ^ 2` contributes a finite `L²` norm, and is a.e. strongly measurable.
  have hAEM : AEMeasurable (fun x => ‖F x - G x‖ₑ ^ 2) μ := by
    simpa only [enorm_pow] using hsub.1.enorm
  have hP : (∫⁻ x, ‖F x - G x‖ₑ ^ 2 ∂μ) < ∞ := by
    have h := hsub.2
    rw [hasFiniteIntegral_def] at h
    simpa only [enorm_pow] using h
  -- `h` is bounded by `M` and supported on the finite-measure set `s`.
  have hQ : (∫⁻ x, ‖h x‖ₑ ^ 2 ∂μ) < ∞ := by
    have hle : ∀ x, ‖h x‖ₑ ^ 2 ≤ s.indicator (fun _ => ENNReal.ofReal M ^ 2) x := by
      intro x
      by_cases hx : x ∈ s
      · rw [Set.indicator_of_mem hx]
        have h1 : ‖h x‖ₑ ≤ ENNReal.ofReal M := by
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (hbd x)
        exact ENNReal.pow_le_pow_left h1
      · rw [Set.indicator_of_notMem hx]
        have hx0 : h x = 0 := by
          by_contra hc
          exact hx (hsup x hc)
        simp [hx0]
    calc ∫⁻ x, ‖h x‖ₑ ^ 2 ∂μ
        ≤ ∫⁻ x, s.indicator (fun _ => ENNReal.ofReal M ^ 2) x ∂μ := lintegral_mono hle
      _ = ENNReal.ofReal M ^ 2 * μ s := lintegral_indicator_const hs _
      _ < ∞ := ENNReal.mul_lt_top hM2 hμs
  -- The product has finite integral.
  calc ∫⁻ x, ‖(F x - G x) * h x‖ₑ ∂μ
      ≤ ∫⁻ x, (‖F x - G x‖ₑ ^ 2 + ‖h x‖ₑ ^ 2) ∂μ :=
        lintegral_mono fun x => enorm_mul_le_sq_add_sq (F x - G x) (h x)
    _ = (∫⁻ x, ‖F x - G x‖ₑ ^ 2 ∂μ) + ∫⁻ x, ‖h x‖ₑ ^ 2 ∂μ := lintegral_add_left' hAEM _
    _ < ∞ := ENNReal.add_lt_top.2 ⟨hP, hQ⟩

theorem integrable_mul_of_sq_sub_bounded {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F G h : α → ℝ} {s : Set α} {M : ℝ}
    (hs : MeasurableSet s) (hμs : μ s < ∞)
    (hsup : ∀ x, h x ≠ 0 → x ∈ s)
    (hM : 0 ≤ M) (hbd : ∀ x, |h x| ≤ M)
    (hsub : Integrable (fun x => (F x - G x) ^ 2) μ)
    (hG : Integrable (fun x => G x * h x) μ)
    (hFm : AEMeasurable F μ) (hhm : AEMeasurable h μ) :
    Integrable (fun x => F x * h x) μ := by
  refine ⟨hFm.aestronglyMeasurable.mul hhm.aestronglyMeasurable, ?_⟩
  -- `F * h = G * h + (F - G) * h`, and both summands have finite integral.
  have hR : HasFiniteIntegral (fun x => (F x - G x) * h x) μ :=
    hasFiniteIntegral_sub_mul hs hμs hsup hbd hsub
  refine HasFiniteIntegral.mono'_enorm (f := fun x => F x * h x)
    (g := fun x => ‖G x * h x‖ₑ + ‖(F x - G x) * h x‖ₑ) ?_ ?_
  · show (∫⁻ x, ‖G x * h x‖ₑ + ‖(F x - G x) * h x‖ₑ ∂μ) < ∞
    rw [lintegral_add_left' hG.1.enorm]
    exact ENNReal.add_lt_top.2 ⟨hG.2, hR⟩
  · filter_upwards with x
    rw [show F x * h x = G x * h x + (F x - G x) * h x by ring]
    exact enorm_add_le _ _

end Work.FTS.PhiStar.Honesty.SlotsLimit.WeightedLimitAux
