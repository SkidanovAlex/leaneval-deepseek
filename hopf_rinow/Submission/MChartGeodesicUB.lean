import ChallengeDeps
import Submission.MChartGlobal
import Submission.MChartSpeed
import Submission.ModelSpeed
import Mathlib

/-!
# Manifold length of a chart-geodesic segment is at most its model length (upper bound)

Task: prove the final theorem `chart_geodesic_pathELength_le` below.

## Setting

Challenge hypotheses with `[IsRiemannianManifold I M]`, point `p`, and the global coordinate
metric `ge` from `Submission.chart_metric_global` (ContDiff ℝ 3, symmetric, positive definite,
agreeing with the fibre inner products on `ball (φ p) ρ` with `φ := extChartAt I p`).  Let
`c : ℝ → E` be a **model geodesic** for `ge` with unit metric speed, i.e. there is
`vel : ℝ → E` with `c 0 = φ p`, `vel 0 = v₀`, `(ge (φ p)) v₀ v₀ = 1`,
`HasDerivAt c (vel t) t`, `HasDerivAt vel (accel (ge (c t)) (fderiv ℝ ge (c t)) (vel t)) t` on
`Ioo (-ε) ε`, and the trajectory stays inside `ball (φ p) ρ` for `t ∈ Icc s t0`.  (Such a `c`
exists by the verified model theory applied to `ge`; obtain it from
`Submission.ModelFlow.uniform_exists_geodesic` + `Submission.ModelSpeed.speed_const`.)

Define `γ := (extChartAt I p).symm ∘ c` on the interval (so `γ` is the corresponding curve in
`M`).  **Claim (upper bound):** for `0 ≤ s ≤ t0` (or any `a ≤ b` within the interval),
`pathELength I γ s t0 ≤ 1 * (t0 - s)` when the metric speed is 1 — in general
`pathELength I γ s t0 ≤ s₀ * (t0 - s)` where `s₀ := Real.sqrt ((ge (φ p)) v₀ v₀)` is the
(constant, by `ModelSpeed.speed_const`) model speed of `c`.

Equivalently: `pathELength I γ s t0 ≤ mgLength ge c s t0`, and `mgLength ge c s t0 = s₀*(t0-s)`
(since the model speed is the constant `s₀`).

## Proof route

1. **`mgLength ge c s t0 = s₀*(t0-s)`**: by definition `mgLength ge c a b = ∫ t in a..b,
   sqrt (ge (c t) (deriv c t) (deriv c t))`; by `ModelSpeed.speed_const`,
   `sqrt (ge (c t) (vel t) (vel t)) = s₀` for all `t` in the interval (`s₀ = sqrt (ge (c 0)
   (vel 0) (vel 0))`), and `deriv c t = vel t` (from `HasDerivAt`); so the integral equals
   `s₀*(b-a)`.  (Use the fundamental theorem / `intervalIntegral.integral_const` and the
   fact that the integrand is constant.)
2. **`pathELength I γ s t0 = mgLength ge c s t0`**: by definition
   `pathELength I γ s t0 = ∫⁻ t in Icc s t0, ‖mfderiv% γ t 1‖ₑ` (an ℝ≥0∞-valued integral).  By
   `Submission.MChartSpeed.chart_speed` (unfold its existential to get `ge` with the speed
   identity), for each `t` where `c` is differentiable: `‖mfderiv% γ t 1‖ₑ =
   ENNReal.ofReal (Real.sqrt (ge (c t) (deriv c t) (deriv c t)))` — since `c t` stays in the
   agreement ball (hypothesis).  Hence the integrands are pointwise equal, so the integrals are
   equal (converting the real-valued `mgLength` into the ℝ≥0∞-valued `pathELength` integrand via
   `ENNReal.ofReal`, and identifying the interval integrals on `Icc` — note `pathELength` uses
   `Icc` while `mgLength` uses `a..b`; you may need to rewrite `intervalIntegral` over `Icc` and
   the `Ioo`-restriction lemmas from `PathELength.lean`).
3. Conclude `pathELength I γ s t0 ≤ s₀*(t0-s)`.

If the equality of integrals is painful (because `pathELength` is an ℝ≥0∞-valued lintegral over
`Icc` while `mgLength` is a real interval integral), you may prove instead the weaker statement
you actually need for the interface work: `pathELength I γ s t0 ≤ (ENNReal.ofReal (s₀*(t0-s)))`,
by bounding the integrand pointwise by the constant `s₀` and using
`lintegral_const`/`setLIntegral_const`.  State whichever is true and provable, keeping the name
`chart_geodesic_pathELength_le`.

## Concrete statement (keep the name; adjust details to a provable true form)

    theorem chart_geodesic_pathELength_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E]
        {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
        [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        [IsRiemannianManifold I M] (p : M) :
        ∃ ρ > 0, ∃ ge : E → E →L[ℝ] E →L[ℝ] ℝ,
          ContDiff ℝ 3 ge ∧
          (∀ y ∈ ball (extChartAt I p p) ρ, ∀ u v : E,
             (ge y) u v = (Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)).inner
                           ((extChartAt I p).symm y)
                           ((mfderiv[range I] (extChartAt I p).symm y) u)
                           ((mfderiv[range I] (extChartAt I p).symm y) v)) ∧
          (∀ {c vel : ℝ → E} {a b : ℝ} {s₀ : ℝ},
             (∀ t ∈ Icc a b, c t ∈ ball (extChartAt I p p) ρ) →
             (∀ t ∈ Icc a b, HasDerivAt c (vel t) t) →
             (∀ t ∈ Icc a b, Real.sqrt (ge (c t) (vel t) (vel t)) = s₀) →
             Manifold.pathELength I ((extChartAt I p).symm ∘ c) a b ≤
               ENNReal.ofReal (s₀ * (b - a)))

The proof must be complete (no placeholders).  The statement below is the one to prove.
-/

open scoped Manifold ENNReal ContDiff Bundle
open Set Bundle Metric MeasureTheory

namespace Submission

open LeanEval.Geometry

noncomputable section

/-- The manifold length of a chart-geodesic segment is at most its model length. -/
theorem chart_geodesic_pathELength_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] (p : M) :
    ∃ ρ > 0, ∃ ge : E → E →L[ℝ] E →L[ℝ] ℝ,
      ContDiff ℝ 3 ge ∧
      (∀ y ∈ ball (extChartAt I p p) ρ, ∀ u v : E,
         (ge y) u v = (Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)).inner
                       ((extChartAt I p).symm y)
                       ((mfderiv[range I] (extChartAt I p).symm y) u)
                       ((mfderiv[range I] (extChartAt I p).symm y) v)) ∧
      (∀ {c vel : ℝ → E} {a b : ℝ} {s₀ : ℝ},
         (∀ t ∈ Icc a b, c t ∈ ball (extChartAt I p p) ρ) →
         (∀ t ∈ Icc a b, HasDerivAt c (vel t) t) →
         (∀ t ∈ Icc a b, Real.sqrt (ge (c t) (vel t) (vel t)) = s₀) →
         Manifold.pathELength I ((extChartAt I p).symm ∘ c) a b ≤
           ENNReal.ofReal (s₀ * (b - a))) := by
  rcases chart_speed (I := I) (M := M) p with
    ⟨ρ, hρpos, ge, hgeC, hgeSymm, hgePos, hgeAgree, hspeed⟩
  refine ⟨ρ, hρpos, ge, hgeC, hgeAgree, ?_⟩
  intro c vel a b s₀ hcball hder hsqrt
  -- pointwise, the manifold speed of the chart curve equals the constant model speed `s₀`
  have hpoint : ∀ t ∈ Icc a b,
      ‖mfderiv% ((extChartAt I p).symm ∘ c) t 1‖ₑ = ENNReal.ofReal s₀ := by
    intro t ht
    rw [hspeed (γ := (extChartAt I p).symm ∘ c) (c := c) (t := t) (u := vel t)
      (by intro s; rfl) (hcball t ht) (hder t ht)]
    rw [hsqrt t ht]
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  calc
    (∫⁻ t in Icc a b, ‖mfderiv% ((extChartAt I p).symm ∘ c) t 1‖ₑ)
        = ∫⁻ t in Icc a b, ENNReal.ofReal s₀ :=
            MeasureTheory.setLIntegral_congr_fun measurableSet_Icc hpoint
    _ = ENNReal.ofReal s₀ * volume (Icc a b) := MeasureTheory.setLIntegral_const _ _
    _ = ENNReal.ofReal s₀ * ENNReal.ofReal (b - a) := by rw [Real.volume_Icc]
    _ ≤ ENNReal.ofReal (s₀ * (b - a)) := by
            by_cases hs : 0 ≤ s₀
            · by_cases hba : 0 ≤ b - a
              · rw [ENNReal.ofReal_mul' (p := s₀) (q := b - a) hba]
              · have hba' : b - a ≤ 0 := le_of_not_ge hba
                rw [ENNReal.ofReal_eq_zero.mpr hba']
                simp
            · have hs' : s₀ ≤ 0 := le_of_not_ge hs
              rw [ENNReal.ofReal_eq_zero.mpr hs']
              simp

end

end Submission
