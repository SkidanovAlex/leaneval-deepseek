import ChallengeDeps
import Submission.Work.BoseBoxFock.PCFU.frameSmear
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.chiW1_integrable`

Bochner-integrability of the windowed two-body kernel

`(p : ℝ³ × ℝ³) ↦ χ_ℓ(p.1) · W₁(p.1 − p.2) · χ_ℓ(p.2)`,

`W₁ = wScaled ℓ (g₀ v h)`, with respect to `volume × volume`.

The two analytic ingredients are the corpus's
`Work.BoseFixB2.Pot.lintegral_wPairC_le` (the joint `∫⁻` of the renormalised pair
kernel is finite as soon as the numerator is *integrable*) and
`Work.BoseFixB2.Pot.aemeasurable_wPairC_prod`.

`ScatSol v` alone makes `g₀ = v(1−w)` only *locally* integrable
(`IsScatteringSolution.rhs_integrable`), so the reduction is: the product
integrand is supported in `closedBall 0 (ℓ/2) × closedBall 0 (ℓ/2)`
(`chiScale_support_le`), hence only the values of `g₀` on `closedBall 0 ℓ` matter.
Replacing `g₀` by its truncation `G := 1_{closedBall 0 (2ℓ)}·g₀` — globally
integrable, being the indicator of a compact set times a locally integrable
function — therefore leaves the pair kernel unchanged
(`wPairC_congr_of_ball`), and `lintegral_wPairC_le` applies to `G`.
-/

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

/-- `g₀ v h = v·(1 − w)` is locally integrable, from `ScatSol v` alone. -/
lemma locallyIntegrable_g0 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) :
    MeasureTheory.LocallyIntegrable (Submission.BoseGases.g0 v h) := by
  have heq : (v * (1 - Classical.choose h)) = Submission.BoseGases.g0 v h := by
    funext x
    simp [Submission.BoseGases.g0, Pi.mul_apply]
  rw [← heq]
  exact (Classical.choose_spec h).2.rhs_integrable

/-- Two numerators that agree on `closedBall 0 ℓ` give the same renormalised pair
kernel `wPairC ℓ ·`: the product kernel is supported where both windows are
nonzero, which forces `‖p.1 − p.2‖ ≤ ℓ`. -/
lemma wPairC_congr_of_ball {g₁ g₂ : EuclideanSpace ℝ (Fin 3) → ℝ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (h : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ ℓ → g₁ z = g₂ z)
    (p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.wPairC ℓ g₁ p.1 p.2 = Submission.BoseGases.wPairC ℓ g₂ p.1 p.2 := by
  by_cases h1 : Submission.BoseGases.chiScale ℓ p.1 = 0
  · simp only [Submission.BoseGases.wPairC, Submission.BoseGases.wPair, h1, zero_mul]
  · by_cases h2 : Submission.BoseGases.chiScale ℓ p.2 = 0
    · simp only [Submission.BoseGases.wPairC, Submission.BoseGases.wPair, h2, mul_zero]
    · have hz : ‖p.1 - p.2‖ ≤ ℓ := by
        have hA : ‖p.1‖ ≤ ℓ / 2 := Submission.BoseGases.chiScale_support_le hℓ h1
        have hB : ‖p.2‖ ≤ ℓ / 2 := Submission.BoseGases.chiScale_support_le hℓ h2
        have := norm_sub_le p.1 p.2
        linarith
      simp only [Submission.BoseGases.wPairC, Submission.BoseGases.wPair]
      rw [Submission.BoseGases.wScaled, Submission.BoseGases.wScaled, h (p.1 - p.2) hz]

/-- The truncated numerator `1_{‖·‖ ≤ 2ℓ}·g₀` is integrable. -/
lemma integrable_indicator_g0 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {ℓ : ℝ} :
    MeasureTheory.Integrable
      ((Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (2 * ℓ)).indicator
        (Submission.BoseGases.g0 v h)) :=
  ((locallyIntegrable_g0 h).integrableOn_isCompact (isCompact_closedBall _ _)).integrable_indicator
    measurableSet_closedBall

theorem chiW1_integrable {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiScale ℓ p.1
          * (Work.BoseFixR.W1fun v h ℓ (p.1 - p.2) : ℝ)
          * Submission.BoseGases.chiScale ℓ p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod MeasureTheory.volume) := by
  set G : EuclideanSpace ℝ (Fin 3) → ℝ :=
    (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (2 * ℓ)).indicator
      (Submission.BoseGases.g0 v h) with hGdef
  have hGint : MeasureTheory.Integrable G := by
    rw [hGdef]
    exact integrable_indicator_g0 h
  have hGeq : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ ℓ → G z = Submission.BoseGases.g0 v h z := by
    intro z hz
    rw [hGdef]
    refine Set.indicator_of_mem ?_ _
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  -- the `‖·‖ₑ`-form of the finiteness supplied by the corpus
  have hbridge : (∫⁻ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
        ‖Submission.BoseGases.wPairC ℓ G p.1 p.2‖ₑ
        ∂((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          MeasureTheory.volume))
      = ∫⁻ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal ‖Submission.BoseGases.wPairC ℓ G p.1 p.2‖
        ∂((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          MeasureTheory.volume) := by
    refine MeasureTheory.lintegral_congr (fun p => ?_)
    rw [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs]
  have hbase : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wPairC ℓ G p.1 p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        MeasureTheory.volume) := by
    refine ⟨Work.BoseFixB2.Pot.aemeasurable_wPairC_prod hGint.aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_norm, ← hbridge]
    exact lt_of_le_of_lt (Work.BoseFixB2.Pot.lintegral_wPairC_le hℓ hGint) ENNReal.ofReal_lt_top
  refine hbase.congr (Filter.Eventually.of_forall ?_)
  intro p
  show Submission.BoseGases.wPairC ℓ G p.1 p.2
      = Submission.BoseGases.chiScale ℓ p.1 * (Work.BoseFixR.W1fun v h ℓ (p.1 - p.2) : ℝ)
        * Submission.BoseGases.chiScale ℓ p.2
  rw [wPairC_congr_of_ball hℓ hGeq p]
  simp only [Work.BoseFixR.W1fun, Submission.BoseGases.wPairC, Submission.BoseGases.wPair]

end Work.BoseBoxFock.PCFU
