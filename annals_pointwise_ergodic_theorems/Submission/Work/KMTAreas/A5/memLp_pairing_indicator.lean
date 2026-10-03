import Mathlib
import Submission.Work.KMTAreas.A5.Basic
import Submission.Work.Analysis.Interpolation.riesz_thorin_linear

namespace Work.KMTAreas.A5

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-!
# The pairing of two indicator functions is in `ℓ¹`

Let `T` be a bilinear-type operator on functions `ℤ → ℂ` whose `ℒ¹` seminorm is controlled by the
`ℒ^{p₀}` and `ℒ^{q₀}` seminorms of its two arguments (`h₀`, with `p₀, q₀ > 0`).  If `F` and `G`
are complex-valued simple functions whose non-zero level sets have finite counting measure, and if
`c ∈ F.range`, `d ∈ G.range` are non-zero level values, then `T` applied to the two indicator
functions of the level sets `F ⁻¹' {c}` and `G ⁻¹' {d}` belongs to `ℓ¹(ℤ)`.

The proof is a direct consequence of the hypothesis: an indicator function of a set of finite
counting measure lies in every `ℒ^p`, `p > 0` (`memLp_indicator_const`, the set being measurable
because `ℤ` carries the discrete measurable space), and the `eLpNorm` of a function is finite as
soon as it is bounded by a product of finite `eLpNorm`s (`ENNReal.mul_lt_top`).  Since every
function on the countable type `ℤ` is a.e. strongly measurable
(`AEStronglyMeasurable.of_discrete`), this gives `MemLp` at exponent `1`.
-/

theorem memLp_pairing_indicator (T : (ℤ → ℂ) → (ℤ → ℂ) → (ℤ → ℂ)) {p₀ q₀ : ℝ}
    (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) {M : NNReal}
    (h₀ : ∀ u v : ℤ → ℂ, MeasureTheory.eLpNorm (T u v) 1 MeasureTheory.Measure.count
      ≤ (M : ENNReal) * MeasureTheory.eLpNorm u (ENNReal.ofReal p₀) MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm v (ENNReal.ofReal q₀) MeasureTheory.Measure.count)
    {F G : MeasureTheory.SimpleFunc ℤ ℂ}
    (hF : ∀ c ∈ F.range, c ≠ 0 → MeasureTheory.Measure.count (F ⁻¹' {c}) < ⊤)
    (hG : ∀ d ∈ G.range, d ≠ 0 → MeasureTheory.Measure.count (G ⁻¹' {d}) < ⊤)
    {c d : ℂ} (hc : c ∈ F.range) (hd : d ∈ G.range) (hc0 : c ≠ 0) (hd0 : d ≠ 0) :
    MeasureTheory.MemLp (T (Set.indicator (F ⁻¹' {c}) (fun _ => (1 : ℂ)))
      (Set.indicator (G ⁻¹' {d}) (fun _ => (1 : ℂ)))) 1 MeasureTheory.Measure.count := by
  have hF' : MeasureTheory.Measure.count (F ⁻¹' {c}) ≠ ⊤ := ne_of_lt (hF c hc hc0)
  have hG' : MeasureTheory.Measure.count (G ⁻¹' {d}) ≠ ⊤ := ne_of_lt (hG d hd hd0)
  have hu : MeasureTheory.MemLp (Set.indicator (F ⁻¹' {c}) (fun _ => (1 : ℂ)))
      (ENNReal.ofReal p₀) MeasureTheory.Measure.count :=
    MeasureTheory.memLp_indicator_const _ (MeasurableSet.of_discrete) _ (Or.inr hF')
  have hv : MeasureTheory.MemLp (Set.indicator (G ⁻¹' {d}) (fun _ => (1 : ℂ)))
      (ENNReal.ofReal q₀) MeasureTheory.Measure.count :=
    MeasureTheory.memLp_indicator_const _ (MeasurableSet.of_discrete) _ (Or.inr hG')
  refine MeasureTheory.memLp_iff.mpr ?_
  refine lt_of_le_of_lt (h₀ _ _) ?_
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top hu.eLpNorm_lt_top)
    hv.eLpNorm_lt_top

end Work.KMTAreas.A5
