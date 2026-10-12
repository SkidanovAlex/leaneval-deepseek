import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB3.CS.Pieces

open MeasureTheory

/-- Chebyshev/Markov-type shell bound: if `f ≥ 0` and `‖·‖ ^ 80 * f` is integrable, then
the integral of `f` over the exterior shell `{‖q‖ ≥ κ}` is controlled by
`κ ^ (-80)` times the full weight-`‖·‖ ^ 80` integral. -/
theorem hp_shell_integral_le (f : EuclideanSpace ℝ (Fin 3) → ℝ) (κ : ℝ) (hκ : 0 < κ)
    (hf : AEMeasurable f MeasureTheory.volume) (hfn : 0 ≤ f)
    (hint : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => ‖p‖ ^ 80 * f p)
      MeasureTheory.volume) :
    ∫ p in {q : EuclideanSpace ℝ (Fin 3) | κ ≤ ‖q‖}, f p
      ≤ (κ ^ 80)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3), ‖p‖ ^ 80 * f p := by
  classical
  have hmeas : MeasurableSet {q : EuclideanSpace ℝ (Fin 3) | κ ≤ ‖q‖} :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  rw [← integral_indicator hmeas]
  -- On the shell, `f` is dominated by `(κ ^ 80)⁻¹ * ‖p‖ ^ 80 * f`; outside it the indicator is `0`.
  have hle : (fun p : EuclideanSpace ℝ (Fin 3) =>
        {q : EuclideanSpace ℝ (Fin 3) | κ ≤ ‖q‖}.indicator f p)
      ≤ fun p => (κ ^ 80)⁻¹ * (‖p‖ ^ 80 * f p) := by
    intro p
    show {q : EuclideanSpace ℝ (Fin 3) | κ ≤ ‖q‖}.indicator f p
      ≤ (κ ^ 80)⁻¹ * (‖p‖ ^ 80 * f p)
    by_cases hp : p ∈ {q : EuclideanSpace ℝ (Fin 3) | κ ≤ ‖q‖}
    · rw [Set.indicator_of_mem hp]
      have hpκ : κ ≤ ‖p‖ := hp
      have h1 : κ ^ 80 ≤ ‖p‖ ^ 80 := pow_le_pow_left₀ hκ.le hpκ 80
      have h2 : (0 : ℝ) ≤ (κ ^ 80)⁻¹ := inv_nonneg.mpr (pow_nonneg hκ.le 80)
      have hmul : κ ^ 80 * f p ≤ ‖p‖ ^ 80 * f p := mul_le_mul_of_nonneg_right h1 (hfn p)
      calc f p = (κ ^ 80)⁻¹ * (κ ^ 80 * f p) := by
              rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 80 hκ.ne'), one_mul]
        _ ≤ (κ ^ 80)⁻¹ * (‖p‖ ^ 80 * f p) := mul_le_mul_of_nonneg_left hmul h2
    · rw [Set.indicator_of_notMem hp]
      exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hκ.le 80))
        (mul_nonneg (pow_nonneg (norm_nonneg _) 80) (hfn p))
  have hnonneg : 0 ≤ᵐ[MeasureTheory.volume]
      (fun p : EuclideanSpace ℝ (Fin 3) =>
        {q : EuclideanSpace ℝ (Fin 3) | κ ≤ ‖q‖}.indicator f p) :=
    Filter.Eventually.of_forall (fun p => Set.indicator_nonneg (fun a _ => hfn a) p)
  have key := integral_mono_of_nonneg hnonneg (hint.const_mul _) (Filter.Eventually.of_forall hle)
  rwa [integral_const_mul] at key

end Work.BoseFixB3.CS.Pieces
