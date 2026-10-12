import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.LatGreen

/-- **Pointwise kernel bound.** For any `q, η` in a real normed space,
`1/(1 + ‖(2π)⁻¹ • q - η‖) ≤ (2π)² (1+‖η‖)/(1+‖q‖)`.

This is the pointwise inequality behind `InvOneAddNormSubIntegralLe`: write
`‖(2π)⁻¹ • q - η‖ = (2π)⁻¹ ‖q - 2π • η‖` and use the reverse triangle inequality
`1 + ‖q‖ ≤ (1 + ‖q - 2π•η‖)(1 + ‖2π•η‖)` together with `1 + ‖2π•η‖ ≤ 2π (1 + ‖η‖)`
(and `(2π)⁻¹ ≤ 1`, `1 ≤ 2π`). -/
lemma inv_one_add_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (q η : E) :
    1 / (1 + ‖(2 * Real.pi)⁻¹ • q - η‖) ≤
      (2 * Real.pi) ^ 2 * (1 + ‖η‖) / (1 + ‖q‖) := by
  have h2πpos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2π1 : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hinvle : (2 * Real.pi)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h2π1
  set p : ℝ := ‖q - (2 * Real.pi) • η‖ with hp_def
  have hp : 0 ≤ p := by rw [hp_def]; exact norm_nonneg _
  -- `1 + ‖q‖ ≤ (1+p)(1+‖2π•η‖)` (reverse triangle inequality)
  have hB : 1 + ‖q‖ ≤ (1 + p) * (1 + ‖(2 * Real.pi) • η‖) := by
    rw [hp_def]
    have h := norm_add_le (q - (2 * Real.pi) • η) ((2 * Real.pi) • η)
    rw [sub_add_cancel] at h
    nlinarith [h, norm_nonneg (q - (2 * Real.pi) • η), norm_nonneg ((2 * Real.pi) • η)]
  -- `1 + ‖2π•η‖ ≤ 2π (1+‖η‖)`
  have hC : 1 + ‖(2 * Real.pi) • η‖ ≤ 2 * Real.pi * (1 + ‖η‖) := by
    rw [norm_smul, Real.norm_of_nonneg (le_of_lt h2πpos)]
    nlinarith [h2π1, norm_nonneg η]
  -- `(2π)⁻¹ (1+p) ≤ 1 + ‖(2π)⁻¹ • q - η‖`
  have hA : (2 * Real.pi)⁻¹ * (1 + p) ≤ 1 + ‖(2 * Real.pi)⁻¹ • q - η‖ := by
    rw [show ‖(2 * Real.pi)⁻¹ • q - η‖ = (2 * Real.pi)⁻¹ * p from by
        rw [hp_def]
        rw [show (2 * Real.pi)⁻¹ • q - η = (2 * Real.pi)⁻¹ • (q - (2 * Real.pi) • η) from by
              rw [smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt h2πpos), one_smul]]
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]]
    nlinarith [hinvle]
  have hApos : (0 : ℝ) < (2 * Real.pi)⁻¹ * (1 + p) := by positivity
  have hden : (0 : ℝ) < 1 + p := by linarith
  have hdenq : (0 : ℝ) < 1 + ‖q‖ := by
    have := norm_nonneg q; linarith
  calc
    1 / (1 + ‖(2 * Real.pi)⁻¹ • q - η‖) ≤ 2 * Real.pi / (1 + p) := by
      have h1 := one_div_le_one_div_of_le hApos hA
      rwa [show 1 / ((2 * Real.pi)⁻¹ * (1 + p)) = 2 * Real.pi / (1 + p) from by
            rw [div_eq_mul_inv, mul_inv_rev, inv_inv, one_mul, div_eq_mul_inv, mul_comm]] at h1
    _ ≤ 2 * Real.pi * (1 + ‖(2 * Real.pi) • η‖) / (1 + ‖q‖) := by
      rw [div_le_div_iff₀ hden hdenq]
      have h2 : 2 * Real.pi * (1 + ‖q‖) ≤
          2 * Real.pi * ((1 + p) * (1 + ‖(2 * Real.pi) • η‖)) :=
        mul_le_mul_of_nonneg_left hB (le_of_lt h2πpos)
      have heq : 2 * Real.pi * ((1 + p) * (1 + ‖(2 * Real.pi) • η‖))
          = (2 * Real.pi * (1 + ‖(2 * Real.pi) • η‖)) * (1 + p) := by ring
      linarith [h2, heq]
    _ ≤ 2 * Real.pi * (2 * Real.pi * (1 + ‖η‖)) / (1 + ‖q‖) := by
      rw [div_le_div_iff₀ hdenq hdenq]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hC (le_of_lt h2πpos)) (le_of_lt hdenq)
    _ = (2 * Real.pi) ^ 2 * (1 + ‖η‖) / (1 + ‖q‖) := by ring

/-- **Kernel estimate for a decaying amplitude against `1/(1+‖·‖)`** (namespace
`Work.BoseFixR.LatGreen`).

For a complex function `Φ` on `ℝ³` which is integrable and has a finite first moment
(`Integrable (fun η => (1+‖η‖)·‖Φ η‖)`), and every `q`,

`∫_η ‖Φ η‖/(1 + ‖(2π)⁻¹ • q - η‖) dη ≤ (2π)² · (∫_η (1+‖η‖)·‖Φ η‖ dη) / (1 + ‖q‖)`.

Proof: the pointwise inequality
`1/(1+‖(2π)⁻¹ • q - η‖) ≤ (2π)² (1+‖η‖)/(1+‖q‖)`, which follows from
`1 + ‖ν - η‖ ≥ (2π)⁻¹ (1 + ‖2πν - 2πη‖)` (as `(2π)⁻¹ ≤ 1`),
`1 + ‖q‖ ≤ (1 + ‖q - 2πη‖)(1 + ‖2πη‖)` (reverse triangle inequality), and
`1 + ‖2πη‖ ≤ 2π (1 + ‖η‖)` (`1 ≤ 2π`).
Multiply by `‖Φ η‖ ≥ 0` and integrate, using the integrability of
`η ↦ (1+‖η‖)‖Φ η‖` to justify the comparison. -/
theorem InvOneAddNormSubIntegralLe {Φ : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hΦ : MeasureTheory.Integrable Φ)
    (hmom : MeasureTheory.Integrable (fun η : EuclideanSpace ℝ (Fin 3) => (1 + ‖η‖) * ‖Φ η‖)) :
    ∀ q : EuclideanSpace ℝ (Fin 3),
      (∫ η : EuclideanSpace ℝ (Fin 3), ‖Φ η‖ / (1 + ‖(2 * Real.pi)⁻¹ • q - η‖)) ≤
        (2 * Real.pi) ^ 2 * (∫ η : EuclideanSpace ℝ (Fin 3), (1 + ‖η‖) * ‖Φ η‖) / (1 + ‖q‖) := by
  -- `hΦ` records that `Φ` is an integrable amplitude; the comparison below needs only
  -- the integrability of the dominating function `η ↦ (1+‖η‖)‖Φ η‖`.
  have _hΦ := hΦ
  intro q
  -- pointwise inequality, obtained by multiplying the kernel bound by `‖Φ η‖ ≥ 0`
  have hpt : ∀ η : EuclideanSpace ℝ (Fin 3), ‖Φ η‖ / (1 + ‖(2 * Real.pi)⁻¹ • q - η‖) ≤
      (2 * Real.pi) ^ 2 * ((1 + ‖η‖) * ‖Φ η‖) / (1 + ‖q‖) := by
    intro η
    have h0 : 0 ≤ ‖Φ η‖ := norm_nonneg _
    have hk := inv_one_add_norm_le q η
    calc ‖Φ η‖ / (1 + ‖(2 * Real.pi)⁻¹ • q - η‖)
        = ‖Φ η‖ * (1 / (1 + ‖(2 * Real.pi)⁻¹ • q - η‖)) := by rw [div_eq_mul_one_div]
      _ ≤ ‖Φ η‖ * ((2 * Real.pi) ^ 2 * (1 + ‖η‖) / (1 + ‖q‖)) :=
            mul_le_mul_of_nonneg_left hk h0
      _ = (2 * Real.pi) ^ 2 * ((1 + ‖η‖) * ‖Φ η‖) / (1 + ‖q‖) := by ring
  have hint : MeasureTheory.Integrable (fun η : EuclideanSpace ℝ (Fin 3) =>
      (2 * Real.pi) ^ 2 * ((1 + ‖η‖) * ‖Φ η‖) / (1 + ‖q‖)) :=
    (hmom.const_mul _).div_const _
  calc ∫ η, ‖Φ η‖ / (1 + ‖(2 * Real.pi)⁻¹ • q - η‖)
      ≤ ∫ η, (2 * Real.pi) ^ 2 * ((1 + ‖η‖) * ‖Φ η‖) / (1 + ‖q‖) :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall (by intro η; positivity)) hint
          (Filter.Eventually.of_forall hpt)
    _ = (2 * Real.pi) ^ 2 * (∫ η, (1 + ‖η‖) * ‖Φ η‖) / (1 + ‖q‖) := by
        rw [MeasureTheory.integral_div, MeasureTheory.integral_const_mul]

end Work.BoseFixR.LatGreen
