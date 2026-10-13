import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

open MeasureTheory Set

/-- **Coercivity forces non-integrability at the origin.**

If `Ψ` dominates `c / z ^ 2` (with `c > 0`) on the interval `(0, z₁)`, then `Ψ` cannot be
integrable on `[0, ∞)`: the singularity `z ↦ c / z ^ 2` is not integrable on `(0, z₁)`
(`intervalIntegral.integrableOn_Ioo_rpow_iff` with exponent `-2`), and a nonnegative lower
bound by a non-integrable function on a subset forces non-integrability. -/
theorem not_integrableOn_of_lower_rpow {Ψ : ℝ → ℝ} {c z₁ : ℝ} (hc : 0 < c) (hz₁ : 0 < z₁)
    (hlow : ∀ z ∈ Set.Ioo (0 : ℝ) z₁, c / z ^ 2 ≤ Ψ z) :
    ¬ MeasureTheory.IntegrableOn Ψ (Set.Ici 0) := by
  intro h
  -- Restrict the assumed integrability to the interval `(0, z₁) ⊆ [0, ∞)`.
  have hsub : Set.Ioo (0 : ℝ) z₁ ⊆ Set.Ici 0 := fun z hz => le_of_lt hz.1
  have hΨ : IntegrableOn Ψ (Set.Ioo (0 : ℝ) z₁) := h.mono_set hsub
  -- On `(0, z₁)` the coercive bound gives `c / z ^ 2 ≤ Ψ` pointwise.
  have hcz : IntegrableOn (fun z => c / z ^ 2) (Set.Ioo (0 : ℝ) z₁) := by
    refine hΨ.mono' (measurable_const.div (measurable_id.pow_const 2)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    rw [Real.norm_eq_abs, abs_of_pos (div_pos hc (pow_pos hz.1 2))]
    exact hlow z hz
  -- Rewrite `c / z ^ 2` as the real power `z ^ (-2)` on `(0, z₁)`.
  have hpow : IntegrableOn (fun z => z ^ (-2 : ℝ)) (Set.Ioo (0 : ℝ) z₁) := by
    have h1 : IntegrableOn (fun z => c⁻¹ * (c / z ^ 2)) (Set.Ioo (0 : ℝ) z₁) :=
      MeasureTheory.Integrable.const_mul hcz c⁻¹
    refine h1.congr_fun ?_ measurableSet_Ioo
    intro z hz
    show c⁻¹ * (c / z ^ 2) = z ^ (-2 : ℝ)
    rw [Real.rpow_neg (le_of_lt hz.1), Real.rpow_two]
    field_simp
  -- But `z ↦ z ^ (-2)` is *not* integrable on `(0, t)` for `t > 0`, since `-1 < -2` is false.
  have hc2 := (intervalIntegral.integrableOn_Ioo_rpow_iff hz₁ (s := (-2 : ℝ))).mp hpow
  norm_num at hc2

end Work.Coercivity
