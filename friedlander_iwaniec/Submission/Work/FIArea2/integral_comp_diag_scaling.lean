import Mathlib
import Submission.Work.FIArea2.Sec6Defs

namespace Work.FIArea2

open MeasureTheory

/-- Diagonal scaling of the Lebesgue integral on `ℝ × ℝ`.

For `a, b > 0` the change of variables `t ↦ (t.1 / a, t.2 / b)` multiplies the
(Lebesgue) integral by `a * b`, the reciprocal of the determinant of the linear
map `(x, y) ↦ (x / a, y / b)`.  The identity is unconditional: when `Ψ` is not
integrable both sides vanish by the convention for the Bochner integral. -/
lemma integral_comp_diag_scaling (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (Ψ : ℝ × ℝ → ℂ) :
    ∫ t : ℝ × ℝ, Ψ (t.1 / a, t.2 / b) = (a * b) * ∫ t : ℝ × ℝ, Ψ t := by
  have ha' : a ≠ 0 := ha.ne'
  have hb' : b ≠ 0 := hb.ne'
  -- The measurable equivalence `t ↦ (t.1 / a, t.2 / b)`.
  let e : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
    (Homeomorph.prodCongr (Homeomorph.mulRight₀ a⁻¹ (inv_ne_zero ha'))
      (Homeomorph.mulRight₀ b⁻¹ (inv_ne_zero hb'))).toMeasurableEquiv
  have hefun : (⇑e : ℝ × ℝ → ℝ × ℝ) = fun t => (t.1 * a⁻¹, t.2 * b⁻¹) := by
    funext t
    rcases t with ⟨x, y⟩
    simp only [e, Homeomorph.toMeasurableEquiv_coe, Homeomorph.coe_prodCongr,
      Homeomorph.coe_mulRight₀, Prod.map_apply]
  have he : ∀ t : ℝ × ℝ, e t = (t.1 / a, t.2 / b) := by
    intro t
    rw [hefun]
    simp only [div_eq_mul_inv]
  -- Pushforward of Lebesgue measure: it is multiplied by `a * b`.
  have hmap_lambda : Measure.map (fun t : ℝ × ℝ => (t.1 * a⁻¹, t.2 * b⁻¹))
      (volume : Measure (ℝ × ℝ)) = ENNReal.ofReal (a * b) • volume := by
    change Measure.map (Prod.map (fun x : ℝ => x * a⁻¹) (fun y : ℝ => y * b⁻¹))
      (volume : Measure (ℝ × ℝ)) = ENNReal.ofReal (a * b) • volume
    rw [Measure.volume_eq_prod ℝ ℝ,
      ← Measure.map_prod_map (volume : Measure ℝ) (volume : Measure ℝ)
        (measurable_mul_const a⁻¹) (measurable_mul_const b⁻¹)]
    simp only [Real.map_volume_mul_right (inv_ne_zero ha'),
      Real.map_volume_mul_right (inv_ne_zero hb'), inv_inv, abs_of_pos ha, abs_of_pos hb]
    rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
      ← ENNReal.ofReal_mul ha.le]
  have hmap : Measure.map e (volume : Measure (ℝ × ℝ)) = ENNReal.ofReal (a * b) • volume := by
    rw [hefun]; exact hmap_lambda
  calc ∫ t : ℝ × ℝ, Ψ (t.1 / a, t.2 / b)
      = ∫ t : ℝ × ℝ, Ψ (e t) := by simp only [he]
    _ = ∫ y : ℝ × ℝ, Ψ y ∂(Measure.map e (volume : Measure (ℝ × ℝ))) :=
        (integral_map_equiv e Ψ).symm
    _ = ∫ y : ℝ × ℝ, Ψ y ∂(ENNReal.ofReal (a * b) • volume) := by rw [hmap]
    _ = (ENNReal.ofReal (a * b)).toReal • ∫ y : ℝ × ℝ, Ψ y ∂volume :=
        integral_smul_measure Ψ _
    _ = (a * b) * ∫ t : ℝ × ℝ, Ψ t := by
        rw [ENNReal.toReal_ofReal (mul_nonneg ha.le hb.le), Complex.real_smul,
          Complex.ofReal_mul]

end Work.FIArea2
