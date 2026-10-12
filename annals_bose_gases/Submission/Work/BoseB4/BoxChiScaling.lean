import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseB4.BoxChi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.BoxChiScaling` — the change of variables `x ↦ ℓ⁻¹ x`

Rescaling the box by `ℓ` multiplies Lebesgue measure by `ℓ³`, which is what
turns the unit-cell integrals defining `χ̂`, `χ̂²` (`Work.BoseB4.BoxData.hatChi`,
`hatChiSq`) into the box integrals against `χ_Λ`:

    `∫ χ_Λ e^{ik·x} = ℓ³ χ̂(ℓk)`,   `∫ χ_Λ² e^{ik·x} = ℓ³ χ̂²(ℓk)`,
    `∫ χ_Λ² = ℓ³`.

These are the three integrals of FS's `eq:Commutator_general` computation.
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory Classical

namespace Work.BoseB4

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **Change of variables `x ↦ ℓ⁻¹ x`** on `ℝ³`: Lebesgue measure scales by `ℓ³`. -/
theorem integral_comp_inv_smul_volume {ℓ : ℝ} (hℓ : 0 < ℓ) (g : ℝ³ → ℝ) :
    ∫ x, g (ℓ⁻¹ • x) = ℓ ^ 3 * ∫ y, g y := by
  have h := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure ℝ³) g hℓ.le
  rw [finrank_euclideanSpace_fin] at h
  rw [h, smul_eq_mul]

namespace BoxData

variable (B : BoxData)

/-- `∫ χ_Λ e^{ik·x} = ℓ³ χ̂(ℓk)`: the first integral of FS
`eq:Commutator_general`.  (The complex exponential is expressed through `cos`;
the sine part integrates to `0` because `χ` is even.) -/
theorem integral_chiLam_mul_cos {ℓ : ℝ} (hℓ : 0 < ℓ) (p : ℝ³) :
    ∫ x, B.chiLam ℓ x * Real.cos (inner ℝ p x) = ℓ ^ 3 * B.hatChi (ℓ • p) := by
  have hℓ0 : ℓ ≠ 0 := ne_of_gt hℓ
  have h := integral_comp_inv_smul_volume hℓ
    (fun y : ℝ³ => B.chi y * Real.cos (inner ℝ (ℓ • p) y))
  rw [hatChi]
  trans ∫ x, (fun y : ℝ³ => B.chi y * Real.cos (inner ℝ (ℓ • p) y)) (ℓ⁻¹ • x)
  · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [chiLam]
    congr 1
    rw [real_inner_smul_right, real_inner_smul_left, ← mul_assoc, inv_mul_cancel₀ hℓ0,
      one_mul]
  · rw [h]

/-- `∫ χ_Λ² e^{ik·x} = ℓ³ χ̂²(ℓk)`: the second integral of FS
`eq:Commutator_general`. -/
theorem integral_chiLam_sq_mul_cos {ℓ : ℝ} (hℓ : 0 < ℓ) (p : ℝ³) :
    ∫ x, (B.chiLam ℓ x) ^ 2 * Real.cos (inner ℝ p x) = ℓ ^ 3 * B.hatChiSq (ℓ • p) := by
  have hℓ0 : ℓ ≠ 0 := ne_of_gt hℓ
  have h := integral_comp_inv_smul_volume hℓ
    (fun y : ℝ³ => (B.chi y) ^ 2 * Real.cos (inner ℝ (ℓ • p) y))
  rw [hatChiSq]
  trans ∫ x, (fun y : ℝ³ => (B.chi y) ^ 2 * Real.cos (inner ℝ (ℓ • p) y)) (ℓ⁻¹ • x)
  · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [chiLam]
    congr 1
    rw [real_inner_smul_right, real_inner_smul_left, ← mul_assoc, inv_mul_cancel₀ hℓ0,
      one_mul]
  · rw [h]

/-- `∫ χ_Λ² = ℓ³ = volume Λ(ℓ)`: FS's normalisation `∫χ² = 1` on the box. -/
theorem integral_chiLam_sq {ℓ : ℝ} (hℓ : 0 < ℓ) : ∫ x, (B.chiLam ℓ x) ^ 2 = ℓ ^ 3 := by
  have h := integral_comp_inv_smul_volume hℓ (fun y : ℝ³ => (B.chi y) ^ 2)
  simp only [chiLam]
  rw [h, B.chi_int, mul_one]

end BoxData

end Work.BoseB4
