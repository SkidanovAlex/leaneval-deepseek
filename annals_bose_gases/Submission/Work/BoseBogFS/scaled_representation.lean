import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Circle
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

/-- **Dilation of a Fourier-inversion representation** (`0 < ε`): if `Φ` (and its first moment) is
integrable and `F x = ∫ η, 𝐞⟪η,x⟫ • Φ η` pointwise, then the dilated function `x ↦ F (ε • x)` is
represented by the dilated profile `u ↦ (ε^3)⁻¹ • Φ (ε⁻¹ • u)`, that profile is integrable, and its
first moment is at most `(1+ε)` times the first moment of `Φ`.
Hints (`open MeasureTheory`): substitute `u = ε • η` in the representation integral using
`MeasureTheory.Measure.integral_comp_smul (volume) (fun u => 𝐞⟪u,x⟫ • Φ u) (ε⁻¹)`, which gives
`∫ η, f (ε⁻¹ • η) = |((ε⁻¹)^3)⁻¹| • ∫ u, f u = ε^3 • ∫ u, f u` (since `finrank ℝ ℝ³ = 3`);
`MeasureTheory.integral_const_mul`/`MeasureTheory.integral_smul` then moves the `(ε^3)⁻¹` scalar;
`real_inner_smul_left`, `real_inner_smul_right` and `ε * ε⁻¹ = 1` (from `hε`) handle the inner
products.  Integrability: `MeasureTheory.Integrable.comp_smul hΦ (ne_of_gt hε)` for
`η ↦ Φ (ε⁻¹ • η)` plus a constant multiplication.  The moment inequality: rewrite the moment of the
dilated profile by the same substitution, then apply
`MeasureTheory.integral_mono_of_nonneg` to the pointwise
`(1 + ε * ‖v‖) * ‖Φ v‖ ≤ (1 + ε) * ((1 + ‖v‖) * ‖Φ v‖)` (`nlinarith` from `0 ≤ ‖v‖`, `0 < ε`). -/
theorem scaled_representation {F : EuclideanSpace ℝ (Fin 3) → ℝ}
    {Φ : EuclideanSpace ℝ (Fin 3) → ℂ} {ε : ℝ} (hε : 0 < ε)
    (h : ∀ x, (F x : ℂ) = ∫ η, Real.fourierChar (inner ℝ η x) • Φ η)
    (hΦ : MeasureTheory.Integrable Φ)
    (hΦm : MeasureTheory.Integrable (fun η => (1 + ‖η‖) * ‖Φ η‖)) :
    (∀ x, (F (ε • x) : ℂ) = ∫ η, Real.fourierChar (inner ℝ η x) • ((ε ^ 3)⁻¹ • Φ (ε⁻¹ • η)))
      ∧ MeasureTheory.Integrable (fun η => (ε ^ 3)⁻¹ • Φ (ε⁻¹ • η))
      ∧ (∫ η, (1 + ‖η‖) * ‖(ε ^ 3)⁻¹ • Φ (ε⁻¹ • η)‖) ≤ (1 + ε) * (∫ η, (1 + ‖η‖) * ‖Φ η‖) := by
  have hεne : ε ≠ 0 := ne_of_gt hε
  -- integrability of the dilated profile: substitute and multiply by a constant
  have hint : MeasureTheory.Integrable (fun η => (ε ^ 3)⁻¹ • Φ (ε⁻¹ • η)) :=
    MeasureTheory.Integrable.smul ((ε ^ 3)⁻¹) (hΦ.comp_smul (inv_ne_zero hεne))
  -- the dilation factor produced by `Measure.integral_comp_smul`
  have habs1 : |(((ε⁻¹) : ℝ) ^ (3 : ℕ))⁻¹| = ε ^ 3 := by
    rw [← inv_pow, inv_inv, abs_of_pos (by positivity : (0 : ℝ) < ε ^ 3)]
  -- the substitution rule in the complex-valued case
  have hsubstC : ∀ (g : EuclideanSpace ℝ (Fin 3) → ℂ),
      (∫ η, g (ε⁻¹ • η)) = ε ^ 3 • ∫ u, g u := by
    intro g
    have hg := MeasureTheory.Measure.integral_comp_smul
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) g (ε⁻¹)
    rw [show Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 from by simp] at hg
    rwa [habs1] at hg
  -- the representation
  have key : ∀ x, (F (ε • x) : ℂ)
      = ∫ η, Real.fourierChar (inner ℝ η x) • ((ε ^ 3)⁻¹ • Φ (ε⁻¹ • η)) := by
    intro x
    have h1 : (∫ η, Real.fourierChar (inner ℝ η x) • ((ε ^ 3)⁻¹ • Φ (ε⁻¹ • η)))
        = (ε ^ 3)⁻¹ • (∫ η, Real.fourierChar (inner ℝ η x) • Φ (ε⁻¹ • η)) := by
      rw [← MeasureTheory.integral_smul]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with η
      rw [smul_comm]
    have h2 : (∫ η, Real.fourierChar (inner ℝ η x) • Φ (ε⁻¹ • η))
        = ε ^ 3 • (F (ε • x) : ℂ) := by
      have hpt : (fun η => Real.fourierChar (inner ℝ η x) • Φ (ε⁻¹ • η))
          = (fun η => (fun u => Real.fourierChar (inner ℝ u (ε • x)) • Φ u) (ε⁻¹ • η)) := by
        funext η
        simp only
        congr 1
        rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, inv_mul_cancel₀ hεne,
          one_mul]
      rw [hpt, hsubstC (fun u => Real.fourierChar (inner ℝ u (ε • x)) • Φ u), ← h (ε • x)]
    rw [h1, h2, smul_smul, inv_mul_cancel₀ (by positivity : ε ^ 3 ≠ 0), one_smul]
  -- the first moment of the dilated profile
  have hmom : (∫ η, (1 + ‖η‖) * ‖(ε ^ 3)⁻¹ • Φ (ε⁻¹ • η)‖)
      = ∫ u, (1 + ε * ‖u‖) * ‖Φ u‖ := by
    have hA : (∫ η, (1 + ‖η‖) * ‖(ε ^ 3)⁻¹ • Φ (ε⁻¹ • η)‖)
        = |(ε ^ 3)⁻¹| * ∫ η, (1 + ‖η‖) * ‖Φ (ε⁻¹ • η)‖ := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with η
      rw [norm_smul, Real.norm_eq_abs]
      ring
    have hB : (∫ η, (1 + ‖η‖) * ‖Φ (ε⁻¹ • η)‖)
        = ε ^ 3 * ∫ u, (1 + ε * ‖u‖) * ‖Φ u‖ := by
      have hg := MeasureTheory.Measure.integral_comp_smul
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
        (fun u => (1 + ε * ‖u‖) * ‖Φ u‖) (ε⁻¹)
      rw [show Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 from by simp] at hg
      rw [habs1, smul_eq_mul] at hg
      rw [← hg]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with η
      congr 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε), ← mul_assoc,
        mul_inv_cancel₀ hεne, one_mul]
    rw [hA, hB, abs_of_pos (by positivity : (0 : ℝ) < (ε ^ 3)⁻¹), ← mul_assoc,
      inv_mul_cancel₀ (by positivity : ε ^ 3 ≠ 0), one_mul]
  refine ⟨key, hint, ?_⟩
  rw [hmom]
  rw [← MeasureTheory.integral_const_mul (1 + ε) (fun η => (1 + ‖η‖) * ‖Φ η‖)]
  apply MeasureTheory.integral_mono_of_nonneg
  · filter_upwards with u
    positivity
  · exact hΦm.const_mul (1 + ε)
  · filter_upwards with u
    have h1 : (1 + ε * ‖u‖) ≤ (1 + ε) * (1 + ‖u‖) := by nlinarith [norm_nonneg u, hε]
    calc (1 + ε * ‖u‖) * ‖Φ u‖ ≤ ((1 + ε) * (1 + ‖u‖)) * ‖Φ u‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = (1 + ε) * ((1 + ‖u‖) * ‖Φ u‖) := by ring

end Work.BoseBogFS
