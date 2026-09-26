import Mathlib
import Submission.Work.Modular.Poisson.Periodize

/-!
# Change of variables for a linear equivalence, on set integrals

For a real linear equivalence `e` of `EuclideanSpace ℝ (Fin n)`, the set integral of a `ℂ`-valued
function over the preimage `e ⁻¹' s` is the set integral of the transported function over `s`,
scaled by the inverse absolute determinant of `e`:

`∫ z in e ⁻¹' s, g z = |det e|⁻¹ • ∫ w in s, g (e.symm w)`.

This is the change-of-variables formula for the Lebesgue measure, whose pushforward under `e` is
`|det e|⁻¹ • volume` (`MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar`). The
transformation of the set integral itself is `MeasureTheory.setIntegral_map_equiv`.
-/

open MeasureTheory

namespace Work.Poisson

theorem setIntegral_preimage_linearEquiv {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (s : Set (EuclideanSpace ℝ (Fin n))) (g : EuclideanSpace ℝ (Fin n) → ℂ) :
    ∫ z in e ⁻¹' s, g z =
      (|LinearMap.det e.toLinearMap|⁻¹ : ℝ) • ∫ w in s, g (e.symm w) := by
  have hdet : LinearMap.det e.toLinearMap ≠ 0 := (LinearEquiv.isUnit_det' e).ne_zero
  -- the pushforward of Lebesgue measure under `e` is `|det e|⁻¹ • volume`
  have hmap : Measure.map (⇑e) volume
      = ENNReal.ofReal |LinearMap.det e.toLinearMap|⁻¹ •
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := volume) (f := e.toLinearMap) hdet
    rw [show Measure.map (⇑e) volume = Measure.map e.toLinearMap volume from rfl, h, abs_inv]
  -- `e` as a measurable equivalence, coinductively equal to `e`
  let φ : EuclideanSpace ℝ (Fin n) ≃ᵐ EuclideanSpace ℝ (Fin n) :=
    e.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have hφ : (φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) = e := rfl
  -- transport the set integral across the measurable equivalence `φ = e`
  have key := setIntegral_map_equiv (μ := volume) φ (fun y => g (e.symm y)) s
  rw [hφ] at key
  simp only [LinearEquiv.symm_apply_apply] at key
  -- `key : ∫ y in s, g (e.symm y) ∂map e volume = ∫ z in e ⁻¹' s, g z`
  rw [← key, hmap, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (abs_nonneg _))]

end Work.Poisson
