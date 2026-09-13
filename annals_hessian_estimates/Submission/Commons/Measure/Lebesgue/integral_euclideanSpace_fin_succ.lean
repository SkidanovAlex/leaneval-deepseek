import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

namespace Commons.Measure.Lebesgue

open MeasureTheory in
/-- Integration over `EuclideanSpace ℝ (Fin (n + 1))` can be performed by first integrating over
the last `n` coordinates and then over the coordinate `0`, when the function is written through the
identification `ℝ^{n+1} ≃ ℝ × ℝ^n`. -/
theorem integral_euclideanSpace_fin_succ {n : ℕ} (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hF : Integrable F volume) :
    ∫ x, F x = ∫ t : ℝ, ∫ w : EuclideanSpace ℝ (Fin n),
      F (WithLp.toLp 2 (Fin.cons t (fun j => w.ofLp j))) := by
  -- Transfer the integral from `EuclideanSpace ℝ (Fin (n+1))` to functions `Fin (n+1) → ℝ`.
  let φ : (Fin (n + 1) → ℝ) ≃ᵐ EuclideanSpace ℝ (Fin (n + 1)) :=
    MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)
  have hφ : MeasurePreserving (⇑φ) volume volume := PiLp.volume_preserving_toLp (Fin (n + 1))
  rw [← hφ.integral_comp' F]
  have h1 : Integrable (fun y : Fin (n + 1) → ℝ => F (φ y)) volume :=
    (hφ.integrable_comp hF.aestronglyMeasurable).mpr hF
  -- Split off the coordinate `0` of a function `Fin (n+1) → ℝ`.
  set E := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0 with hE
  have hE1 : MeasurePreserving (⇑E) volume volume := volume_preserving_piFinSuccAbove _ 0
  rw [← hE1.symm.integral_comp' (fun y : Fin (n + 1) → ℝ => F (φ y))]
  have hEsymm : ∀ p : ℝ × (Fin n → ℝ), E.symm p = Fin.cons p.1 p.2 := by
    intro p
    ext i
    simp [E, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.consEquiv_apply]
  have h2 : Integrable (fun p : ℝ × (Fin n → ℝ) => F (φ (Fin.cons p.1 p.2))) volume := by
    have hh : Integrable (fun p : ℝ × (Fin n → ℝ) => F (φ (E.symm p))) volume :=
      (hE1.symm.integrable_comp h1.aestronglyMeasurable).mpr h1
    simpa only [hEsymm] using hh
  simp only [hEsymm]
  -- Apply Fubini's theorem on the product `ℝ × (Fin n → ℝ)`.
  rw [Measure.volume_eq_prod ℝ (Fin n → ℝ), integral_prod _ h2]
  congr 1 with t
  -- Transfer the inner integral back to `EuclideanSpace ℝ (Fin n)`.
  let ψ : (Fin n → ℝ) ≃ᵐ EuclideanSpace ℝ (Fin n) :=
    MeasurableEquiv.toLp 2 (Fin n → ℝ)
  have hψ : MeasurePreserving (⇑ψ) volume volume := PiLp.volume_preserving_toLp (Fin n)
  rw [← hψ.symm.integral_comp' (fun g : Fin n → ℝ => F (φ (Fin.cons t g)))]
  rfl

end Commons.Measure.Lebesgue