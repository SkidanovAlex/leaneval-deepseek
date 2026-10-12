import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `L²`-triangle bound `‖ψ + ψ'‖₂ ≤ ‖ψ‖₂ + ‖ψ'‖₂` in squared form

If `∫_s ψ² ≤ R²` and `∫_s ψ'² ≤ R²` with `0 ≤ R`, then
`√(∫_s (ψ + ψ')²) ≤ 2R`.

The proof is a crude two-variable bound, avoiding Cauchy–Schwarz entirely:
pointwise `(ψ + ψ')² ≤ 2ψ² + 2ψ'²`, hence
`∫_s (ψ + ψ')² ≤ 2∫_s ψ² + 2∫_s ψ'² ≤ 4R²`, and `√(4R²) = 2R` since `R ≥ 0`.
The `MemLp` hypotheses supply the integrability needed for `integral_mono`
(without them a non-integrable `ψ²` would have Bochner integral `0` by
convention and the hypotheses would be vacuous).
-/

namespace Work.BoseKinLoc.Kinetic

theorem sqrt_integralOn_add_sq_le {s : Set (EuclideanSpace ℝ (Fin 3))}
    {ψ ψ' : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hψ : MeasureTheory.MemLp ψ 2 (MeasureTheory.volume.restrict s))
    (hψ' : MeasureTheory.MemLp ψ' 2 (MeasureTheory.volume.restrict s))
    (hRψ : ∫ z in s, (ψ z) ^ 2 ≤ R ^ 2)
    (hRψ' : ∫ z in s, (ψ' z) ^ 2 ≤ R ^ 2) :
    Real.sqrt (∫ z in s, (ψ z + ψ' z) ^ 2) ≤ 2 * R := by
  have hA : MeasureTheory.Integrable (fun z => (ψ z) ^ 2) (MeasureTheory.volume.restrict s) :=
    hψ.integrable_sq
  have hB : MeasureTheory.Integrable (fun z => (ψ' z) ^ 2) (MeasureTheory.volume.restrict s) :=
    hψ'.integrable_sq
  have hC : MeasureTheory.Integrable (fun z => (ψ z + ψ' z) ^ 2)
      (MeasureTheory.volume.restrict s) :=
    (hψ.add hψ').integrable_sq
  have hInt2 : MeasureTheory.Integrable (fun z => 2 * (ψ z) ^ 2 + 2 * (ψ' z) ^ 2)
      (MeasureTheory.volume.restrict s) := (hA.const_mul 2).add (hB.const_mul 2)
  -- Pointwise two-variable bound: `(a + b)² = 2a² + 2b² - (a - b)² ≤ 2a² + 2b²`.
  have hpoint : ∀ z, (ψ z + ψ' z) ^ 2 ≤ 2 * (ψ z) ^ 2 + 2 * (ψ' z) ^ 2 := by
    intro z
    nlinarith [sq_nonneg (ψ z), sq_nonneg (ψ' z), sq_nonneg (ψ z - ψ' z)]
  have h1 : ∫ z in s, (ψ z + ψ' z) ^ 2 ≤ ∫ z in s, (2 * (ψ z) ^ 2 + 2 * (ψ' z) ^ 2) :=
    MeasureTheory.integral_mono hC hInt2 hpoint
  have h2 : ∫ z in s, (2 * (ψ z) ^ 2 + 2 * (ψ' z) ^ 2)
      = 2 * (∫ z in s, (ψ z) ^ 2) + 2 * (∫ z in s, (ψ' z) ^ 2) := by
    rw [MeasureTheory.integral_add (hA.const_mul 2) (hB.const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have h3 : ∫ z in s, (ψ z + ψ' z) ^ 2 ≤ 4 * R ^ 2 := by
    calc ∫ z in s, (ψ z + ψ' z) ^ 2 ≤ ∫ z in s, (2 * (ψ z) ^ 2 + 2 * (ψ' z) ^ 2) := h1
      _ = 2 * (∫ z in s, (ψ z) ^ 2) + 2 * (∫ z in s, (ψ' z) ^ 2) := h2
      _ ≤ 2 * R ^ 2 + 2 * R ^ 2 := by linarith
      _ = 4 * R ^ 2 := by ring
  have h4 : Real.sqrt (4 * R ^ 2) = 2 * R := by
    have hsq : (4 : ℝ) * R ^ 2 = (2 * R) ^ 2 := by ring
    rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith)]
  calc Real.sqrt (∫ z in s, (ψ z + ψ' z) ^ 2) ≤ Real.sqrt (4 * R ^ 2) := Real.sqrt_le_sqrt h3
    _ = 2 * R := h4

end Work.BoseKinLoc.Kinetic
