import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

namespace Commons.MeasureTheory.Function

open _root_.MeasureTheory ENNReal

/-- Hölder's inequality for the extended `Lᵖ` seminorm of a product of complex-valued functions:
if `p⁻¹ = q⁻¹ + r⁻¹` then `‖f * g‖_{Lᵖ} ≤ ‖f‖_{Lq} ‖g‖_{Lʳ}`.

This is the complex-valued (i.e. `ENNReal`-valued norm) specialization of Mathlib's
`MeasureTheory.eLpNorm_smul_le_mul_eLpNorm`. -/
theorem eLpNorm_mul_le_eLpNorm_mul_eLpNorm_complex {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {p q r : ENNReal} (hpq : p⁻¹ = q⁻¹ + r⁻¹)
    {f g : α → ℂ} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    MeasureTheory.eLpNorm (fun x => f x * g x) p μ
      ≤ MeasureTheory.eLpNorm f q μ * MeasureTheory.eLpNorm g r μ := by
  -- `HolderTriple q r p` is the reindexed form of the hypothesis `p⁻¹ = q⁻¹ + r⁻¹`.
  have h := MeasureTheory.eLpNorm_smul_le_mul_eLpNorm (p := q) (q := r) (r := p)
    (hpqr := ⟨hpq.symm⟩) (f := g) (φ := f) hf.aestronglyMeasurable hg.aestronglyMeasurable
  have hfun : (f • g) = fun x => f x * g x := by
    ext x; simp [smul_eq_mul]
  rw [hfun] at h
  exact h

end Commons.MeasureTheory.Function
