import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-- **The `L²` Cauchy–Schwarz inequality for the Bochner integral of a product.**
For `f g : α → ℂ` in `L²(μ)`, `‖∫ x, f x * g x ∂μ‖ ^ 2 ≤ (∫ x, ‖f x‖ ^ 2 ∂μ) * (∫ x, ‖g x‖ ^ 2 ∂μ)`.
Both `MemLp` hypotheses make the three integrals honest (no junk-`0`), so this is the classical
inequality; it is the real-valued companion of Mathlib's
`MeasureTheory.integral_mul_norm_le_Lp_mul_Lq` at `p = q = 2`.
⚠ the file must NOT import `Submission.Work.BoseBoxFock.slotSum_sectorPointwise` (a `update_pairCoord` clash). -/
theorem norm_integral_mul_sq_le {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    {f g : α → ℂ} (hf : MeasureTheory.MemLp f 2 μ) (hg : MeasureTheory.MemLp g 2 μ) :
    ‖∫ x, f x * g x ∂μ‖ ^ 2
      ≤ (∫ x, ‖f x‖ ^ 2 ∂μ) * (∫ x, ‖g x‖ ^ 2 ∂μ) := by
  -- Hölder's inequality at the conjugate exponents `p = q = 2` (valid for any measure `μ`).
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have hf' : MeasureTheory.MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hf
  have hg' : MeasureTheory.MemLp g (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hg
  have hH := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq (μ := μ) (f := f) (g := g) hpq hf' hg'
  -- `‖f x‖ ^ (2 : ℝ)` (the `rpow` form produced by Hölder) is `‖f x‖ ^ 2`.
  have hA : (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) = ∫ x, ‖f x‖ ^ 2 ∂μ :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by simp)
  have hB : (∫ x, ‖g x‖ ^ (2 : ℝ) ∂μ) = ∫ x, ‖g x‖ ^ 2 ∂μ :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by simp)
  have hnorm : ‖∫ x, f x * g x ∂μ‖ ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by
    calc ‖∫ x, f x * g x ∂μ‖ ≤ ∫ x, ‖f x * g x‖ ∂μ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ = ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by simp only [norm_mul]
  have hF : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := MeasureTheory.integral_nonneg fun x => sq_nonneg _
  have hG : 0 ≤ ∫ x, ‖g x‖ ^ 2 ∂μ := MeasureTheory.integral_nonneg fun x => sq_nonneg _
  have hchain : ‖∫ x, f x * g x ∂μ‖
      ≤ Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂μ) := by
    calc ‖∫ x, f x * g x ∂μ‖ ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂μ := hnorm
      _ ≤ (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)
            * (∫ x, ‖g x‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := hH
      _ = Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂μ) := by
          rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, hA, hB]
  -- Square the two-sided bound and use `(√a)² = a` for the two nonnegative integrals.
  calc ‖∫ x, f x * g x ∂μ‖ ^ 2
      ≤ (Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂μ)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hchain 2
    _ = (∫ x, ‖f x‖ ^ 2 ∂μ) * (∫ x, ‖g x‖ ^ 2 ∂μ) := by
        rw [mul_pow, Real.sq_sqrt hF, Real.sq_sqrt hG]

end Work.BoseBoxFock
