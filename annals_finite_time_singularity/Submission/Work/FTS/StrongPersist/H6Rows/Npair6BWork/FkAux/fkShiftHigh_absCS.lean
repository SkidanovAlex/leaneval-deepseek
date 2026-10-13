import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Submission.Work.FTS.TransportS.TvUniform.integral_sqrt_mul_sqrt_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

/-- Pointwise Cauchy–Schwarz for the two weighted squares: if `ρ ≥ 0` then the modulus of the
pairing `g·(ρ·A·B)` equals `√(g²·ρ·A²)·√(ρ·B²)`. -/
theorem fkShiftHigh_sqrt_eq_abs {g : ℝ → ℝ} {A B ρ : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (hp : 0 ≤ ρ p.1 p.2) :
    ‖g p.1 * (ρ p.1 p.2 * A p.1 p.2 * B p.1 p.2)‖
      = Real.sqrt ((g p.1) ^ 2 * ρ p.1 p.2 * (A p.1 p.2) ^ 2)
        * Real.sqrt (ρ p.1 p.2 * (B p.1 p.2) ^ 2) := by
  have hFnn : 0 ≤ (g p.1) ^ 2 * ρ p.1 p.2 * (A p.1 p.2) ^ 2 :=
    mul_nonneg (mul_nonneg (sq_nonneg _) hp) (sq_nonneg _)
  have hGnn : 0 ≤ ρ p.1 p.2 * (B p.1 p.2) ^ 2 := mul_nonneg hp (sq_nonneg _)
  rw [Real.norm_eq_abs, ← Real.sqrt_mul hFnn (ρ p.1 p.2 * (B p.1 p.2) ^ 2),
    show (g p.1) ^ 2 * ρ p.1 p.2 * (A p.1 p.2) ^ 2 * (ρ p.1 p.2 * (B p.1 p.2) ^ 2)
        = (g p.1 * (ρ p.1 p.2 * A p.1 p.2 * B p.1 p.2)) ^ 2 from by ring,
    Real.sqrt_sq_eq_abs]

theorem fkShiftHigh_absCS {μ : MeasureTheory.Measure (ℝ × ℝ)} {g : ℝ → ℝ}
    {A B ρ : ℝ → ℝ → ℝ}
    (hρ : ∀ᵐ p ∂μ, 0 ≤ ρ p.1 p.2)
    (haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => g p.1 * (ρ p.1 p.2 * A p.1 p.2 * B p.1 p.2)) μ)
    (hF : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (g p.1) ^ 2 * ρ p.1 p.2 * (A p.1 p.2) ^ 2) μ)
    (hG : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ρ p.1 p.2 * (B p.1 p.2) ^ 2) μ) :
    MeasureTheory.Integrable
        (fun p : ℝ × ℝ => g p.1 * (ρ p.1 p.2 * A p.1 p.2 * B p.1 p.2)) μ ∧
      |∫ p, g p.1 * (ρ p.1 p.2 * A p.1 p.2 * B p.1 p.2) ∂μ|
        ≤ Real.sqrt (∫ p, (g p.1) ^ 2 * ρ p.1 p.2 * (A p.1 p.2) ^ 2 ∂μ)
          * Real.sqrt (∫ p, ρ p.1 p.2 * (B p.1 p.2) ^ 2 ∂μ) := by
  have hae : (fun p : ℝ × ℝ => ‖g p.1 * (ρ p.1 p.2 * A p.1 p.2 * B p.1 p.2)‖)
      =ᵐ[μ] (fun p : ℝ × ℝ => Real.sqrt ((g p.1) ^ 2 * ρ p.1 p.2 * (A p.1 p.2) ^ 2)
        * Real.sqrt (ρ p.1 p.2 * (B p.1 p.2) ^ 2)) :=
    hρ.mono fun p hp => fkShiftHigh_sqrt_eq_abs hp
  -- the dominating function `(F + G)/2`
  have hbound : (fun p : ℝ × ℝ => ‖g p.1 * (ρ p.1 p.2 * A p.1 p.2 * B p.1 p.2)‖)
      ≤ᵐ[μ] (fun p : ℝ × ℝ => ((g p.1) ^ 2 * ρ p.1 p.2 * (A p.1 p.2) ^ 2
        + ρ p.1 p.2 * (B p.1 p.2) ^ 2) / 2) := by
    filter_upwards [hae, hρ] with p hp hpρ
    rw [hp]
    have hFnn : 0 ≤ (g p.1) ^ 2 * ρ p.1 p.2 * (A p.1 p.2) ^ 2 :=
      mul_nonneg (mul_nonneg (sq_nonneg _) hpρ) (sq_nonneg _)
    have hGnn : 0 ≤ ρ p.1 p.2 * (B p.1 p.2) ^ 2 := mul_nonneg hpρ (sq_nonneg _)
    nlinarith [sq_nonneg (Real.sqrt ((g p.1) ^ 2 * ρ p.1 p.2 * (A p.1 p.2) ^ 2)
        - Real.sqrt (ρ p.1 p.2 * (B p.1 p.2) ^ 2)),
      Real.sq_sqrt hFnn, Real.sq_sqrt hGnn]
  have hInt : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => g p.1 * (ρ p.1 p.2 * A p.1 p.2 * B p.1 p.2)) μ :=
    MeasureTheory.Integrable.mono' ((hF.add hG).div_const 2) haesm hbound
  refine ⟨hInt, ?_⟩
  have hcongr : ∫ p, ‖g p.1 * (ρ p.1 p.2 * A p.1 p.2 * B p.1 p.2)‖ ∂μ
      = ∫ p, Real.sqrt ((g p.1) ^ 2 * ρ p.1 p.2 * (A p.1 p.2) ^ 2)
        * Real.sqrt (ρ p.1 p.2 * (B p.1 p.2) ^ 2) ∂μ :=
    MeasureTheory.integral_congr_ae hae
  have hFnn_ae : 0 ≤ᵐ[μ]
      (fun p : ℝ × ℝ => (g p.1) ^ 2 * ρ p.1 p.2 * (A p.1 p.2) ^ 2) :=
    hρ.mono fun p hp => mul_nonneg (mul_nonneg (sq_nonneg _) hp) (sq_nonneg _)
  have hGnn_ae : 0 ≤ᵐ[μ] (fun p : ℝ × ℝ => ρ p.1 p.2 * (B p.1 p.2) ^ 2) :=
    hρ.mono fun p hp => mul_nonneg hp (sq_nonneg _)
  calc |∫ p, g p.1 * (ρ p.1 p.2 * A p.1 p.2 * B p.1 p.2) ∂μ|
      = ‖∫ p, g p.1 * (ρ p.1 p.2 * A p.1 p.2 * B p.1 p.2) ∂μ‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ p, ‖g p.1 * (ρ p.1 p.2 * A p.1 p.2 * B p.1 p.2)‖ ∂μ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ p, Real.sqrt ((g p.1) ^ 2 * ρ p.1 p.2 * (A p.1 p.2) ^ 2)
          * Real.sqrt (ρ p.1 p.2 * (B p.1 p.2) ^ 2) ∂μ := hcongr
    _ ≤ Real.sqrt (∫ p, (g p.1) ^ 2 * ρ p.1 p.2 * (A p.1 p.2) ^ 2 ∂μ)
          * Real.sqrt (∫ p, ρ p.1 p.2 * (B p.1 p.2) ^ 2 ∂μ) :=
        Work.FTS.TransportS.TvUniform.integral_sqrt_mul_sqrt_le μ hFnn_ae hGnn_ae hF hG

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
