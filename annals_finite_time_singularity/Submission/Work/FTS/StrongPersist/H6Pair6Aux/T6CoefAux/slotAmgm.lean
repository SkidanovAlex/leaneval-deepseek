import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.mismatchAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux

open MeasureTheory

theorem slotAmgm {G X Y Z : ℝ → ℝ → ℝ} {A B : ℝ}
    (hXint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => G p.1 p.2 * X p.1 p.2 ^ 2)
      Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.pm)
    (hYZint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => G p.1 p.2 * Y p.1 p.2 ^ 2 * Z p.1 p.2 ^ 2)
      Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.pm)
    (hXv : (∫ p, G p.1 p.2 * X p.1 p.2 ^ 2
      ∂Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.pm) ≤ A)
    (hYZv : (∫ p, G p.1 p.2 * Y p.1 p.2 ^ 2 * Z p.1 p.2 ^ 2
      ∂Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.pm) ≤ B)
    (hA : 0 < A) (hB : 0 < B)
    (hGnn : ∀ᵐ p ∂Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.pm, 0 ≤ G p.1 p.2)
    (hFmeas : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => G p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2)
      Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.pm) :
    MeasureTheory.Integrable
        (fun p : ℝ × ℝ => G p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2)
        Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.pm ∧
      |∫ p, G p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2
        ∂Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.pm| ≤ Real.sqrt A * Real.sqrt B := by
  classical
  -- the pointwise AM–GM majorant of the product by `(G X² + G Y²Z²)/2`
  have hpt : ∀ᵐ p ∂pm,
      ‖G p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2‖
        ≤ (G p.1 p.2 * X p.1 p.2 ^ 2 + G p.1 p.2 * Y p.1 p.2 ^ 2 * Z p.1 p.2 ^ 2) / 2 := by
    filter_upwards [hGnn] with p hp
    have h := pt_le (G p.1 p.2) (X p.1 p.2) (Y p.1 p.2) (Z p.1 p.2) 1 hp (by norm_num)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hp]
    convert h using 1 <;> ring
  have hInt2 : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (G p.1 p.2 * X p.1 p.2 ^ 2
        + G p.1 p.2 * Y p.1 p.2 ^ 2 * Z p.1 p.2 ^ 2) / 2) pm :=
    (hXint.add hYZint).div_const 2
  have hIntF : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => G p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2) pm :=
    MeasureTheory.Integrable.mono' hInt2 hFmeas hpt
  refine ⟨hIntF, ?_⟩
  -- the optimized AM–GM, integrated
  have key : ∀ lam : ℝ, 0 < lam →
      ∫ p, |G p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2| ∂pm
        ≤ (lam * A + lam⁻¹ * B) / 2 := by
    intro lam hlam
    have hpt2 : ∀ᵐ p ∂pm,
        |G p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2|
          ≤ (lam * (G p.1 p.2 * X p.1 p.2 ^ 2)
              + lam⁻¹ * (G p.1 p.2 * Y p.1 p.2 ^ 2 * Z p.1 p.2 ^ 2)) / 2 := by
      filter_upwards [hGnn] with p hp
      have h := pt_le (G p.1 p.2) (X p.1 p.2) (Y p.1 p.2) (Z p.1 p.2) lam hp hlam
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hp]
      convert h using 1 <;> ring
    have hInt3 : MeasureTheory.Integrable
        (fun p : ℝ × ℝ => (lam * (G p.1 p.2 * X p.1 p.2 ^ 2)
          + lam⁻¹ * (G p.1 p.2 * Y p.1 p.2 ^ 2 * Z p.1 p.2 ^ 2)) / 2) pm :=
      ((hXint.const_mul lam).add (hYZint.const_mul lam⁻¹)).div_const 2
    have hmono := MeasureTheory.integral_mono_ae hIntF.abs hInt3 hpt2
    have hval : ∫ p, (lam * (G p.1 p.2 * X p.1 p.2 ^ 2)
          + lam⁻¹ * (G p.1 p.2 * Y p.1 p.2 ^ 2 * Z p.1 p.2 ^ 2)) / 2 ∂pm
        = (lam * (∫ p, G p.1 p.2 * X p.1 p.2 ^ 2 ∂pm)
            + lam⁻¹ * (∫ p, G p.1 p.2 * Y p.1 p.2 ^ 2 * Z p.1 p.2 ^ 2 ∂pm)) / 2 := by
      rw [MeasureTheory.integral_div,
        MeasureTheory.integral_add (hXint.const_mul lam) (hYZint.const_mul lam⁻¹),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    rw [hval] at hmono
    have h1 : lam * (∫ p, G p.1 p.2 * X p.1 p.2 ^ 2 ∂pm) ≤ lam * A :=
      mul_le_mul_of_nonneg_left hXv hlam.le
    have h2 : lam⁻¹ * (∫ p, G p.1 p.2 * Y p.1 p.2 ^ 2 * Z p.1 p.2 ^ 2 ∂pm) ≤ lam⁻¹ * B :=
      mul_le_mul_of_nonneg_left hYZv (inv_nonneg.mpr hlam.le)
    linarith
  have hlam : 0 < Real.sqrt B / Real.sqrt A :=
    div_pos (Real.sqrt_pos.mpr hB) (Real.sqrt_pos.mpr hA)
  have hk := key (Real.sqrt B / Real.sqrt A) hlam
  have htarget : (Real.sqrt B / Real.sqrt A * A + (Real.sqrt B / Real.sqrt A)⁻¹ * B) / 2
      = Real.sqrt A * Real.sqrt B := by
    rw [inv_div]
    field_simp
    rw [Real.sq_sqrt hA.le, Real.sq_sqrt hB.le]
    ring
  rw [htarget] at hk
  calc |∫ p, G p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2 ∂pm|
      ≤ ∫ p, |G p.1 p.2 * X p.1 p.2 * Y p.1 p.2 * Z p.1 p.2| ∂pm :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ Real.sqrt A * Real.sqrt B := hk

end Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux
