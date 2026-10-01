import Mathlib
import Submission.Work.ZeroDensity.Ingham.Defs
import Submission.Work.ZeroDensity.Ingham.zetaDetectorDefs
import Submission.Work.ZeroDensity.Ingham.windowIntegralHolder

namespace Work.ZeroDensity.Ingham.zetaDetectorBig

theorem perZeroBound (K : ℕ) (z : ℂ) (L Cg δ : ℝ) (hL : 0 ≤ L) (hCg : 0 < Cg) (hδ : 0 < δ)
    (hgam : ∀ v : ℝ, ‖Complex.Gamma (((1 / 2 : ℝ) - z.re : ℝ) + (v : ℝ) * Complex.I)‖ ≤ Cg / δ)
    (hf : Continuous fun v : ℝ => ‖riemannZeta ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖)
    (hg : Continuous fun v : ℝ => ‖Work.ZeroDensity.Ingham.MK K ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖)
    (hw : Continuous fun v : ℝ => ‖Complex.Gamma (((1 / 2 : ℝ) - z.re : ℝ) + (v : ℝ) * Complex.I)‖) :
    (∫ v in (-L)..L, Work.ZeroDensity.Ingham.critIntegrand K z v)
      ≤ (Cg / δ) * (2 * L) ^ ((1 : ℝ) / 4) *
          (∫ v in (-L)..L, ‖riemannZeta ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ ^ 4) ^ ((1 : ℝ) / 4) *
          (∫ v in (-L)..L, ‖Work.ZeroDensity.Ingham.MK K ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ ^ 2) ^ ((1 : ℝ) / 2) := by
  have hAB : (-L) ≤ L := by linarith
  have hWpos : (0 : ℝ) < Cg / δ := div_pos hCg hδ
  have hWnn : (0 : ℝ) ≤ Cg / δ := le_of_lt hWpos
  have h2L : (0 : ℝ) ≤ 2 * L := by linarith
  -- Hölder with the weight function `‖Γ‖`, bounded by `Cg/δ`
  have hholder := Work.ZeroDensity.Ingham.windowIntegralHolder
    (f := fun v : ℝ => ‖riemannZeta ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖)
    (g := fun v : ℝ => ‖Work.ZeroDensity.Ingham.MK K ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖)
    (w := fun v : ℝ => ‖Complex.Gamma (((1 / 2 : ℝ) - z.re : ℝ) + (v : ℝ) * Complex.I)‖)
    (A := -L) (B := L) (W := Cg / δ)
    hAB hWnn hf hg hw (fun v => norm_nonneg _) (fun v => norm_nonneg _) (fun v => norm_nonneg _)
    (fun v => hgam v)
  -- the weight has integral at most `(Cg/δ) · (2L)`
  have hIntI : (∫ v in (-L)..L, ‖Complex.Gamma (((1 / 2 : ℝ) - z.re : ℝ) + (v : ℝ) * Complex.I)‖)
      ≤ (Cg / δ) * (2 * L) := by
    have h := intervalIntegral.integral_mono (μ := MeasureTheory.volume) hAB
      (hw.intervalIntegrable (μ := MeasureTheory.volume) (-L) L)
      (intervalIntegrable_const (μ := MeasureTheory.volume) (c := Cg / δ)) (fun v => hgam v)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    calc (∫ v in (-L)..L, ‖Complex.Gamma (((1 / 2 : ℝ) - z.re : ℝ) + (v : ℝ) * Complex.I)‖)
        ≤ (L - (-L)) * (Cg / δ) := h
      _ = (Cg / δ) * (2 * L) := by ring
  have hInn : 0 ≤ (∫ v in (-L)..L, ‖Complex.Gamma (((1 / 2 : ℝ) - z.re : ℝ) + (v : ℝ) * Complex.I)‖) :=
    intervalIntegral.integral_nonneg_of_forall hAB (fun v => norm_nonneg _)
  have hIpow : (∫ v in (-L)..L, ‖Complex.Gamma (((1 / 2 : ℝ) - z.re : ℝ) + (v : ℝ) * Complex.I)‖) ^ ((1 : ℝ) / 4)
      ≤ (Cg / δ) ^ ((1 : ℝ) / 4) * (2 * L) ^ ((1 : ℝ) / 4) := by
    calc (∫ v in (-L)..L, ‖Complex.Gamma (((1 / 2 : ℝ) - z.re : ℝ) + (v : ℝ) * Complex.I)‖) ^ ((1 : ℝ) / 4)
        ≤ ((Cg / δ) * (2 * L)) ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow hInn hIntI (by norm_num)
      _ = (Cg / δ) ^ ((1 : ℝ) / 4) * (2 * L) ^ ((1 : ℝ) / 4) := Real.mul_rpow hWnn h2L
  have hP4 : 0 ≤ (∫ v in (-L)..L, ‖riemannZeta ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ ^ 4) :=
    intervalIntegral.integral_nonneg_of_forall hAB (fun v => pow_nonneg (norm_nonneg _) 4)
  have hQ2 : 0 ≤ (∫ v in (-L)..L, ‖Work.ZeroDensity.Ingham.MK K ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ ^ 2) :=
    intervalIntegral.integral_nonneg_of_forall hAB (fun v => pow_nonneg (norm_nonneg _) 2)
  have hA : 0 ≤ (Cg / δ) ^ ((3 : ℝ) / 4) *
      (∫ v in (-L)..L, ‖riemannZeta ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ ^ 4) ^ ((1 : ℝ) / 4) :=
    mul_nonneg (Real.rpow_nonneg hWnn _) (Real.rpow_nonneg hP4 _)
  have hB : 0 ≤ (∫ v in (-L)..L, ‖Work.ZeroDensity.Ingham.MK K ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ ^ 2) ^ ((1 : ℝ) / 2) :=
    Real.rpow_nonneg hQ2 _
  have hW3 : (Cg / δ) ^ ((3 : ℝ) / 4) * (Cg / δ) ^ ((1 : ℝ) / 4) = Cg / δ := by
    rw [← Real.rpow_add hWpos, show (3 : ℝ) / 4 + 1 / 4 = 1 by norm_num, Real.rpow_one]
  have hstep : (Cg / δ) ^ ((3 : ℝ) / 4) *
        (∫ v in (-L)..L, ‖riemannZeta ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ ^ 4) ^ ((1 : ℝ) / 4) *
        (∫ v in (-L)..L, ‖Complex.Gamma (((1 / 2 : ℝ) - z.re : ℝ) + (v : ℝ) * Complex.I)‖) ^ ((1 : ℝ) / 4) *
        (∫ v in (-L)..L, ‖Work.ZeroDensity.Ingham.MK K ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ ^ 2) ^ ((1 : ℝ) / 2)
      ≤ (Cg / δ) * (2 * L) ^ ((1 : ℝ) / 4) *
        (∫ v in (-L)..L, ‖riemannZeta ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ ^ 4) ^ ((1 : ℝ) / 4) *
        (∫ v in (-L)..L, ‖Work.ZeroDensity.Ingham.MK K ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ ^ 2) ^ ((1 : ℝ) / 2) := by
    have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hIpow hA) hB
    refine h1.trans (le_of_eq ?_)
    calc (Cg / δ) ^ ((3 : ℝ) / 4) *
          (∫ v in (-L)..L, ‖riemannZeta ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ ^ 4) ^ ((1 : ℝ) / 4) *
          ((Cg / δ) ^ ((1 : ℝ) / 4) * (2 * L) ^ ((1 : ℝ) / 4)) *
          (∫ v in (-L)..L, ‖Work.ZeroDensity.Ingham.MK K ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ ^ 2) ^ ((1 : ℝ) / 2)
        = ((Cg / δ) ^ ((3 : ℝ) / 4) * (Cg / δ) ^ ((1 : ℝ) / 4)) * (2 * L) ^ ((1 : ℝ) / 4) *
          (∫ v in (-L)..L, ‖riemannZeta ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ ^ 4) ^ ((1 : ℝ) / 4) *
          (∫ v in (-L)..L, ‖Work.ZeroDensity.Ingham.MK K ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ ^ 2) ^ ((1 : ℝ) / 2) := by ring
      _ = (Cg / δ) * (2 * L) ^ ((1 : ℝ) / 4) *
          (∫ v in (-L)..L, ‖riemannZeta ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ ^ 4) ^ ((1 : ℝ) / 4) *
          (∫ v in (-L)..L, ‖Work.ZeroDensity.Ingham.MK K ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ ^ 2) ^ ((1 : ℝ) / 2) := by rw [hW3]
  calc (∫ v in (-L)..L, Work.ZeroDensity.Ingham.critIntegrand K z v)
      = ∫ v in (-L)..L, ‖riemannZeta ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ *
          ‖Work.ZeroDensity.Ingham.MK K ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ *
          ‖Complex.Gamma (((1 / 2 : ℝ) - z.re : ℝ) + (v : ℝ) * Complex.I)‖ := by
        apply intervalIntegral.integral_congr; intro v _
        simp only [Work.ZeroDensity.Ingham.critIntegrand]
    _ ≤ (Cg / δ) ^ ((3 : ℝ) / 4) *
        (∫ v in (-L)..L, ‖riemannZeta ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ ^ 4) ^ ((1 : ℝ) / 4) *
        (∫ v in (-L)..L, ‖Complex.Gamma (((1 / 2 : ℝ) - z.re : ℝ) + (v : ℝ) * Complex.I)‖) ^ ((1 : ℝ) / 4) *
        (∫ v in (-L)..L, ‖Work.ZeroDensity.Ingham.MK K ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ ^ 2) ^ ((1 : ℝ) / 2) := hholder
    _ ≤ (Cg / δ) * (2 * L) ^ ((1 : ℝ) / 4) *
        (∫ v in (-L)..L, ‖riemannZeta ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ ^ 4) ^ ((1 : ℝ) / 4) *
        (∫ v in (-L)..L, ‖Work.ZeroDensity.Ingham.MK K ((1 / 2 : ℂ) + (z.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ ^ 2) ^ ((1 : ℝ) / 2) := hstep

end Work.ZeroDensity.Ingham.zetaDetectorBig
