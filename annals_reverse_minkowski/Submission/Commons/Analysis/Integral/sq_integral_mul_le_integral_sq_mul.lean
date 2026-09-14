import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

namespace Commons.Analysis.Integral

open MeasureTheory Set Filter
open scoped Real Topology

/-- Cauchy--Schwarz for weighted integrals: if `w ≥ 0` and `a ^ 2 * w`, `b ^ 2 * w` are
integrable, then `(∫ a b w) ^ 2 ≤ (∫ a ^ 2 w) * (∫ b ^ 2 w)`. -/
theorem sq_integral_mul_le_integral_sq_mul (a b w : ℝ → ℝ) (hw : ∀ x, 0 ≤ w x)
    (ha : Integrable fun x => a x ^ 2 * w x) (hb : Integrable fun x => b x ^ 2 * w x) :
    (∫ x, a x * b x * w x) ^ 2 ≤ (∫ x, a x ^ 2 * w x) * (∫ x, b x ^ 2 * w x) := by
  by_cases hCint : Integrable fun x => a x * b x * w x
  · set A : ℝ := ∫ x, a x ^ 2 * w x with hAdef
    set B : ℝ := ∫ x, b x ^ 2 * w x with hBdef
    set C : ℝ := ∫ x, a x * b x * w x with hCdef
    have hA0 : 0 ≤ A := by
      rw [hAdef]
      exact integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hw x))
    have hB0 : 0 ≤ B := by
      rw [hBdef]
      exact integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hw x))
    have hquad : ∀ t : ℝ, 0 ≤ A + 2 * t * C + t ^ 2 * B := by
      intro t
      have hg : Integrable fun x => (2 * t) * (a x * b x * w x) := hCint.const_mul (2 * t)
      have hh : Integrable fun x => t ^ 2 * (b x ^ 2 * w x) := hb.const_mul (t ^ 2)
      have hcongr : (fun x => (a x + t * b x) ^ 2 * w x)
          =ᵐ[volume] fun x => a x ^ 2 * w x + (2 * t) * (a x * b x * w x)
            + t ^ 2 * (b x ^ 2 * w x) := by
        filter_upwards with x
        ring
      have hval : (∫ x, (a x + t * b x) ^ 2 * w x) = A + 2 * t * C + t ^ 2 * B := by
        rw [integral_congr_ae hcongr]
        rw [show (∫ x, a x ^ 2 * w x + (2 * t) * (a x * b x * w x) + t ^ 2 * (b x ^ 2 * w x))
            = ∫ x, ((fun y => a y ^ 2 * w y) + (fun y => (2 * t) * (a y * b y * w y))) x
                + (fun y => t ^ 2 * (b y ^ 2 * w y)) x from rfl]
        rw [integral_add (ha.add hg) hh, integral_add' ha hg]
        rw [integral_const_mul, integral_const_mul, ← hAdef, ← hCdef, ← hBdef]
      have hnonneg : 0 ≤ ∫ x, (a x + t * b x) ^ 2 * w x :=
        integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hw x))
      rw [hval] at hnonneg
      exact hnonneg
    have hmain : C ^ 2 ≤ A * B := by
      by_cases hBzero : B = 0
      · have hC0 : C = 0 := by
          by_contra hCne
          have h2C : (2 : ℝ) * C ≠ 0 := mul_ne_zero (by norm_num) hCne
          have h := hquad (-(A + 1) / (2 * C))
          have heq : A + 2 * (-(A + 1) / (2 * C)) * C + (-(A + 1) / (2 * C)) ^ 2 * B = -1 := by
            rw [hBzero]
            field_simp
            ring
          linarith [h, heq]
        rw [hC0, hBzero]
        norm_num
      · have hBpos : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hBzero)
        have hBne : B ≠ 0 := ne_of_gt hBpos
        have h := hquad (-(C / B))
        have heq : A + 2 * (-(C / B)) * C + (-(C / B)) ^ 2 * B = A - C ^ 2 / B := by
          field_simp
          ring
        have hstep : 0 ≤ A - C ^ 2 / B := by linarith [h, heq]
        have h3 : C ^ 2 / B ≤ A := by linarith [hstep]
        exact (div_le_iff₀ hBpos).mp h3
    exact hmain
  · rw [integral_undef hCint]
    have hA0 : 0 ≤ ∫ x, a x ^ 2 * w x :=
      integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hw x))
    have hB0 : 0 ≤ ∫ x, b x ^ 2 * w x :=
      integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hw x))
    have hmul : 0 ≤ (∫ x, a x ^ 2 * w x) * (∫ x, b x ^ 2 * w x) := mul_nonneg hA0 hB0
    simpa using hmul

end Commons.Analysis.Integral