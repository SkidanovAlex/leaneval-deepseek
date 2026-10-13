import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

/-- Pure algebra behind the diagonal Cauchy–Schwarz inequality: a quadratic
`t ↦ t ^ 2 * A + 2 * t * C + B` which is nonnegative everywhere and has `0 ≤ A` forces
`C ^ 2 ≤ A * B`.

Indeed, for `t = -C / A` (when `A > 0`) the identity
`A * (t ^ 2 * A + 2 * t * C + B) = A * B - C ^ 2` gives the claim, while if `A = 0` the
inequality at `t = -(B + 1) / (2 * C)` (when `C ≠ 0`) reads `0 ≤ -1`. -/
private lemma sq_le_mul_of_forall_quad_nonneg {A B C : ℝ} (hA : 0 ≤ A)
    (h : ∀ t : ℝ, 0 ≤ t ^ 2 * A + 2 * t * C + B) : C ^ 2 ≤ A * B := by
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · -- `A = 0`: the quadratic degenerates to a nonnegative affine function, so `C = 0`.
    have hAz : A = 0 := hA0.symm
    have hC : C = 0 := by
      by_contra hC
      have ht := h (-(B + 1) / (2 * C))
      rw [hAz] at ht
      have hsimp : 2 * (-(B + 1) / (2 * C)) * C = -(B + 1) := by field_simp
      rw [hsimp] at ht
      linarith
    rw [hC, hAz]
    norm_num
  · -- `A > 0`: evaluate at the vertex `t = -C / A` and multiply by `A`.
    have hq := h (-C / A)
    have hprod : 0 ≤ A * ((-C / A) ^ 2 * A + 2 * (-C / A) * C + B) :=
      mul_nonneg hApos.le hq
    have hval : A * ((-C / A) ^ 2 * A + 2 * (-C / A) * C + B) = A * B - C ^ 2 := by
      field_simp
      ring
    linarith

/-- Cauchy–Schwarz (Bunyakovsky) for the weighted integral: for a.e.-nonnegative `ρ` and
`f`, `g` with `f * f * ρ`, `g * g * ρ` and `f * g * ρ` integrable,
`(∫ f * g * ρ) ^ 2 ≤ (∫ f * f * ρ) * (∫ g * g * ρ)`.

The proof is the discriminant argument for the quadratic
`t ↦ ∫ (t * f + g) ^ 2 * ρ = t ^ 2 * ∫ f ^ 2 * ρ + 2 * t * ∫ f * g * ρ + ∫ g ^ 2 * ρ`,
which is nonnegative for every real `t` because `ρ ≥ 0` a.e.; `∫ f ^ 2 * ρ ≥ 0` is
immediate from the same a.e. nonnegativity. No measurability of `ρ` is needed. -/
theorem cs_diag {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {ρ f g : α → ℝ}
    (hρ : 0 ≤ᵐ[μ] ρ)
    (hf : MeasureTheory.Integrable (fun x => f x * f x * ρ x) μ)
    (hg : MeasureTheory.Integrable (fun x => g x * g x * ρ x) μ)
    (hfg : MeasureTheory.Integrable (fun x => f x * g x * ρ x) μ) :
    (∫ x, f x * g x * ρ x ∂μ) ^ 2 ≤
      (∫ x, f x * f x * ρ x ∂μ) * (∫ x, g x * g x * ρ x ∂μ) := by
  refine sq_le_mul_of_forall_quad_nonneg ?_ ?_
  · -- `0 ≤ ∫ f * f * ρ`.
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [hρ] with x hx
    exact mul_nonneg (mul_self_nonneg (f x)) hx
  · intro t
    -- the complete square expands into the three integrable pieces
    have key : (∫ x, (t * f x + g x) * (t * f x + g x) * ρ x ∂μ)
        = t ^ 2 * (∫ x, f x * f x * ρ x ∂μ) + 2 * t * (∫ x, f x * g x * ρ x ∂μ)
          + (∫ x, g x * g x * ρ x ∂μ) := by
      have hpt : (fun x => (t * f x + g x) * (t * f x + g x) * ρ x) =
          fun x => t ^ 2 * (f x * f x * ρ x) + (2 * t) * (f x * g x * ρ x)
            + (g x * g x * ρ x) := by
        funext x
        ring
      rw [hpt]
      have i1 : MeasureTheory.Integrable (fun x => t ^ 2 * (f x * f x * ρ x)) μ :=
        hf.const_mul (t ^ 2)
      have i2 : MeasureTheory.Integrable (fun x => (2 * t) * (f x * g x * ρ x)) μ :=
        hfg.const_mul (2 * t)
      have i12 : MeasureTheory.Integrable
          (fun x => t ^ 2 * (f x * f x * ρ x) + (2 * t) * (f x * g x * ρ x)) μ :=
        i1.add i2
      rw [MeasureTheory.integral_add i12 hg, MeasureTheory.integral_add i1 i2,
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    rw [← key]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [hρ] with x hx
    exact mul_nonneg (mul_self_nonneg _) hx

end Work.FTS.StrongEps.EpsE4Thr
