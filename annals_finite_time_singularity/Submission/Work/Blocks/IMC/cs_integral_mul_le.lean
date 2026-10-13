import Mathlib.MeasureTheory.Function.L2Space

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Blocks.IMC

theorem cs_integral_mul_le {α : Type*} [MeasurableSpace α] (mu : MeasureTheory.Measure α)
    {f g : α → ℝ} (hfm : MeasureTheory.AEStronglyMeasurable f mu)
    (hgm : MeasureTheory.AEStronglyMeasurable g mu)
    (hf : MeasureTheory.Integrable (fun x => f x ^ 2) mu)
    (hg : MeasureTheory.Integrable (fun x => g x ^ 2) mu) :
    |∫ x, f x * g x ∂mu| ≤ Real.sqrt (∫ x, f x ^ 2 ∂mu) * Real.sqrt (∫ x, g x ^ 2 ∂mu) := by
  -- Square-integrability of `f` and `g` (in the `MemLp` form required by Hölder).
  have hf2 : MeasureTheory.MemLp f 2 mu :=
    (MeasureTheory.memLp_two_iff_integrable_sq (μ := mu) hfm).mpr hf
  have hg2 : MeasureTheory.MemLp g 2 mu :=
    (MeasureTheory.memLp_two_iff_integrable_sq (μ := mu) hgm).mpr hg
  -- Drop the absolute value inside the integral.
  have h1 : |∫ x, f x * g x ∂mu| ≤ ∫ x, |f x| * |g x| ∂mu := by
    simpa only [Real.norm_eq_abs, abs_mul] using
      (MeasureTheory.norm_integral_le_integral_norm (μ := mu) (f := fun x => f x * g x))
  -- Hölder with conjugate exponents `p = q = 2`.
  have h2 : ∫ x, |f x| * |g x| ∂mu ≤
      (∫ x, |f x| ^ (2:ℝ) ∂mu) ^ (1/2:ℝ) * (∫ x, |g x| ^ (2:ℝ) ∂mu) ^ (1/2:ℝ) := by
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.integral_mul_norm_le_Lp_mul_Lq (μ := mu) (p := 2) (q := 2)
        (f := f) (g := g) (by norm_num [Real.holderConjugate_iff])
        (by simpa using hf2) (by simpa using hg2))
  -- `|f|^2 = f^2` and the real power `(·)^(1/2)` is the square root.
  have hA : (∫ x, |f x| ^ (2:ℝ) ∂mu) = ∫ x, f x ^ 2 ∂mu :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by simp [sq_abs]))
  have hB : (∫ x, |g x| ^ (2:ℝ) ∂mu) = ∫ x, g x ^ 2 ∂mu :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by simp [sq_abs]))
  calc |∫ x, f x * g x ∂mu| ≤ ∫ x, |f x| * |g x| ∂mu := h1
    _ ≤ (∫ x, |f x| ^ (2:ℝ) ∂mu) ^ (1/2:ℝ) * (∫ x, |g x| ^ (2:ℝ) ∂mu) ^ (1/2:ℝ) := h2
    _ = Real.sqrt (∫ x, f x ^ 2 ∂mu) * Real.sqrt (∫ x, g x ^ 2 ∂mu) := by
        rw [hA, hB, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]

end Work.Blocks.IMC
