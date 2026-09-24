import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Commons.Analysis.Integration

open MeasureTheory
open scoped Interval

/-- A real quadratic expression `A + 2*t*B + t^2*C` which is nonnegative for every real `t`,
with `0 ≤ C`, satisfies `B^2 ≤ A*C`. -/
theorem sq_le_mul_of_forall_quadratic_nonneg {A B C : ℝ} (hC : 0 ≤ C)
    (h : ∀ t : ℝ, 0 ≤ A + 2 * t * B + t ^ 2 * C) : B ^ 2 ≤ A * C := by
  rcases lt_or_eq_of_le hC with hC | hC0
  · -- `C > 0`: evaluate at the vertex `t = -B/C`.
    have ht := h (-(B / C))
    have hkey : 0 ≤ A - B ^ 2 / C := by
      have heq : A + 2 * (-(B / C)) * B + (-(B / C)) ^ 2 * C = A - B ^ 2 / C := by
        field_simp; ring
      linarith [ht, heq]
    have hmul : 0 ≤ C * (A - B ^ 2 / C) := mul_nonneg hC.le hkey
    have hsub : 0 ≤ C * A - B ^ 2 := by
      have heq : C * (A - B ^ 2 / C) = C * A - B ^ 2 := by
        rw [mul_sub, mul_div_cancel₀ _ hC.ne']
      linarith [hmul, heq]
    linarith [hsub]
  · -- `C = 0`: the expression is affine and bounded below only if `B = 0`.
    rw [← hC0] at h ⊢
    rw [mul_zero]
    have hB : B = 0 := by
      by_contra hB
      have ht := h (-(A + 1) / (2 * B))
      have heq : A + 2 * (-(A + 1) / (2 * B)) * B + (-(A + 1) / (2 * B)) ^ 2 * 0 = -1 := by
        field_simp; ring
      linarith [ht, heq]
    rw [hB]; norm_num

/-- Cauchy–Schwarz for the integral of two real functions with respect to an arbitrary measure:
`(∫ u*v)^2 ≤ (∫ u^2) * (∫ v^2)`. -/
theorem integral_mul_sq_le_of_integrable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {u v : α → ℝ}
    (h1 : Integrable (fun x => u x * v x) μ)
    (h2 : Integrable (fun x => u x ^ 2) μ)
    (h3 : Integrable (fun x => v x ^ 2) μ) :
    (∫ x, u x * v x ∂μ) ^ 2 ≤ (∫ x, u x ^ 2 ∂μ) * (∫ x, v x ^ 2 ∂μ) := by
  have hC : 0 ≤ ∫ x, v x ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg (v x))
  refine sq_le_mul_of_forall_quadratic_nonneg hC ?_
  intro t
  have hA : Integrable (fun x => u x ^ 2 + (2 * t) * (u x * v x)) μ :=
    h2.add (h1.const_mul (2 * t))
  have hB : Integrable (fun x => t ^ 2 * (v x ^ 2)) μ := h3.const_mul (t ^ 2)
  have hnonneg : 0 ≤ ∫ x, (u x ^ 2 + (2 * t) * (u x * v x) + t ^ 2 * (v x ^ 2)) ∂μ := by
    apply integral_nonneg
    intro x
    show (0 : ℝ) ≤ u x ^ 2 + (2 * t) * (u x * v x) + t ^ 2 * (v x ^ 2)
    rw [show u x ^ 2 + (2 * t) * (u x * v x) + t ^ 2 * (v x ^ 2) = (u x + t * v x) ^ 2 by
      ring]
    exact sq_nonneg _
  have hexp : ∫ x, (u x ^ 2 + (2 * t) * (u x * v x) + t ^ 2 * (v x ^ 2)) ∂μ
      = (∫ x, u x ^ 2 ∂μ) + 2 * t * (∫ x, u x * v x ∂μ) + t ^ 2 * (∫ x, v x ^ 2 ∂μ) := by
    rw [integral_add (f := fun x => u x ^ 2 + (2 * t) * (u x * v x))
          (g := fun x => t ^ 2 * (v x ^ 2)) hA hB,
        integral_add (f := fun x => u x ^ 2) (g := fun x => (2 * t) * (u x * v x)) h2
          (h1.const_mul (2 * t)),
        integral_const_mul, integral_const_mul]
  rw [← hexp]
  exact hnonneg

/-- Weighted Cauchy–Schwarz on `[0,1]`: for nonnegative `f, g`,
`(∫ f*g)^2 ≤ (∫ f) * (∫ f*g^2)`. -/
theorem integral_mul_sq_le {f g : ℝ → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (h1 : IntervalIntegrable (fun x => f x * g x) volume (0:ℝ) 1)
    (h2 : IntervalIntegrable (fun x => f x * g x ^ 2) volume (0:ℝ) 1)
    (h3 : IntervalIntegrable f volume (0:ℝ) 1) :
    (∫ x in (0:ℝ)..1, f x * g x) ^ 2
      ≤ (∫ x in (0:ℝ)..1, f x) * (∫ x in (0:ℝ)..1, f x * g x ^ 2) := by
  have hkey : ∀ h : ℝ → ℝ, ∫ x in (0:ℝ)..1, h x = ∫ x, h x ∂(volume.restrict (Ι (0:ℝ) 1)) := by
    intro h
    rw [intervalIntegral.integral_of_le zero_le_one, Set.uIoc_of_le zero_le_one]
  rw [hkey (fun x => f x * g x), hkey (fun x => f x), hkey (fun x => f x * g x ^ 2)]
  have hu2 : Integrable (fun x => Real.sqrt (f x) ^ 2) (volume.restrict (Ι (0:ℝ) 1)) :=
    (h3.def').congr (Filter.Eventually.of_forall (fun x => (Real.sq_sqrt (hf x)).symm))
  have huv : Integrable (fun x => Real.sqrt (f x) * (Real.sqrt (f x) * g x))
      (volume.restrict (Ι (0:ℝ) 1)) :=
    (h1.def').congr (Filter.Eventually.of_forall (fun x => by
      dsimp only
      rw [← mul_assoc, Real.mul_self_sqrt (hf x)]))
  have hv2 : Integrable (fun x => (Real.sqrt (f x) * g x) ^ 2)
      (volume.restrict (Ι (0:ℝ) 1)) :=
    (h2.def').congr (Filter.Eventually.of_forall (fun x => by
      dsimp only
      rw [mul_pow, Real.sq_sqrt (hf x)]))
  have hcs := integral_mul_sq_le_of_integrable huv hu2 hv2
  have e1 : ∫ x, Real.sqrt (f x) * (Real.sqrt (f x) * g x)
        ∂(volume.restrict (Ι (0:ℝ) 1))
      = ∫ x, f x * g x ∂(volume.restrict (Ι (0:ℝ) 1)) :=
    integral_congr_ae (Filter.Eventually.of_forall (fun x => by
      dsimp only
      rw [← mul_assoc, Real.mul_self_sqrt (hf x)]))
  have e2 : ∫ x, Real.sqrt (f x) ^ 2 ∂(volume.restrict (Ι (0:ℝ) 1))
      = ∫ x, f x ∂(volume.restrict (Ι (0:ℝ) 1)) :=
    integral_congr_ae (Filter.Eventually.of_forall (fun x => (Real.sq_sqrt (hf x))))
  have e3 : ∫ x, (Real.sqrt (f x) * g x) ^ 2 ∂(volume.restrict (Ι (0:ℝ) 1))
      = ∫ x, f x * g x ^ 2 ∂(volume.restrict (Ι (0:ℝ) 1)) :=
    integral_congr_ae (Filter.Eventually.of_forall (fun x => by
      dsimp only
      rw [mul_pow, Real.sq_sqrt (hf x)]))
  rw [e1, e2, e3] at hcs
  exact hcs

end Commons.Analysis.Integration