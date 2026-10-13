import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.cc

open MeasureTheory

/-- Real-algebra core of the Cauchy–Schwarz (Bunyakovsky) inequality.

If the quadratic polynomial `t ↦ A + 2*C*t + B*t^2` is nonnegative for every real `t` and
`B ≥ 0`, then `C^2 ≤ A*B`.  The proof is the classical discriminant argument, carried out
without any irreducibility assumptions: in the degenerate case `B = 0` the linear function
`t ↦ A + 2*C*t` can only be nonnegative on all of `ℝ` when `C = 0` (evaluate at
`t = -(A+1)/(2*C)`); otherwise it suffices to evaluate at `t = -C/B`. -/
theorem cs_quad {A B C : ℝ} (h : ∀ t : ℝ, 0 ≤ A + 2 * C * t + B * t ^ 2) (hB : 0 ≤ B) :
    C ^ 2 ≤ A * B := by
  by_cases hB0 : B = 0
  · have hC : C = 0 := by
      by_contra hC0
      have h2C : (2 : ℝ) * C ≠ 0 := mul_ne_zero (by norm_num) hC0
      have hk := h (-(A + 1) / (2 * C))
      have hval : A + 2 * C * (-(A + 1) / (2 * C)) + B * (-(A + 1) / (2 * C)) ^ 2 = -1 := by
        rw [hB0]
        field_simp
        ring
      rw [hval] at hk
      norm_num at hk
    rw [hC, hB0]
    norm_num
  · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    have hkey := h (-(C / B))
    have hval : A + 2 * C * (-(C / B)) + B * (-(C / B)) ^ 2 = A - C ^ 2 / B := by
      field_simp
      ring
    rw [hval] at hkey
    have hle : C ^ 2 / B ≤ A := by linarith
    have heq : C ^ 2 = (C ^ 2 / B) * B := by
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_right hle hB

/-- **Cauchy–Schwarz for interval integrals** (`L²`-Hölder with `p = q = 2`), in the form
`(∫_a^b u v)^2 ≤ (∫_a^b u^2) * (∫_a^b v^2)`.

No measurability of `u`, `v` is assumed beyond square-integrability: if the product `u*v`
fails to be integrable the Bochner integral of the product is `0` (`integral_undef`) while
the right-hand side is a product of two nonnegative integrals, and otherwise the
nonnegativity of the quadratic `t ↦ ∫ (u + t v)^2` feeds the discriminant lemma `cs_quad`. -/
theorem cs_interval {a b : ℝ} (hab : a ≤ b) {u v : ℝ → ℝ}
    (hu : MeasureTheory.IntegrableOn (fun x => (u x) ^ 2) (Set.Ioc a b))
    (hv : MeasureTheory.IntegrableOn (fun x => (v x) ^ 2) (Set.Ioc a b)) :
    (∫ x in a..b, u x * v x) ^ 2 ≤ (∫ x in a..b, (u x) ^ 2) * (∫ x in a..b, (v x) ^ 2) := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hab]
  have h1 : Integrable (fun x => (u x) ^ 2) (volume.restrict (Set.Ioc a b)) := hu
  have h2 : Integrable (fun x => (v x) ^ 2) (volume.restrict (Set.Ioc a b)) := hv
  have hA : 0 ≤ ∫ x in Set.Ioc a b, (u x) ^ 2 := integral_nonneg (fun x => sq_nonneg (u x))
  have hB : 0 ≤ ∫ x in Set.Ioc a b, (v x) ^ 2 := integral_nonneg (fun x => sq_nonneg (v x))
  by_cases huv : Integrable (fun x => u x * v x) (volume.restrict (Set.Ioc a b))
  · have h3 : Integrable (fun x => u x * v x) (volume.restrict (Set.Ioc a b)) := huv
    -- The value of `∫ (u + t v)^2` as a polynomial in `t`.
    have hInt : ∀ t : ℝ,
        (∫ x in Set.Ioc a b, (u x + t * v x) ^ 2)
          = (∫ x in Set.Ioc a b, (u x) ^ 2) + 2 * (∫ x in Set.Ioc a b, u x * v x) * t
            + (∫ x in Set.Ioc a b, (v x) ^ 2) * t ^ 2 := by
      intro t
      have hmid : Integrable (fun x => (2 * t) * (u x * v x))
          (volume.restrict (Set.Ioc a b)) := h3.const_mul (2 * t)
      have hlast : Integrable (fun x => t ^ 2 * (v x) ^ 2)
          (volume.restrict (Set.Ioc a b)) := h2.const_mul (t ^ 2)
      have hsum : Integrable (fun x => (u x) ^ 2 + (2 * t) * (u x * v x))
          (volume.restrict (Set.Ioc a b)) := h1.add hmid
      rw [show (fun x => (u x + t * v x) ^ 2)
            = (fun x => (u x) ^ 2 + (2 * t) * (u x * v x) + t ^ 2 * (v x) ^ 2) from
          funext (fun x => by ring)]
      rw [integral_add hsum hlast, integral_add h1 hmid,
        integral_const_mul, integral_const_mul]
      ring
    refine cs_quad ?_ hB
    intro t
    rw [← hInt t]
    exact integral_nonneg (fun x => sq_nonneg (u x + t * v x))
  · rw [integral_undef huv]
    have : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [this]
    exact mul_nonneg hA hB

end Work.FTS.GalBasis.cc
