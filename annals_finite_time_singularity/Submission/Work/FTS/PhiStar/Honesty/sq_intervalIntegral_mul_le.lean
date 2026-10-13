import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.PhiStar.Honesty

/-- Cauchy–Schwarz (Bunyakovsky) inequality for the interval integral.

For real functions `f`, `g` on `[a, b]` (`a ≤ b`) such that `f²`, `g²` and `f * g` are
interval integrable, the square of the integral of the product is bounded by the product of
the integrals of the squares.

The proof avoids any measurability assumption by the classical quadratic-form argument: for
every `c : ℝ` the function `(f - c * g)²` is nonnegative, hence
`0 ≤ ∫ (f - c g)² = A - 2 c B + c² C` where `A = ∫ f²`, `B = ∫ f g`, `C = ∫ g²`; expanding the
square requires only the interval integrability of `f²`, `f * g`, `g²`.  Choosing `c = B / C`
when `C > 0` (respectively observing `C = 0 ⟹ B = 0`) yields `B² ≤ A * C`. -/
theorem sq_intervalIntegral_mul_le {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf2 : IntervalIntegrable (fun t : ℝ => f t ^ 2) volume a b)
    (hg2 : IntervalIntegrable (fun t : ℝ => g t ^ 2) volume a b)
    (hfg : IntervalIntegrable (fun t : ℝ => f t * g t) volume a b) :
    (∫ t in a..b, f t * g t) ^ 2 ≤ (∫ t in a..b, f t ^ 2) * (∫ t in a..b, g t ^ 2) := by
  set A : ℝ := ∫ t in a..b, f t ^ 2 with hA
  set B : ℝ := ∫ t in a..b, f t * g t with hB
  set C : ℝ := ∫ t in a..b, g t ^ 2 with hC
  have key : ∀ c : ℝ, 0 ≤ A - 2 * c * B + c ^ 2 * C := by
    intro c
    have hF : IntervalIntegrable (fun s : ℝ => f s ^ 2 - 2 * c * (f s * g s)) volume a b :=
      hf2.sub (hfg.const_mul (2 * c))
    have hG : IntervalIntegrable (fun s : ℝ => c ^ 2 * g s ^ 2) volume a b :=
      hg2.const_mul (c ^ 2)
    have hid : ∫ t in a..b, (f t - c * g t) ^ 2 = A - 2 * c * B + c ^ 2 * C := by
      rw [show (fun t : ℝ => (f t - c * g t) ^ 2)
            = fun t => (fun s : ℝ => f s ^ 2 - 2 * c * (f s * g s)) t
                + (fun s : ℝ => c ^ 2 * g s ^ 2) t from
          funext (fun t => by ring)]
      rw [intervalIntegral.integral_add hF hG,
        intervalIntegral.integral_sub hf2 (hfg.const_mul (2 * c)),
        intervalIntegral.integral_const_mul (2 * c) (fun t => f t * g t),
        intervalIntegral.integral_const_mul (c ^ 2) (fun t => g t ^ 2),
        ← hA, ← hB, ← hC]
    rw [← hid]
    exact intervalIntegral.integral_nonneg hab (fun u _ => sq_nonneg _)
  have hC0 : 0 ≤ C := by
    rw [hC]
    exact intervalIntegral.integral_nonneg hab (fun u _ => sq_nonneg _)
  have main : B ^ 2 ≤ A * C := by
    rcases lt_or_eq_of_le hC0 with hCpos | hCz
    · have h1 := key (B / C)
      have h2 : A - 2 * (B / C) * B + (B / C) ^ 2 * C = A - B ^ 2 / C := by
        field_simp [ne_of_gt hCpos]
        ring
      rw [h2] at h1
      have h3 : B ^ 2 / C ≤ A := by linarith
      exact (div_le_iff₀ hCpos).mp h3
    · have hCeq : C = 0 := hCz.symm
      have hB0 : B = 0 := by
        by_contra hBne
        have h1 := key ((A + 1) / (2 * B))
        rw [hCeq] at h1
        have h2 : 2 * ((A + 1) / (2 * B)) * B = A + 1 := by
          field_simp [hBne]
        nlinarith [h1, h2]
      rw [hCeq, hB0]
      simp
  rw [hA, hB, hC] at main
  exact main

end Work.FTS.PhiStar.Honesty
