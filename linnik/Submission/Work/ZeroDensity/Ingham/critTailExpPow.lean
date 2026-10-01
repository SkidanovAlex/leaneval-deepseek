import Mathlib

open Filter

namespace Work.ZeroDensity.Ingham

theorem critTailExpPow (c : ℝ) (hc : 0 < c) (n : ℕ) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → (1 + x) ^ n ≤ Real.exp (c * x) := by
  have hlo : (fun x : ℝ => (2:ℝ)^n * x^n) =o[atTop] fun x : ℝ => Real.exp (c * x) :=
    (isLittleO_pow_exp_pos_mul_atTop n hc).const_mul_left ((2:ℝ)^n)
  have hb : ∀ᶠ x : ℝ in atTop, ‖(2:ℝ)^n * x^n‖ ≤ ‖Real.exp (c * x)‖ := hlo.eventuallyLE
  have hge : ∀ᶠ x : ℝ in atTop, (1:ℝ) ≤ x :=
    Filter.eventually_atTop.mpr ⟨1, fun b hb => hb⟩
  have hmain : ∀ᶠ x : ℝ in atTop, (1 + x)^n ≤ Real.exp (c * x) := by
    filter_upwards [hb, hge] with x hb' hge'
    have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos hge'
    have hb'' : (2:ℝ)^n * x^n ≤ Real.exp (c * x) := by
      rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (by norm_num) n) (pow_nonneg (le_of_lt hx0) n)),
          Real.norm_of_nonneg (le_of_lt (Real.exp_pos _))] at hb'
      exact hb'
    have hle : 1 + x ≤ 2 * x := by linarith
    have h1 : (0:ℝ) ≤ 1 + x := by linarith
    have hpow : (1 + x)^n ≤ (2 * x)^n := pow_le_pow_left₀ h1 hle n
    rw [mul_pow] at hpow
    exact le_trans hpow hb''
  rcases Filter.eventually_atTop.mp hmain with ⟨X, hX⟩
  exact ⟨X, fun x hx => hX x hx⟩

end Work.ZeroDensity.Ingham
