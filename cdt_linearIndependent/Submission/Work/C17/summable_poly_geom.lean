import Mathlib

namespace Work.C17

/-- Comparison test with a polynomially-weighted geometric majorant.

If `|f n| ≤ C (n+1)^4 θ^n` with `C, θ ≥ 0`, then for every real `r` with
`θ |r| < 1` the series `∑ f n · r^n` converges absolutely.  Indeed
`|f n · r^n| ≤ C (n+1)^4 (θ |r|)^n`, and a polynomial times a geometric
sequence with ratio `< 1` is summable. -/
theorem summable_poly_geom (f : ℕ → ℝ) (C θ : ℝ) (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (hf : ∀ n : ℕ, |f n| ≤ C * ((n : ℝ) + 1) ^ 4 * θ ^ n) {r : ℝ} (hr : θ * |r| < 1) :
    Summable fun n : ℕ => f n * r ^ n := by
  set ρ : ℝ := θ * |r| with hρdef
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; positivity
  have hρ1 : ρ < 1 := by rw [hρdef]; exact hr
  have hρnorm : ‖ρ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hρ0]; exact hρ1
  -- Monomials against the geometric sequence `ρ^n` are summable.
  have hpow : ∀ k : ℕ, Summable (fun n : ℕ => (n : ℝ) ^ k * ρ ^ n) :=
    fun k => summable_pow_mul_geometric_of_norm_lt_one k hρnorm
  have hsumm : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ 4 * ρ ^ n) := by
    have h1 := hpow 4
    have h2 := (hpow 3).mul_left (4 : ℝ)
    have h3 := (hpow 2).mul_left (6 : ℝ)
    have h4 := (hpow 1).mul_left (4 : ℝ)
    have h5 := summable_geometric_of_norm_lt_one hρnorm
    have hall := (((h1.add h2).add h3).add h4).add h5
    refine hall.congr (fun n => ?_)
    ring
  refine Summable.of_norm_bounded (g := fun n : ℕ => C * (((n : ℝ) + 1) ^ 4 * ρ ^ n))
    (hsumm.mul_left C) (fun n => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  calc |f n| * |r| ^ n
      ≤ (C * ((n : ℝ) + 1) ^ 4 * θ ^ n) * |r| ^ n :=
        mul_le_mul_of_nonneg_right (hf n) (by positivity)
    _ = C * (((n : ℝ) + 1) ^ 4 * ρ ^ n) := by
        rw [hρdef, mul_pow]; ring

end Work.C17
