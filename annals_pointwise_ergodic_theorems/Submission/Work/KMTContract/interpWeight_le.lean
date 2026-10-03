import Mathlib

set_option linter.unusedVariables false

namespace Work.KMTContract

/-- **The arithmetic core of the interpolation step of the composition.** Let `M₀ = C₆·2^{-cL}`
be the constant of the `(2,2,1)` bound of area A6 and `M₁ = C₇·2^{AρL}` that of the lossy bound
of area A7 at the auxiliary exponents, where `L = max(max l₁ l₂)(max s₁ s₂) ≥ 0`. If the
Ionescu--Wainger parameter is chosen small, `ρ ≤ (1-θ)c/(2θ(A+1))`, then the geometrically
interpolated constant of the bilinear interpolation lemma `VarBilinInterp`,

`Cθ · M₀^{1-θ} · M₁^θ = Cθ · C₆^{1-θ} C₇^θ · 2^{-(1-θ)cL + θAρL}`,

is bounded by `Cθ · max(C₆,C₇) · 2^{-((1-θ)c/2)L}` — i.e. the loss `2^{θAρL}` is absorbed into
half of the gain `2^{-(1-θ)cL}`.

This is the exact inequality needed to turn the two weighted paraproduct bounds (A6, A7) into the
canonical gain `2^{-c'·L}` of `VarpStatementΛ` with `c' = (1-θ)c/2`; it is stated in `ℝ` (with
`Real.rpow` for the real exponents) so that the composition can do its arithmetic in `ℝ`. -/
theorem interpWeight_le {c A ρ θ L C₆ C₇ Cθ : ℝ}
    (hc : 0 < c) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hA : 0 ≤ A) (hρ0 : 0 < ρ)
    (hρ : ρ ≤ (1 - θ) * c / (2 * θ * (A + 1))) (hL : 0 ≤ L)
    (hC₆ : 0 ≤ C₆) (hC₇ : 0 ≤ C₇) (hCθ : 0 ≤ Cθ) :
    Cθ * (C₆ * (2 : ℝ) ^ (-(c * L))) ^ (1 - θ) * (C₇ * (2 : ℝ) ^ (A * ρ * L)) ^ θ
      ≤ Cθ * max C₆ C₇ * (2 : ℝ) ^ (-(((1 - θ) * c / 2) * L)) := by
  have h2 : (0 : ℝ) < 2 := two_pos
  have h2le : (0 : ℝ) ≤ 2 := le_of_lt h2
  have hone : (1 : ℝ) ≤ 2 := by norm_num
  have h1θ : 0 < 1 - θ := by linarith
  have h1θ' : (0 : ℝ) ≤ 1 - θ := le_of_lt h1θ
  have hMnn : (0 : ℝ) ≤ max C₆ C₇ := le_trans hC₆ (le_max_left _ _)
  -- Clear the division in the hypothesis on `ρ`.
  have hden : 0 < 2 * θ * (A + 1) := by positivity
  have hρ' : ρ * (2 * θ * (A + 1)) ≤ (1 - θ) * c := (le_div_iff₀ hden).mp hρ
  -- `θρA ≤ (1-θ)c/2`, hence `AρLθ ≤ (1-θ)cL/2`.
  have hkey : A * ρ * L * θ ≤ (1 - θ) * c * L / 2 := by
    have hρA : θ * ρ * (A + 1) ≤ (1 - θ) * c / 2 := by linarith [hρ']
    have hρA2 : θ * ρ * A ≤ (1 - θ) * c / 2 := by
      have hle : A ≤ A + 1 := by linarith
      have h1 := mul_le_mul_of_nonneg_left hle (mul_nonneg (le_of_lt hθ0) (le_of_lt hρ0))
      linarith [h1, hρA]
    have hmulL := mul_le_mul_of_nonneg_right hρA2 hL
    linarith [hmulL, hc]
  -- Exponent comparison: `-(cL)(1-θ) + AρLθ ≤ -((1-θ)c/2)L`.
  have hexp : (-(c * L)) * (1 - θ) + (A * ρ * L) * θ ≤ -(((1 - θ) * c / 2) * L) := by
    linarith [hkey]
  have hpow : (2 : ℝ) ^ ((-(c * L)) * (1 - θ) + (A * ρ * L) * θ)
      ≤ (2 : ℝ) ^ (-(((1 - θ) * c / 2) * L)) :=
    Real.rpow_le_rpow_of_exponent_le hone hexp
  -- Weighted geometric mean of `C₆, C₇` is at most their maximum.
  have hterm : C₆ ^ (1 - θ) * C₇ ^ θ ≤ max C₆ C₇ := by
    have h1 : C₆ ^ (1 - θ) ≤ (max C₆ C₇) ^ (1 - θ) :=
      Real.rpow_le_rpow hC₆ (le_max_left _ _) h1θ'
    have h2' : C₇ ^ θ ≤ (max C₆ C₇) ^ θ :=
      Real.rpow_le_rpow hC₇ (le_max_right _ _) (le_of_lt hθ0)
    calc C₆ ^ (1 - θ) * C₇ ^ θ ≤ (max C₆ C₇) ^ (1 - θ) * (max C₆ C₇) ^ θ :=
          mul_le_mul h1 h2' (Real.rpow_nonneg hC₇ θ) (Real.rpow_nonneg hMnn (1 - θ))
      _ ≤ (max C₆ C₇) ^ ((1 - θ) + θ) := Real.le_rpow_add hMnn (1 - θ) θ
      _ = max C₆ C₇ := by rw [show (1 - θ) + θ = 1 by ring, Real.rpow_one]
  -- Rewrite the left-hand side into a product of the two factors handled above.
  have hLHS : Cθ * (C₆ * (2 : ℝ) ^ (-(c * L))) ^ (1 - θ) * (C₇ * (2 : ℝ) ^ (A * ρ * L)) ^ θ
      = Cθ * ((C₆ ^ (1 - θ) * C₇ ^ θ) *
          ((2 : ℝ) ^ ((-(c * L)) * (1 - θ)) * (2 : ℝ) ^ ((A * ρ * L) * θ))) := by
    rw [Real.mul_rpow hC₆ (Real.rpow_nonneg h2le _),
        Real.mul_rpow hC₇ (Real.rpow_nonneg h2le _),
        ← Real.rpow_mul h2le, ← Real.rpow_mul h2le]
    ring
  have hmain : (C₆ ^ (1 - θ) * C₇ ^ θ) *
        ((2 : ℝ) ^ ((-(c * L)) * (1 - θ)) * (2 : ℝ) ^ ((A * ρ * L) * θ))
      ≤ max C₆ C₇ * (2 : ℝ) ^ (-(((1 - θ) * c / 2) * L)) := by
    rw [← Real.rpow_add h2]
    exact mul_le_mul hterm hpow (Real.rpow_nonneg h2le _) hMnn
  have hRHS : Cθ * max C₆ C₇ * (2 : ℝ) ^ (-(((1 - θ) * c / 2) * L))
      = Cθ * (max C₆ C₇ * (2 : ℝ) ^ (-(((1 - θ) * c / 2) * L))) := by ring
  rw [hLHS, hRHS]
  exact mul_le_mul_of_nonneg_left hmain hCθ

end Work.KMTContract
