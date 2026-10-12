import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseB7.Coef
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseC3QAll.kernel_coef_bounds` — FS §10, the scalar kernel regime at a mode `q ∈ P_H^q`

The per-mode content of FS `eq:BoverA` / `lem:EstimatesOnQ3-js` for the
Bogoliubov kernels `𝒜(q) = A`, `ℬ(q) = B` of FS `eq:BogHamPositive-1`, under
the hypotheses collected along `q ∈ P_H^q` (`‖q‖ ≥ ¼K_H⁻¹a⁻¹`, so
`R := ‖q‖` obeys `1/(4K_H a) ≤ R`; `A ≥ R²/2`; `|ℬ| ≤ ρ_z K a`; the diluteness
`ρ a³K_H² ≤ (3/2)𝓁`; and the smallness `96 K𝓁 ≤ 1`):

* `2|ℬ| ≤ 𝒜` (FS `eq:BoverA`),
* `1 - α² ≥ ½`,
* `|α| ≤ 64K𝓁` (FS `eq:alphaInPH`),
* `𝒟 ≥ R²/4` (the kinetic lower bound of the diagonalised weight),

where `α = ℬ/(𝒜+√(𝒜²-ℬ²))` and `𝒟 = ½(𝒜+√(𝒜²-ℬ²))` are
`Work.BoseB7.alphaCoef` and `Work.BoseB7.Dcoef`.

The arithmetic core is that `R ≥ 1/(4K_H a)` and `|ℬ| ≤ ρ_zKa` give
`|ℬ| ≤ 1/(64K_H²a²)`, while the diluteness plus `96K𝓁 ≤ 1` gives
`32ρ_zKa³K_H² ≤ 48K𝓁`; the cutoff `K` only enters through the smallness.
-/

noncomputable section

namespace Work.BoseC3QAll

open Work.BoseB7

/-- `|α(𝒜,ℬ)| ≤ |ℬ|/𝒜`: `α = ℬ/(𝒜+√(𝒜²-ℬ²))` and the denominator dominates
`𝒜` (`√· ≥ 0`).  FS `eq:alphaInPH`'s first step. -/
theorem abs_alphaCoef_le {A B : ℝ} (hA : 0 < A) :
    |alphaCoef A B| ≤ |B| / A := by
  have hden : 0 < A + Submission.BoseGases.bogS A B := by
    have := Submission.BoseGases.bogS_nonneg A B
    linarith
  rw [alphaCoef, Submission.BoseGases.bogAlpha, abs_div, abs_of_pos hden]
  exact div_le_div_of_nonneg_left (abs_nonneg B) hA
    (by linarith [Submission.BoseGases.bogS_nonneg A B])

theorem kernel_coef_bounds {A B R ρ K a KH ell : ℝ}
    (hK : 0 ≤ K) (hell : 0 ≤ ell) (hKa : 0 < KH * a)
    (hA : 0 < A) (hAB : |B| ≤ A) (hBle : |B| ≤ ρ * K * a)
    (hR : R ^ 2 / 2 ≤ A) (hRcut : 1 / (4 * KH * a) ≤ R)
    (hρl : ρ * a ^ 3 * KH ^ 2 ≤ (3 / 2) * ell)
    (hsmall : 96 * K * ell ≤ 1) :
    (2 * |B| ≤ A) ∧ (1 / 2 ≤ 1 - Work.BoseB7.alphaCoef A B ^ 2) ∧
      (|Work.BoseB7.alphaCoef A B| ≤ 64 * K * ell) ∧
      (R ^ 2 / 4 ≤ Work.BoseB7.Dcoef A B) := by
  -- `R ≥ 1/(4K_H a) > 0`, so `A ≥ R²/2 ≥ (1/(4K_H a))²/2`
  have h4 : 0 < 4 * KH * a := by linarith
  have hxpos : 0 < 1 / (4 * KH * a) := one_div_pos.mpr h4
  have hRsq : (1 / (4 * KH * a)) ^ 2 ≤ R ^ 2 :=
    pow_le_pow_left₀ (le_of_lt hxpos) hRcut 2
  have hAx : (1 / (4 * KH * a)) ^ 2 / 2 ≤ A := by linarith
  -- `64 K (ρ_z a³ K_H²) ≤ 96 K𝓁 ≤ 1`
  have hkey : 64 * K * (ρ * a ^ 3 * KH ^ 2) ≤ 1 := by
    have h1 : K * (ρ * a ^ 3 * KH ^ 2) ≤ K * ((3 / 2) * ell) :=
      mul_le_mul_of_nonneg_left hρl hK
    nlinarith [h1, hsmall]
  have hBdiv : ρ * K * a ≤ 1 / (64 * KH ^ 2 * a ^ 2) := by
    rw [le_div_iff₀ (by nlinarith [pow_pos hKa 2])]
    nlinarith [hkey]
  -- conclusion 1: `2|ℬ| ≤ 𝒜`
  have hB2 : 2 * |B| ≤ A := by
    have h1 : |B| ≤ 1 / (64 * KH ^ 2 * a ^ 2) := le_trans hBle hBdiv
    have h2 : 1 / (64 * KH ^ 2 * a ^ 2) = (1 / (4 * KH * a)) ^ 2 / 4 := by
      field_simp
      ring
    rw [h2] at h1
    linarith
  -- conclusion 2
  have hhalf : 1 / 2 ≤ 1 - alphaCoef A B ^ 2 := half_le_one_sub_alphaCoef_sq hA hB2
  -- conclusion 3: `|α| ≤ |ℬ|/𝒜 ≤ (ρ_zKa)/A ≤ 32ρ_zKa³K_H² ≤ 48K𝓁 ≤ 64K𝓁`
  have hρKa_nn : 0 ≤ ρ * K * a := le_trans (abs_nonneg B) hBle
  have hα1 : |alphaCoef A B| ≤ |B| / A := abs_alphaCoef_le hA
  have hα2 : |B| / A ≤ (ρ * K * a) / A := div_le_div_of_nonneg_right hBle (le_of_lt hA)
  have hx2pos : 0 < (1 / (4 * KH * a)) ^ 2 / 2 := by positivity
  have hα3 : (ρ * K * a) / A ≤ (ρ * K * a) / ((1 / (4 * KH * a)) ^ 2 / 2) :=
    div_le_div_of_nonneg_left hρKa_nn hx2pos hAx
  have hα4 : (ρ * K * a) / ((1 / (4 * KH * a)) ^ 2 / 2) = 32 * (ρ * K * a ^ 3 * KH ^ 2) := by
    field_simp
    ring
  have hα5 : 32 * (ρ * K * a ^ 3 * KH ^ 2) ≤ 64 * K * ell := by
    have h1 : K * (ρ * a ^ 3 * KH ^ 2) ≤ K * ((3 / 2) * ell) :=
      mul_le_mul_of_nonneg_left hρl hK
    have h2 : 0 ≤ K * ell := mul_nonneg hK hell
    nlinarith [h1]
  have hα : |alphaCoef A B| ≤ 64 * K * ell := by linarith
  -- conclusion 4: `𝒟 = ½(𝒜+√(𝒜²-ℬ²)) ≥ 𝒜/2 ≥ R²/4`
  have hD : R ^ 2 / 4 ≤ Dcoef A B := by
    have hs : 0 ≤ Submission.BoseGases.bogS A B := Submission.BoseGases.bogS_nonneg A B
    rw [Dcoef, Submission.BoseGases.bogD]
    linarith
  exact ⟨hB2, hhalf, hα, hD⟩

end Work.BoseC3QAll
