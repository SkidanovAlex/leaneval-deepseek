import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Bog2Mode
import Submission.Work.BoseB7.Params
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.Coef` — the coefficients of FS §10

FS §10's whole calculation is a statement about the *kernels*

* `𝒜(k) = τ(k) + ρ_z Ŵ₁(k)`, `ℬ(k) = ρ_z Ŵ₁(k)` (FS `eq:BogHamPositive-1`),
* `𝒟_k = ½(𝒜_k + √(𝒜_k² - ℬ_k²))`, `α_k = ℬ_k/(𝒜_k + √(𝒜_k² - ℬ_k²))`
  (FS `thm:BogHamDiag`; the rationalised form is the one used in the proofs of
  §10, cf. `eq:Comparealpha-A`, `eq:alphaInPH`),
* `𝒞(k) = ℓ⁻³(ρ_z - μ)Ŵ₁(0)χ̂(k)z` and the shift
  `c_k = 2𝒞(k)/(𝒜_k + ℬ_k + √(𝒜_k² - ℬ_k²))` (FS `eq:Defb_k`).

The Bogoliubov *scalar* algebra (`bogS`, `bogD`, `bogAlpha`, and the identities
`bog_D_mul_one_add_alpha_sq`, `bog_alpha_mul_D`, `bog_A_sub_s_eq`) is the
corpus's `Submission.Bog2Mode`; it is reused here so that the `B6` and `B7`
chapters cannot disagree about `α` and `𝒟`.

## Contents

* `Acoef`, `Bcoef`, `Ccoef`, `Dcoef`, `alphaCoef`, `cCoef` — FS's kernels.
* `alphaCoef_eq_inv_mul` — the rationalisation
  `α = ℬ/(𝒜+√(𝒜²-ℬ²)) = ℬ⁻¹(𝒜-√(𝒜²-ℬ²))` (FS's two forms of `α`).
* `one_sub_alpha_sq` — `1 - α² = 2√(𝒜²-ℬ²)/(𝒜+√(𝒜²-ℬ²))` and
  `1 - α² ≥ (√(𝒜²-ℬ²)/𝒜)² > 0`, the denominator control of
  `lem:EstimatesOnQ3-js`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7

open Submission.BoseGases (bogS bogD bogAlpha bog_denom_ne_zero)
open Submission.BoseGases (bogS_sq bogS_nonneg bogS_sq_le bogD_pos bog_A_sub_s_eq)

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- FS `eq:BogHamPositive-1`: `𝒜(k) = τ(k) + ρ_z Ŵ₁(k)`. -/
noncomputable def Acoef (tau W : ℝ³ → ℝ) (ρ : ℝ) : ℝ³ → ℝ := fun k => tau k + ρ * W k

/-- FS `eq:BogHamPositive-1`: `ℬ(k) = ρ_z Ŵ₁(k)`. -/
noncomputable def Bcoef (W : ℝ³ → ℝ) (ρ : ℝ) : ℝ³ → ℝ := fun k => ρ * W k

/-- FS `eq:BogHamPositive-1` / `thm:BogHamDiag`: `𝒟(k) = ½(𝒜(k) + √(𝒜(k)²-ℬ(k)²))`,
the weight of the diagonalised quadratic operator. -/
noncomputable def Dcoef (A B : ℝ) : ℝ := bogD A B

/-- FS `thm:BogHamDiag`'s squeezing parameter in its rationalised form
`α = ℬ/(𝒜+√(𝒜²-ℬ²))` (the form used throughout the proofs of §10, in which
`|α| ≤ 𝓁` is `eq:alphaInPH`). -/
noncomputable def alphaCoef (A B : ℝ) : ℝ := bogAlpha A B

/-- FS `eq:BogHamPositive-1`: `𝒞(k) = ℓ⁻³(ρ_z-μ)Ŵ₁(0)χ̂(k)z`, the coefficient of
the linear terms of `𝒦^Bog` (non-zero only for `|k| ≤ ½K_H⁻¹a⁻¹`, i.e. in the
definition of `c_k`). -/
noncomputable def Ccoef (ell ρ μ W0 z : ℝ) (hatChi : ℝ³ → ℝ) (k : ℝ³) : ℝ :=
  ell ^ (-(3 : ℝ)) * (ρ - μ) * W0 * hatChi k * z

/-- FS `eq:Defb_k`'s shift
`c_k = 2𝒞(k)/(𝒜(k)+ℬ(k)+√(𝒜(k)²-ℬ(k)²))` for `|k| ≤ ½K_H⁻¹a⁻¹`, and `0` above
the cutoff.  (The estimates of `lem:EstimatesOnQ3-js` are proved for the
*unshifted* `b_k = a_k + α_k a_{-k}†`; the shift is FS's linear-term bookkeeping
of `thm:BogHamDiag`, recorded here for completeness.) -/
noncomputable def cCoef (ell ρ μ W0 z : ℝ) (hatChi : ℝ³ → ℝ) (AC B : ℝ) (cut : ℝ)
    (k : ℝ³) : ℝ :=
  if ‖k‖ ≤ cut then 2 * Ccoef ell ρ μ W0 z hatChi k / (AC + B + bogS AC B) else 0

/-! ## The rationalisation identities of `α` and `1-α²` -/

/-- FS's two forms of the squeezing parameter agree:
`ℬ/(𝒜+√(𝒜²-ℬ²)) = ℬ⁻¹(𝒜-√(𝒜²-ℬ²))` (`𝒜 > 0`, `|ℬ| ≤ 𝒜`).  This is the
algebraic content of `thm:BogHamDiag`'s `α_k := ℬ(k)⁻¹(𝒜(k) - √(𝒜²-ℬ²))`. -/
theorem alphaCoef_eq_inv_mul {A B : ℝ} (hA : 0 < A) (hB : |B| ≤ A) (hB0 : B ≠ 0) :
    alphaCoef A B = B⁻¹ * (A - bogS A B) := by
  have hden : A + bogS A B ≠ 0 := bog_denom_ne_zero hA hB
  have hs2 : (bogS A B) ^ 2 = A ^ 2 - B ^ 2 := bogS_sq hB
  rw [alphaCoef, bogAlpha]
  field_simp
  nlinarith [hs2]

/-- `α(𝒜+√(𝒜²-ℬ²)) = ℬ`: the defining relation of `α`, used to rewrite
`Ŵ₁(k)α_k = ρ_z⁻¹𝒜(k)(1-√(1-ℬ²/𝒜²))` (FS's proof of `lem:EstimateIntegral`). -/
theorem alphaCoef_mul_denom {A B : ℝ} (hA : 0 < A) (hB : |B| ≤ A) :
    alphaCoef A B * (A + bogS A B) = B := by
  rw [alphaCoef, bogAlpha, div_mul_cancel₀ _ (bog_denom_ne_zero hA hB)]

/-- `1 - α² = (2√(𝒜²-ℬ²))/(𝒜+√(𝒜²-ℬ²))`: the denominator bookkeeping of
`lem:EstimatesOnQ3-js` (the factors `1/((1-α_k²)(1-α_{s-k}²))`). -/
theorem one_sub_alphaCoef_sq {A B : ℝ} (hA : 0 < A) (hB : |B| ≤ A) :
    1 - alphaCoef A B ^ 2 = 2 * bogS A B / (A + bogS A B) := by
  have hden : A + bogS A B ≠ 0 := bog_denom_ne_zero hA hB
  have hs2 : (bogS A B) ^ 2 = A ^ 2 - B ^ 2 := bogS_sq hB
  rw [alphaCoef, bogAlpha]
  field_simp
  nlinarith [hs2]

/-- `1 - α² = 2√(𝒜²-ℬ²)/(𝒜+√(𝒜²-ℬ²)) > 0` for `𝒜 > 0`, `|ℬ| < 𝒜` (strict):
the strictness is *needed* — at `|ℬ| = 𝒜` one has `α = ±1` and `1-α² = 0`.  In
FS `|ℬ/𝒜| ≤ ½` (`eq:BoverA`), so this is exactly the smallness FS record. -/
theorem one_sub_alphaCoef_sq_pos {A B : ℝ} (hA : 0 < A) (hB : |B| < A) :
    0 < 1 - alphaCoef A B ^ 2 := by
  have hB' : |B| ≤ A := le_of_lt hB
  rw [one_sub_alphaCoef_sq hA hB']
  have hs : 0 < bogS A B := by
    have hs2 : (bogS A B) ^ 2 = A ^ 2 - B ^ 2 := bogS_sq hB'
    have hB2 : B ^ 2 < A ^ 2 := by
      rw [sq_lt_sq]; rwa [abs_of_pos hA]
    rcases eq_or_lt_of_le (bogS_nonneg A B) with h | h
    · rw [← h] at hs2; nlinarith
    · exact h
  have hden : 0 < A + bogS A B := by linarith
  positivity

/-- `1 - α² ≥ ½` under FS's smallness `2|ℬ| ≤ 𝒜` (the regime behind `eq:BoverA`:
`|ℬ/𝒜| ≤ C𝓁 ≤ ½`).  The crude uniform bound the estimates use to discard the
denominators `(1-α²)`. -/
theorem half_le_one_sub_alphaCoef_sq {A B : ℝ} (hA : 0 < A) (hB : 2 * |B| ≤ A) :
    (1 : ℝ) / 2 ≤ 1 - alphaCoef A B ^ 2 := by
  have hB' : |B| ≤ A := by linarith [abs_nonneg B]
  rw [one_sub_alphaCoef_sq hA hB']
  have hden : 0 < A + bogS A B := by have := bogS_nonneg A B; linarith
  rw [le_div_iff₀ hden]
  have hs2 : (bogS A B) ^ 2 = A ^ 2 - B ^ 2 := bogS_sq hB'
  have hsnn : 0 ≤ bogS A B := bogS_nonneg A B
  have habs : B ^ 2 ≤ (A / 2) ^ 2 := by
    have h1 : |B| ≤ A / 2 := by linarith
    calc B ^ 2 = |B| ^ 2 := (sq_abs B).symm
      _ ≤ (A / 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg B) h1 2
  have hkey : (A / 3) ^ 2 ≤ (bogS A B) ^ 2 := by nlinarith
  have hA3 : A / 3 ≤ bogS A B := by
    have h := sq_le_sq.mp hkey
    rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ A / 3), abs_of_nonneg hsnn] at h
  linarith

end Work.BoseB7
