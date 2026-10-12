import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7.Estimates
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.alpha_secondOrder_bound` — the second-order control of `Ŵ₁(k)α_k`

FS §10 (`eq:Comparealpha-A` and its use in `lem:EstimateIntegral`) needs the
*second-order* expansion of the Bogoliubov coefficient

  `α_k = ℬ_k/(𝒜_k + √(𝒜_k² - ℬ_k²))`

in the diluteness regime `ℬ_k = ρ_z Ŵ₁(k)`, `2|ℬ_k| ≤ 𝒜_k`:

  `|Ŵ₁(k)α_k - ρ_z Ŵ₁(k)²/(2𝒜_k)| ≤ 2ρ_z³Ŵ₁(k)⁴/𝒜_k³`.

This says that the first-order term `ρ_zŴ₁²/(2𝒜)` of the expansion of
`Ŵ₁α` is the whole leading part, with the remainder of the same *order in ρ_z*
as the leading term but suppressed by the diluteness parameter `(ℬ/𝒜)² ≤ ¼`.

The mathematical content is one line: writing `S = √(𝒜²-ℬ²)`, `D = 𝒜 + S`,

  `Ŵ₁α - ρ_zŴ₁²/(2𝒜) = ℬW/D - ℬW/(2𝒜) = ℬW(𝒜-S)/(2𝒜D) = ℬ³W/(2𝒜D²)`,

because `(𝒜-S)(𝒜+S) = ℬ²`, and then `D = 𝒜 + S ≥ 𝒜` gives
`2𝒜D² ≥ 2𝒜³ ≥ 𝒜³/2`.  The sign information used for the absolute value is
`ρ_z = z²/ℓ³ ≥ 0` (`thm:Kafz` together with `ℓ > 0`), which gives
`ρ_z³Ŵ₁⁴ ≥ 0`.

## Contents

* `alpha_secondOrder_scalar` — the pure scalar statement (no mode lattice).
* `alpha_secondOrder_bound` — the requested statement.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7

open Submission.BoseGases (bogS bogS_nonneg bogS_sq bog_denom_ne_zero)

/-- **The scalar core of `alpha_secondOrder_bound`.**  For `𝒜 > 0`, `ρ ≥ 0`,
`ℬ = ρW` and `2|ℬ| ≤ 𝒜`, the second-order remainder of the Bogoliubov
coefficient `α = ℬ/(𝒜+√(𝒜²-ℬ²))` is bounded by `2ρ³W⁴/𝒜³`.

(The hypothesis `ρ ≥ 0` is not decoration: it is what makes `ρ³W⁴ ≥ 0`, hence
the comparison of `1/(2𝒜(𝒜+S)²)` with `2/𝒜³` legitimate.  In the application
`ρ = ρ_z = z²/ℓ³ ≥ 0`.) -/
lemma alpha_secondOrder_scalar {A B W ρ : ℝ} (hA : 0 < A) (hρ : 0 ≤ ρ)
    (hBrel : B = ρ * W) (hBsmall : 2 * |B| ≤ A) :
    |W * (B / (A + bogS A B)) - ρ * W ^ 2 / (2 * A)| ≤
      2 * ρ ^ 3 * W ^ 4 / A ^ 3 := by
  have hBabs : |B| ≤ A := by linarith [abs_nonneg B]
  have hSnn : 0 ≤ bogS A B := bogS_nonneg A B
  have hden : A + bogS A B ≠ 0 := bog_denom_ne_zero hA hBabs
  have hsq : bogS A B ^ 2 = A ^ 2 - B ^ 2 := bogS_sq hBabs
  have hfac : A ^ 2 - bogS A B ^ 2 = B ^ 2 := by linarith [hsq]
  -- `ρW² = ℬW` and `ℬ³W = ρ³W⁴`: both are consequences of `ℬ = ρW`.
  have h1 : ρ * W ^ 2 = B * W := by rw [hBrel]; ring
  have h2 : B ^ 3 * W = ρ ^ 3 * W ^ 4 := by rw [hBrel]; ring
  -- the exact second-order identity (FS's `𝒜-S = ℬ²/(𝒜+S)`, used once)
  have hmul : W * B * (A ^ 2 - bogS A B ^ 2) = W * B * B ^ 2 := by rw [hfac]
  have hkey : W * (B / (A + bogS A B)) - ρ * W ^ 2 / (2 * A)
      = ρ ^ 3 * W ^ 4 / (2 * A * (A + bogS A B) ^ 2) := by
    rw [h1, ← h2]
    field_simp
    ring_nf
    nlinarith [hmul]
  rw [hkey]
  -- the remainder is nonnegative, and `𝒜 + S ≥ 𝒜 > 0` bounds it by `2ρ³W⁴/𝒜³`
  have hnum : 0 ≤ ρ ^ 3 * W ^ 4 := by positivity
  have hmain : ρ ^ 3 * W ^ 4 / (2 * A * (A + bogS A B) ^ 2) ≤
      ρ ^ 3 * W ^ 4 / (A ^ 3 / 2) := by
    apply div_le_div_of_nonneg_left hnum (by positivity)
    nlinarith [hSnn, sq_nonneg (bogS A B), sq_nonneg (A + bogS A B)]
  have heq : ρ ^ 3 * W ^ 4 / (A ^ 3 / 2) = 2 * ρ ^ 3 * W ^ 4 / A ^ 3 := by
    field_simp
  rw [abs_of_nonneg (by positivity :
    (0 : ℝ) ≤ ρ ^ 3 * W ^ 4 / (2 * A * (A + bogS A B) ^ 2))]
  linarith [hmain, heq]

theorem alpha_secondOrder_bound {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) {k : Mode} (hell : 0 < E.ell) (hA : 0 < E.A k)
    (hBrel : E.B k = E.rho * E.W1 k) (hBsmall : 2 * |E.B k| ≤ E.A k) :
    |E.W1 k * E.alpha k - E.rho * E.W1 k ^ 2 / (2 * E.A k)| ≤
      2 * E.rho ^ 3 * E.W1 k ^ 4 / E.A k ^ 3 := by
  -- `ρ_z = z²/ℓ³ ≥ 0` (`thm:Kafz`), using `ℓ > 0`.
  have hρ : 0 ≤ E.rho := by
    rw [Q3Env.rho, rhoZ]
    positivity
  -- `α` is the rationalised Bogoliubov coefficient `ℬ/(𝒜+√(𝒜²-ℬ²))`.
  have hα : E.alpha k = E.B k / (E.A k + bogS (E.A k) (E.B k)) := rfl
  rw [hα]
  exact alpha_secondOrder_scalar hA hρ hBrel hBsmall

end Work.BoseB7
