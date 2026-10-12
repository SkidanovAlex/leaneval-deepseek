import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.ZPLatticeAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.CleanFunAux` — the kinematic abbreviations of the clean-row sign row

The sign row `Work.BoseBogFS.cleanFun_nonneg_of_large` states that the clean part of the
zero-point summand (FS `eq:LHYIntegral1`)

`cleanFun v h ρ μ k = 𝒵(τ(k)+c(k), c(k)) − c(k)²/(2‖k‖²)`

is nonnegative for large `‖k‖`, where

* `τ = tauAt v μ k` is the honest smoothed kinetic symbol
  `τ̃ = (1−ε_T)u²φ(x/u) + ε_T u₂²φ(x/u₂)` with the two thresholds
  `u = (2sℓ)⁻¹`, `u₂ = (2dsℓ)⁻¹` (`Work.BoseBoxFock.tauSm`);
* `c = cAt v h ρ μ k = ρ·Ŵ₁(k)` is the pairing coefficient;
* `𝒵(𝒜,ℬ) = 𝒜 − √(𝒜²−ℬ²)` (`Work.BoseB6.bogZeroPoint`).

The proof has three inputs, and this module collects the *kinematic abbreviations* in which
they are stated (so that the statements stay readable):

* **upper bound of `τ`** — `φ(r) ≤ (max 0 (r−1))²` gives
  `τ ≤ (1−ε_T)(max 0 (x−u))² + ε_T(max 0 (x−u₂))²`, hence the **linear deficit**
  `2‖k‖·min(u,u₂) − max(u,u₂)² ≤ ‖k‖² − τ` (`cleanLoMin`, `cleanLoMax`);
* **lower bound of `τ`** — `φ(r) ≥ (max 0 (r−2))²` gives `(max 0 (x−2·max(u,u₂)))² ≤ τ`;
* **bound of the pairing** — `|cAt v h ρ μ k| ≤ cleanCB v μ`, where
  `cleanRhoB v μ = μ + μ·K_ℓ^{-2}/(2¹⁴π)` is the upper bound for `|ρ|` in the closed
  condition `CloseCondFS` (`|ρ−μ| ≤ μK_ℓ^{-2}/(2¹⁴π)`) and `16π·a v` is FS `eq:WSestimate`
  (`Work.BoseB7AK.W1rows.W1hat_abs_le`).

The threshold of the row is `cleanKstar v μ`: the largest of `0`, `2·max(u,u₂) + √(2·cleanCB)`
(so that `τ ≥ 2·cleanCB`, giving `0 < 𝒜` and `|c| ≤ 𝒜` for `𝒜 = τ+c`) and
`(cleanCB + max(u,u₂)²)/(2·min(u,u₂))` (so that `x² − τ ≥ cleanCB`, giving `𝒜 ≤ x²`).

This module is **definitions only** (plus one pure-real lemma): it is the frozen vocabulary
shared with the delegated rows `tauAt_bounds` and `abs_cAt_le`, and it deliberately does not
import `CleanRowDefs` (so that a prover of those rows needs only the kinematic layer).
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The first threshold of the honest kinetic symbol, `u = (2sℓ)⁻¹`. -/
def cleanLo1 (v : ℝ³ → ℝ) (μ : ℝ) : ℝ :=
  (2 * (paramsAt μ (a v)).s * ell v μ)⁻¹

/-- The second threshold of the honest kinetic symbol, `u₂ = (2dsℓ)⁻¹`. -/
def cleanLo2 (v : ℝ³ → ℝ) (μ : ℝ) : ℝ :=
  (2 * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s * ell v μ)⁻¹

/-- The larger of the two thresholds: the lower bound of `τ` reads
`(max 0 (x − 2·cleanLoMax))² ≤ τ`. -/
def cleanLoMax (v : ℝ³ → ℝ) (μ : ℝ) : ℝ := max (cleanLo1 v μ) (cleanLo2 v μ)

/-- The smaller of the two thresholds: the linear deficit of `τ` has slope
`2·cleanLoMin`. -/
def cleanLoMin (v : ℝ³ → ℝ) (μ : ℝ) : ℝ := min (cleanLo1 v μ) (cleanLo2 v μ)

/-- The bound for `|ρ|` carried by `Work.BoseBoxFock.CloseCondFS`:
`|ρ| ≤ μ + μ·K_ℓ^{-2}/(2¹⁴π)`. -/
def cleanRhoB (v : ℝ³ → ℝ) (μ : ℝ) : ℝ :=
  μ + μ * (paramsAt μ (a v)).Kl ^ (-(2 : ℝ)) / ((2 : ℝ) ^ 14 * Real.pi)

/-- The uniform bound for the pairing coefficient `|cAt v h ρ μ k|` under
`CloseCondFS v μ ρ`: `cleanRhoB · 16π·a v`. -/
def cleanCB (v : ℝ³ → ℝ) (μ : ℝ) : ℝ := cleanRhoB v μ * (16 * Real.pi * a v)

/-- **The threshold of the sign row.**  Beyond `cleanKstar` the clean summand is nonnegative:
`2·max(u,u₂) + √(2·cleanCB)` forces `τ ≥ 2·cleanCB` (so `0 < τ+c` and `|c| ≤ τ+c`) and
`(cleanCB + max(u,u₂)²)/(2·min(u,u₂))` forces `‖k‖² − τ ≥ cleanCB` (so `τ+c ≤ ‖k‖²`). -/
def cleanKstar (v : ℝ³ → ℝ) (μ : ℝ) : ℝ :=
  max 0 (max (2 * cleanLoMax v μ + Real.sqrt (2 * cleanCB v μ))
    ((cleanCB v μ + (cleanLoMax v μ) ^ 2) / (2 * cleanLoMin v μ)))

/-- **The pure-real core of the sign row.**  If `0 < A`, `|c| ≤ A` and `A ≤ x²`, then
`𝒵(A,c) − c²/(2x²) ≥ 0`: `A − √(A²−c²) = c²/(A+√(A²−c²)) ≥ c²/(2A) ≥ c²/(2x²)`. -/
lemma le_sub_sqrt_div {A c x : ℝ} (hA : 0 < A) (hc : |c| ≤ A) (hAx : A ≤ x ^ 2) :
    0 ≤ A - Real.sqrt (A ^ 2 - c ^ 2) - c ^ 2 / (2 * x ^ 2) := by
  have hc2 : c ^ 2 ≤ A ^ 2 := by
    rw [← sq_abs c]
    exact pow_le_pow_left₀ (abs_nonneg c) hc 2
  have hsA : Real.sqrt (A ^ 2 - c ^ 2) ≤ A := by
    calc Real.sqrt (A ^ 2 - c ^ 2) ≤ Real.sqrt (A ^ 2) :=
          Real.sqrt_le_sqrt (by linarith [sq_nonneg c])
      _ = A := Real.sqrt_sq hA.le
  have hs2 : Real.sqrt (A ^ 2 - c ^ 2) ^ 2 = A ^ 2 - c ^ 2 := Real.sq_sqrt (by linarith)
  have hden : 0 < A + Real.sqrt (A ^ 2 - c ^ 2) := by
    have := Real.sqrt_nonneg (A ^ 2 - c ^ 2); linarith
  have hid : A - Real.sqrt (A ^ 2 - c ^ 2) = c ^ 2 / (A + Real.sqrt (A ^ 2 - c ^ 2)) := by
    rw [eq_div_iff (ne_of_gt hden)]
    nlinarith [hs2]
  have h1 : c ^ 2 / (2 * A) ≤ c ^ 2 / (A + Real.sqrt (A ^ 2 - c ^ 2)) :=
    div_le_div_of_nonneg_left (sq_nonneg c) (by linarith) (by linarith)
  have h2 : c ^ 2 / (2 * x ^ 2) ≤ c ^ 2 / (2 * A) :=
    div_le_div_of_nonneg_left (sq_nonneg c) (by positivity) (by nlinarith)
  rw [hid]
  linarith

end Work.BoseBogFS
