import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.BoseB6.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node B6 — the scaled variables of FS `lem:BogIntegral`

With `𝒜(k) = τ(k) + ρ_zŴ₁(k)`, `ℬ(k) = ρ_zŴ₁(k)` (`eq:BogHamPositive-1`) and the
scaling `k = √(ρ_z a)t` one has `𝒜 = ρ_z a α`, `ℬ = ρ_z a β` with

  `β(t) = a⁻¹Ŵ₁(√(ρ_z a)t)`,  `α(t) = τ̃(t) + β(t)`,

  `τ̃(t) = (1−ε_T)[|t| − c₁]₊² + ε_T[|t| − c₂]₊²`,
  `c₁ = ½(K_ℓs)⁻¹(μ/ρ_z)^{1/2}`, `c₂ = ½(K_ℓds)⁻¹(μ/ρ_z)^{1/2}`.

This module fixes `fsTau` (FS's `τ̃`) and the kernel interface `ScaledKernel`
(FS `eq:tautilde-Est`'s two ingredients: `β(0) = 8π`, `0 ≤ β ≤ B`,
`|β(t)−8π| ≤ η|t|`, and compact support from the kernel's momentum cutoff).
The elementary consequences (`eq:tautilde-Est`) are proved separately as
`Work.BoseB6.fsTau_bounds`.
-/

noncomputable section

open scoped Real BigOperators

namespace Work.BoseB6

/-- FS's truncated kinetic symbol in the scaled variables (`lem:BogIntegral`):
`τ̃(t) = (1−ε_T)[|t|−c₁]₊² + ε_T[|t|−c₂]₊²`. -/
def fsTau (εT c1 c2 t : ℝ) : ℝ :=
  (1 - εT) * (max (|t| - c1) 0) ^ 2 + εT * (max (|t| - c2) 0) ^ 2

/-- FS's scaled Bogoliubov kernel data: `β(t) = a⁻¹Ŵ₁(√(ρ_z a)t)` with
`β(0) = 8π`, `0 ≤ β ≤ B`, `|β(t) − 8π| ≤ η|t|` (the χ-Taylor bound
`|Ŵ₁(k) − Ŵ₁(0)| ≤ Ca(kR)²` and boundedness, interpolated), and `β = 0` beyond
the kernel's momentum cutoff (`‖t‖ ≤ T`). -/
structure ScaledKernel where
  /-- `β(t) = a⁻¹Ŵ₁(√(ρ_z a)t)`. -/
  β : ℝ → ℝ
  /-- a bound `β ≤ B` (from `∫|Ŵ₁| ≤ Ca`, FS `eq:WSestimate`). -/
  B : ℝ
  /-- the closeness parameter of `|β(t) − 8π| ≤ η|t|`. -/
  η : ℝ
  /-- the momentum cutoff of the kernel, `β(t) = 0` for `|t| > T`. -/
  T : ℝ
  Bnn : 0 ≤ B
  ηnn : 0 ≤ η
  Tnn : 0 ≤ T
  /-- `Ŵ₁ ≥ 0` a.e. gives `β ≥ 0`. -/
  nonneg : ∀ r, 0 ≤ β r
  /-- FS `eq:WSestimate`: `β ≤ B`. -/
  bound : ∀ r, β r ≤ B
  /-- `|Ŵ₁(k) − Ŵ₁(0)| ≤ Ca(kR)²` in scaled variables (for `r = ‖t‖ ≥ 0`). -/
  close : ∀ r, 0 ≤ r → |β r - 8 * Real.pi| ≤ η * r
  /-- the kernel's momentum cutoff. -/
  support : ∀ r, T < r → β r = 0

/-- **`β(0) = 8π`** (FS `Ŵ₁(0) = ∫Ŵ₁ = 8πa`): the closeness hypothesis at `r = 0`. -/
theorem ScaledKernel.beta_zero (K : ScaledKernel) : K.β 0 = 8 * Real.pi := by
  have h := K.close 0 le_rfl
  simp only [mul_zero, abs_le] at h
  linarith [h.1, h.2]

end Work.BoseB6
