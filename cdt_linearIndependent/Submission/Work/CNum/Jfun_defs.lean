import Mathlib
import Submission.Work.CNum.Basic

/-! # CNum: definitions for the chord bound of `Jfun`

`Jfun ψ = log ‖h(c₂ + ρ₂ e^{iψ})‖` is the value of `log ‖h‖` on the circle `C₂`,
where `h = hauptH` is the hauptmodul and `Jfun` is given in `Basic` as the explicit
sum `log 256 + log ‖w ψ‖ + Σ' n, 24 log ‖1 + (w ψ)ⁿ⁺¹‖`.

For the constants we use the closed forms
`c₂ = cenC2 = 629/572`, `ρ₂ = √rho2sq = 115/143` (both rational), and the rational
upper bound `rJ = 79/100` for `‖w ψ‖` on the arc `ψ ∈ [-3.9, -2.39]`.

This file only introduces *definitions* (no proofs), so that the lemmas about them can
be stated and proved in parallel (including by other agents).
-/

namespace Work.CNum

open Complex

/-- `c₂ = 629/572`, the real centre of the circle `C₂`. -/
noncomputable def cJ : ℝ := 629 / 572

/-- `ρ₂ = 115/143`, the real radius of the circle `C₂`. -/
noncomputable def uJ : ℝ := 115 / 143

/-- `rJ = 79/100`: a rational upper bound for `‖w ψ‖` on the arc `[-3.9, -2.39]`. -/
noncomputable def rJ : ℝ := 79 / 100

/-- The point of the circle `C₂` of parameter `ψ`: `w ψ = c₂ + ρ₂ e^{iψ}`. -/
noncomputable def wf (ψ : ℝ) : ℂ := (cJ : ℂ) + (uJ : ℂ) * Complex.exp (Complex.I * ψ)

/-- The `m`-th summand `24 log ‖1 + (w ψ)ᵐ‖` of `Jfun`. -/
noncomputable def tt (m : ℕ) (ψ : ℝ) : ℝ := 24 * Real.log ‖1 + (wf ψ) ^ m‖

/-- `w ψ - c₂ = ρ₂ e^{iψ}`, the tangent factor `w' ψ = i (w ψ - c₂)`. -/
noncomputable def tanf (ψ : ℝ) : ℂ := Complex.I * (wf ψ - cJ)

/-- The first derivative of the `m`-th summand: with `f = w ψ` and `f' = tanf`,
`d/dψ 24 log ‖1 + fᵐ‖ = 24 Re [ m fᵐ⁻¹ f' / (1 + fᵐ) ]`. -/
noncomputable def tD (m : ℕ) (ψ : ℝ) : ℝ :=
  24 * ((m : ℂ) * (wf ψ) ^ (m - 1) * tanf ψ / (1 + (wf ψ) ^ m)).re

/-- `f'' ψ = -(w ψ - c₂)`, the second derivative of `wf`. -/
noncomputable def tanf2 (ψ : ℝ) : ℂ := -(wf ψ - cJ)

/-- The second derivative of the `m`-th summand, obtained from the quotient rule applied
to `m fᵐ⁻¹ f' / (1 + fᵐ)`. -/
noncomputable def tD2 (m : ℕ) (ψ : ℝ) : ℝ :=
  24 * ( ((m : ℂ) * ((m : ℂ) - 1)) * (wf ψ) ^ (m - 2) * (tanf ψ) ^ 2 / (1 + (wf ψ) ^ m)
      + (m : ℂ) * (wf ψ) ^ (m - 1) * tanf2 ψ / (1 + (wf ψ) ^ m)
      - (m : ℂ) ^ 2 * (wf ψ) ^ (2 * m - 2) * (tanf ψ) ^ 2 / (1 + (wf ψ) ^ m) ^ 2 ).re

/-- Summable dominating sequence for the first derivative series. -/
noncomputable def u1J (m : ℕ) : ℝ := 24 * (m : ℝ) * rJ ^ (m - 1) * uJ / (1 - rJ ^ m)

/-- Summable dominating sequence for the second derivative series, and the pointwise
lower bound `-tD2 m ψ ≤ bndJ m` for `‖w ψ‖ ≤ rJ`. -/
noncomputable def bndJ (m : ℕ) : ℝ :=
  24 * ( ((m : ℝ) * ((m : ℝ) - 1)) * rJ ^ (m - 2) * uJ ^ 2 / (1 - rJ ^ m)
      + (m : ℝ) * rJ ^ (m - 1) * uJ / (1 - rJ ^ m)
      + (m : ℝ) ^ 2 * rJ ^ (2 * m - 2) * uJ ^ 2 / (1 - rJ ^ m) ^ 2 )

/-- The quadratic form `K ψ = c₂² + ρ₂² + 2 c₂ ρ₂ cos ψ = ‖w ψ‖²`. -/
noncomputable def KK (ψ : ℝ) : ℝ := cJ ^ 2 + uJ ^ 2 + 2 * cJ * uJ * Real.cos ψ

/-- `log ‖w ψ‖`, written through `KK`. -/
noncomputable def LL (ψ : ℝ) : ℝ := (1 / 2) * Real.log (KK ψ)

/-- First derivative of `LL`: `-c₂ρ₂ sin ψ / K ψ`. -/
noncomputable def LLD (ψ : ℝ) : ℝ := -cJ * uJ * Real.sin ψ / KK ψ

/-- Second derivative of `LL`: `-c₂ρ₂ cos ψ / K ψ - 2 (c₂ρ₂ sin ψ)² / (K ψ)²`.
On the arc of interest this is bounded below by `-2`. -/
noncomputable def LLDD (ψ : ℝ) : ℝ :=
  -cJ * uJ * Real.cos ψ / KK ψ - 2 * (cJ * uJ * Real.sin ψ) ^ 2 / (KK ψ) ^ 2

end Work.CNum
