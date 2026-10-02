import Submission.EFL.S12MainA2

/-!
# The faithful (existential-threshold) Type A₂ branch of §12: the data bundle

This module is part of `Submission/Work/S12Faithful/`, the GKO route-(3)
re-instantiation of the §12 Type-A₂ branch requested by the lead
(`NOTES_LEAD_GKO.md`, corrections of 2026-09-27).

## Why a new bundle is needed

`Submission/EFL/S12ANum.lean` pins the §12 parameters to powers of `σ`:
`ρ = σ/2`, `ρ_abs = σ/4`, `ε = σ³/10⁴²`, `ζ = σ/10¹⁴`, `η = 22ε`, and derives
every numeric side condition from `σ ≤ 10⁻²⁴`.  Those powers are *exactly* the
quantities that Corollary 10.13 (`cor:optcol`) consumes: the paper applies it
with `ρ/4`, `ε^{1/3}`, `22ε` in the roles of `p, ε, η` (efl.tex:2806).  With the
*faithful* (existential-threshold) form of Theorem 10.8 the consumer must choose
`ε` **after** the threshold functions are known, so no power of a single master
constant `σ` can serve: the parameters have to be free constants subject only to
explicit smallness relations.

## What this file provides

`S12A2Data n r₁ r₀ β γ ρ ξ ε ζ η ηr` collects *every* numeric side condition used
by the Type-A₂ branch, in the general form (no `σ`):

* `ρ` is the A₂ density, `ρ_abs = ρ/2` the absorber density (so `ρ_abs` does not
  appear as a parameter);
* `ε` is the fullness parameter (`IsFull 𝓗 ρ ε`), `ζ` the *lower-regularity
  parameter passed to Corollary 10.13* and `η` its discrepancy parameter
  (`η = 22ε` in the paper, recorded here as the field `hη22`);
* `ηr` is the *robustness* parameter of `stat:r_rem` (the paper's `ε^{1/3}/10³⁰`
  role, i.e. the `σ/10³⁰` of `S12MainA2.lean`);
* `β, γ, r₁, r₀` are the colouring-hierarchy parameters, and `ξ` the absorber
  smallness parameter (chosen by `exists_S12A2Data`).

The branch theorem `Work.S12Faithful.s12_branch_A2_faithful` consumes exactly
this bundle and feeds the *unchanged* generic chain
(`s12_to_S12Out → s12_chain → s12_finish_A2_gen`).

`Work.S12Faithful.exists_S12A2Data` produces the bundle (together with `ξ` and
the threshold `N`) from the constant-level smallness relations.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-- **The numeric data of the faithful Type-A₂ branch**, with free constants.

All fields are either constant-level relations between `β, γ, ρ, ξ, ε, ζ, η, ηr`
or `n`-large conditions (of the shape `c ≤ (constant)·n` or a floor estimate);
none of them mentions `𝓗`, `φ`, `U` or the reservoir.  The names `h15ρ`, `h30`,
`h8r₀`, `h20ε`, `h20εξ`, `hξε`, `h15ε`, `hδle`, `hξsharp`, `hεn3`, `hρn25`,
`hξn`, `h4ρεn`, `hsqrtγ`, `hξle`, `hnum3`, `hDlb` are the `S12ANum` fields with
`σ/2 ↦ ρ`, `σ/4 ↦ ρ/2`, `σ³/10⁴² ↦ ε`, `σ/10¹⁴ ↦ ζ`, `22σ³/10⁴² ↦ η` and
`σ/10³⁰ ↦ ηr`. -/
structure S12A2Data (n : ℕ) (r₁ r₀ : ℕ) (β γ ρ ξ ε ζ η ηr : ℝ) : Prop where
  /-- the full numeric hierarchy of §12, at `ρ_abs = ρ/2` and `κ = 1/2` -/
  hm : S12Margins n r₁ r₀ β γ ρ (ρ / 2) ξ ε (1 / 2)
  /-- the margins of the Leftover Lemma -/
  hleft : LeftoverMargins n r₁ γ ρ (ρ / 2) ε ξ
  /-- `0 < ρ` -/
  hρ0 : 0 < ρ
  /-- `ρ ≤ 1` -/
  hρ1 : ρ ≤ 1
  /-- `ρ ≤ 1/100` (the hypothesis of Step 2, Type A₂) -/
  hρ100 : ρ ≤ 1 / 100
  /-- `0 < β` -/
  hβ0 : 0 < β
  /-- `β ≤ 1` (the `DiffMargins` hypothesis) -/
  hβ1 : β ≤ 1
  /-- `β ≤ γ` -/
  hβγ : β ≤ γ
  /-- `0 < γ` -/
  hγ0 : 0 < γ
  /-- `γ ≤ 1` -/
  hγ1 : γ ≤ 1
  /-- `γ ≤ γ^{1/2}` (used by `(eqn:deficit)` and `(eqn:rs)`) -/
  hγs : γ ≤ Real.sqrt γ
  /-- `0 < ξ` -/
  hξ0 : 0 < ξ
  /-- `0 < ε` -/
  hε0 : 0 < ε
  /-- `0 < ζ` -/
  hζ0 : 0 < ζ
  /-- `0 < η` -/
  hη0 : 0 < η
  /-- `0 < ηr` -/
  hηr0 : 0 < ηr
  /-- `η` dominates the discrepancy bound `22ε` of `stat:r_rem` -/
  hη22 : 22 * ε ≤ η
  /-- `(eqn:bound_prev_col)` / UC1: `15γ^{1/2} + ξ ≤ ρε/2` -/
  h15ρ : 15 * Real.sqrt γ + ξ ≤ ρ * ε / 2
  /-- `30γ^{1/2} ≤ ρ`: `|C_final| > 0` -/
  h30 : 30 * Real.sqrt γ ≤ ρ
  /-- `8 ≤ ρε r₀` -/
  h8r₀ : 8 ≤ ρ * ε * (r₀ : ℝ)
  /-- `20ε ≤ ρ²` (the Type A₂ reservoir) -/
  h20ε : 20 * ε ≤ ρ ^ 2
  /-- `20ε + ξ ≤ ρ/2` (the Type A₂ reservoir) -/
  h20εξ : 20 * ε + ξ ≤ ρ / 2
  /-- `ξ ≤ ρ/2` (the Type A₂ reservoir) -/
  hξε : ξ ≤ ρ / 2
  /-- `15ε ≤ ρ` (`(eqn:rs)` for Type A₂) -/
  h15ε : 15 * ε ≤ ρ
  /-- `ξ ≤ 19ε` (the two-sided bound on `d_{R_res}`) -/
  hξε19 : ξ ≤ 19 * ε
  /-- `(eqn:deficit)`: `ξ + 20ε + 15γ^{1/2} ≤ 22ε` -/
  hδnum : ξ + 20 * ε + 15 * Real.sqrt γ ≤ 22 * ε
  /-- `ξ + (15γ^{1/2})^{1/2} ≤ ηr/2` (the small deletion in `stat:r_rem`) -/
  hξεrob : ξ + Real.sqrt (15 * Real.sqrt γ) ≤ ηr / 2
  /-- `ε^{1/2} ≤ ηr` -/
  hsqrtε : Real.sqrt ε ≤ ηr
  /-- the numerical hypothesis of the lower regularity of `G_final[U]` -/
  hnumα : ρ / 2 * (1 - 2 * Real.sqrt ε) ≥
    (ξ + Real.sqrt (15 * Real.sqrt γ)) + (ρ / 3 - ηr)
  /-- `(def:pseudoreg)` `stat:r_rem`: `ρ/4 - ζ ≤ ρ/3(1-α)^{2} - ηr/(1-α)` -/
  hnum1 : ρ / 4 - ζ ≤ ρ / 3 * (1 - 1 / 10 ^ 4) ^ 2 - ηr / (1 - 1 / 10 ^ 4)
  /-- `stat:r_rem`: `ηr/(1-α) ≤ ζ` -/
  hnum2 : ηr / (1 - 1 / 10 ^ 4) ≤ ζ
  /-- the size-comparison hypothesis of `selfLowerRegular_mono` -/
  hcardc : (1 : ℝ) ≤ (1 + (1 / 10 ^ 4) * ηr) * (1 - 10 * ε)
  /-- the sharp form of the absorber `R₁`: `10ξ + 1/n ≤ γ/2` -/
  hξsharp : 10 * ξ + 1 / (n : ℝ) ≤ γ / 2
  /-- `3 ≤ εn` (`s12_step3_typeA`) -/
  hεn3 : 3 ≤ ε * (n : ℝ)
  /-- `25 ≤ ρn` (the Type A₂ reservoir) -/
  hρn25 : 25 ≤ ρ * (n : ℝ)
  /-- `2 ≤ ξn` (the Type A₂ reservoir) -/
  hξn : 2 ≤ ξ * (n : ℝ)
  /-- `4 ≤ ρεn`: the final colour set is non-empty -/
  h4ρεn : 4 ≤ ρ * ε * (n : ℝ)
  /-- the C1/C3 numeric hypotheses of the nibble -/
  hnum3 : (Dparam n ρ : ℝ) + (D'param (Dparam n ρ) γ : ℝ) +
      (2 * γ * (n : ℝ) + 32 / β ^ 2) ≤ (n : ℝ)

/-- **The constant-level smallness bundle of the faithful Type-A₂ branch**: the
hypotheses under which `Work.S12Faithful.exists_S12A2Data` produces `S12A2Data`.  Every
field is a relation between the free constants `β γ ρ ε ζ η ηr` and the integer
parameters `r₁ r₀` (none mentions `n`), so the bundle is exactly what a proof must supply
before choosing the threshold. -/
structure S12A2Small (β γ ρ ε ζ η ηr : ℝ) (r₁ r₀ : ℕ) : Prop where
  hβ0 : 0 < β
  hγ0 : 0 < γ
  hρ0 : 0 < ρ
  hε0 : 0 < ε
  hζ0 : 0 < ζ
  hη0 : 0 < η
  hηr0 : 0 < ηr
  hr₁2 : 2 ≤ r₁
  hr₀2 : 2 ≤ r₀
  hr₁r₀ : r₁ < r₀
  hρ4 : ρ ≤ 1 / 4
  hρ100 : ρ ≤ 1 / 100
  hγ1 : γ ≤ 1
  hβγ : β ≤ γ
  hβsq : 8 * β ≤ γ ^ 2
  hβ4 : β ≤ γ ^ 4 / 10 ^ 12
  hγρs : 10 ^ 6 * (2 * γ) ≤ ρ / 2
  hγ2ε : γ ≤ 2 * ε
  hε1000 : 1000 * ε ≤ 1
  hε4000 : 4000 * ε ≤ 1
  h8γε : 8 * γ ≤ ε
  hγρabs : 1000 * (3 * γ / 2) ≤ (ρ / 2) * ε
  hβr1 : 32 ≤ β * (r₁ : ℝ)
  hr₁β₀ : (r₁ : ℝ) ≤ β * ((r₀ : ℝ) - 1)
  hr₀big : (r₁ : ℝ) < γ / 4 * ((r₀ : ℝ) - 1)
  hL5in : 10 * Real.sqrt γ < 3 * ε
  hsmall : 10 ^ 4 * Real.sqrt γ ≤ (ρ / 2) * ε
  hη22 : 22 * ε ≤ η
  h15γρε : 60 * Real.sqrt γ ≤ ρ * ε
  h15γε : 15 * Real.sqrt γ ≤ ε
  h20ερ : 20 * ε ≤ ρ / 4
  h30 : 30 * Real.sqrt γ ≤ ρ
  h8r₀ : 8 ≤ ρ * ε * (r₀ : ℝ)
  h20ε : 20 * ε ≤ ρ ^ 2
  h15ερ : 15 * ε ≤ ρ
  hηrbig : 4 * Real.sqrt (15 * Real.sqrt γ) ≤ ηr
  hsqrtε : Real.sqrt ε ≤ ηr
  hnumα0 : ρ / 2 * (1 - 2 * Real.sqrt ε) ≥
    2 * Real.sqrt (15 * Real.sqrt γ) + (ρ / 3 - ηr)
  hnum1 : ρ / 4 - ζ ≤ ρ / 3 * (1 - 1 / 10 ^ 4) ^ 2 - ηr / (1 - 1 / 10 ^ 4)
  hnum2 : ηr / (1 - 1 / 10 ^ 4) ≤ ζ
  hcardc : (1 : ℝ) ≤ (1 + (1 / 10 ^ 4) * ηr) * (1 - 10 * ε)

end

end ErdosFaberLovaszConjecture
