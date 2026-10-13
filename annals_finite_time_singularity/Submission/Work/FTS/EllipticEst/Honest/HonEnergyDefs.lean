/-
Copyright: work module for the Elgindi finite-time singularity project.

# The functionals of the honest `w²`-weighted energy inequality

This module fixes the *notation* of the truncated energy identity and of the truncated
inequality of Step 1 of Elgindi's `prop:H2`, so that the auxiliary lemmas of the assembly
(`HonTruncIdentitySmooth`, `HonEnergyTruncIneq`, `CutErrTendsto`, ...) can be stated compactly.

* `TruncId α Ψ φ` — the six-term identity obtained by testing `(PolarBSL)` against `Ψ·φ·w²`
  and integrating by parts in `θ` and in `z` (`φ` a test weight vanishing on a neighbourhood
  of `z = 0` with compact support in `(0,∞)`);
* `TruncX α Ψ φ` — the left-hand side of the truncated inequality (the `w²`-weighted energy of
  `∂_zΨ` and `∂_θΨ` against the test weight `φ`);
* `TruncSrc α F φ` — the source term `(1/2)∫_z φw²∫_θ F²`;
* `TruncErr α Ψ φ` — the truncation error produced by the derivatives of `φ` against the
  weight bounds `|(z²w²)''| ≤ 6w²`, `|(zw²)'| ≤ 3w²`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false

/-- The energy functional of the truncated inequality, with an arbitrary `z`-weight `φ`:
`α²∫_z φw²z²∫_θ (∂_zΨ)² + ∫_z φw²∫_θ (∂_θΨ)²`. -/
def TruncX (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (φ : ℝ → ℝ) : ℝ :=
  α ^ 2 * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2 * z ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz Ψ z θ) ^ 2))
    + (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth Ψ z θ) ^ 2))

/-- The source term of the truncated inequality: `(1/2)∫_z φw²∫_θ F²`. -/
def TruncSrc (α : ℝ) (F : ℝ → ℝ → ℝ) (φ : ℝ → ℝ) : ℝ :=
  (1 / 2) * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2))

/-- The `Ψ²`-mass of a truncated weight: `∫_z φw²∫_θ Ψ²`. -/
def TruncP (Ψ : ℝ → ℝ → ℝ) (φ : ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2
    * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)

/-- The truncation error of the radial integration by parts: the `φ'`- and `φ''`-terms produced by
differentiating `z²φw²` and `zφw²`, bounded pointwise by `|(z²w²)''| ≤ 6w²`, `|(zw²)'| ≤ 3w²`. -/
def TruncErr (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (φ : ℝ → ℝ) : ℝ :=
  (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
      (2 * |deriv φ z| * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
        + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
      * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
    + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz, |deriv φ z|
        * (z * (Work.Spaces.w z) ^ 2) * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))

/-- The honest truncated energy identity for the test weight `φ`. -/
def TruncId (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (φ : ℝ → ℝ) : Prop :=
  (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.bslOp α Ψ z θ * Ψ z θ))
    = α ^ 2 * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2 * z ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz Ψ z θ) ^ 2))
      - (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
          deriv (deriv (fun z => φ z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z
            * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
      + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
          deriv (fun z => φ z * (Work.Spaces.w z) ^ 2 * z) z
            * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
      + (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth Ψ z θ) ^ 2))
      + (1 / 2) * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Ψ z θ / Real.cos θ) ^ 2))
      - 6 * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))

end Work.FTS.EllipticEst.Honest
