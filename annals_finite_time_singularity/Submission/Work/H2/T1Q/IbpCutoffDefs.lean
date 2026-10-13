/-
# `Work.H2.T1Q.IbpCutoffDefs` — the objects of the `IbpCutoff` angular integration by parts

The target `Work.H2.T1Q.IbpCutoff` is the angular integration by parts

  `∫_θ sin(2θ)^{-q}·(χ hf)·(sin(2θ)·hv')·hv
      = -∫_θ sin(2θ)^{-q}·(χ·((1/2) sin(2θ) hf' + (1-q) cos(2θ) hf) + (1/2) sin(2θ) χ' hf)·hv²`

for `χ` smooth and vanishing off `[δ, π/2-δ]` (`0 < δ ≤ π/4`) and `hf`, `hv` of class `C¹`
on the open interval `(0, π/2)`.  The cutoff `χ` localises everything to the compact
subinterval `[δ, π/2-δ] ⊂ (0, π/2)`, where `sin(2θ)` is bounded below and all the functions
involved are continuous: no boundary behaviour of `hf`, `hv` is needed at all.

The identity is the `θ`-integral of the pointwise statement that the primitive

  `IbpPrim q χ hf hv θ = (1/2)·sin(2θ)^{1-q}·χ(θ)·hf(θ)·hv(θ)²`

has derivative `IbpG q χ hf hv + IbpK q χ hf hv` on the open interval, together with the
vanishing of the primitive at the two endpoints (a consequence of `χ = 0` there).

This file only introduces the three objects, so that they can be shared between the main
proof and the auxiliary lemmas proved about them.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.H2.T1Q

/-- The left-hand integrand of `IbpCutoff`: `sin(2θ)^{-q}·(χ θ · hf θ)·(sin(2θ)·hv' θ)·hv θ`. -/
def IbpG (q : ℝ) (χ hf hv : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => (Real.sin (2 * θ)) ^ (-q) * (χ θ * hf θ) * (Real.sin (2 * θ) * deriv hv θ) * hv θ

/-- The right-hand integrand of `IbpCutoff`, without the overall sign:

`sin(2θ)^{-q}·(χ θ·((1/2)·sin(2θ)·hf' θ + (1-q)·cos(2θ)·hf θ) + (1/2)·sin(2θ)·χ' θ·hf θ)·hv θ²`. -/
def IbpK (q : ℝ) (χ hf hv : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => (Real.sin (2 * θ)) ^ (-q)
      * (χ θ * ((1 / 2) * (Real.sin (2 * θ) * deriv hf θ)
            + (1 - q) * Real.cos (2 * θ) * hf θ)
          + (1 / 2) * (Real.sin (2 * θ) * deriv χ θ) * hf θ)
      * (hv θ) ^ 2

/-- The primitive of the angular integration by parts: `(1/2)·sin(2θ)^{1-q}·χ θ·hf θ·hv θ²`. -/
def IbpPrim (q : ℝ) (χ hf hv : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => (1 / 2) * (Real.sin (2 * θ)) ^ (1 - q) * (χ θ * hf θ) * (hv θ) ^ 2

end Work.H2.T1Q
