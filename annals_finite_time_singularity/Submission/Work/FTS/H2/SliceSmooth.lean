/-
Copyright: work module for the Elgindi finite-time singularity project.

# `SliceSmooth`: the honest `z`-slice regularity for the `𝒲^{l,∞}`-product facts

`Work.FTS.LocData.SmoothQuad f` (the interior `C^∞` class used throughout this directory)
constrains `f` only on the **open** quadrant; the `z`-slices `f(·,θ)` at the two boundary lines
`θ = 0` and `θ = π/2` are then unconstrained, and the totalised derivatives `pzIter i f` used by
`Work.Spaces.WlInf` are the junk value `0` wherever the slice is not differentiable.  As a
consequence `𝒲^{4,∞}`-product facts stated with `SmoothQuad` alone are *false*: with the two
complementary nowhere-differentiable pairs `f = bdryFn (φ M 1)`, `g = bdryFn (ψ M 1)` one has
`|f|_𝒲 = |g|_𝒲 = M` while `|fg|_𝒲 ≥ 2M` (machine-checked in
`Submission/Work/FTS/H2/AuxProdWFalse.lean`, `Work.FTS.H2.prodW_false`).

The missing hypothesis is that the `z`-slices are genuinely `C^∞` on `(-1,∞)` **at every angle,
including the two boundary lines**.  That is:

* `SliceSmooth f := ∀ θ ∈ Iθ, ContDiffOn ℝ Stability.smoothOrder (fun z => f z θ) (Set.Ioi (-1))`,
  with `Stability.smoothOrder = ((⊤ : ℕ∞) : WithTop ℕ∞)` the honest `C^∞` order (`⊤ : WithTop ℕ∞`
  itself is the *analytic* order `ω`, which is why `Spaces.SmoothInt` is not usable here);

and `SmoothQuad f ∧ SliceSmooth f` is exactly `Spaces.SmoothInt` with analyticity replaced by
`C^∞`.  It is satisfied by the objects of the elliptic chapter (`F_*`, whose slices are multiples
of `2z/(1+z)²`, as well as the smooth profiles with compact support in `z`), and it makes the
Leibniz expansion of the suprema occurring in `WlInf` valid at every `θ ∈ Iθ`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Stability.Cutoff
import Submission.Work.FTS.LocData.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

open scoped Real Topology
open Set Filter

/-- The `z`-slices of `f` are `C^∞` on `(-1,∞)`, at every angle `θ ∈ Iθ`, including the two
boundary lines `θ = 0`, `θ = π/2`. -/
def SliceSmooth (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ θ ∈ Work.Spaces.Iθ,
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => f z θ) (Set.Ioi (-1))

end Work.FTS.H2
