/-
Copyright: work module for the Elgindi finite-time singularity project.

# Endpoint bounds for the angular slices of `DivSinBase`

`DivSinBase` (the base case of the angular calculus behind `DivisionBySin`) is proved by
two *weighted* integration-by-parts identities for a smooth slice `h : ℝ → ℝ` vanishing at
`θ = 0, π/2`, with

  `u = h / sin(2θ)`  (i.e. `u = SinQ h`),  `s = sin(2θ)`,  `c = cos(2θ)`.

Both identities need only *boundedness* of `h`, `h'`, `h''`, `u`, `u'` near the two
endpoints `0` and `π/2` (together with the pointwise identities
`h' = 2cu + su'`, `h'' = su'' + 4cu' - 4su` on the interior, which are supplied by
`Work.Elliptic.htU_interior_facts`).  This file fixes the predicate `SliceBdd`
expressing exactly those bounds, so that the analytic content ("the bounds hold for every
smooth slice vanishing at the endpoints", `Work.Elliptic.DivSinSliceBdd`) can be stated
and proved separately from the integration-by-parts identities
(`Work.Elliptic.DivSinIdentityA`, `Work.Elliptic.DivSinIdentityB`).

The bounds are stated on the two half-intervals `(0, π/4)` and `(π/4, π/2)` so that they
cover `(0, π/2)` up to the single point `π/4`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Elliptic.DivSinDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-- Endpoint bounds for a smooth angular slice `h` with `h 0 = h (π/2) = 0`: there is a
constant `C ≥ 0` such that, on the two half-intervals `(0,π/4)` and `(π/4,π/2)`,

* `|h θ| ≤ C θ` near `0` and `|h θ| ≤ C (π/2 - θ)` near `π/2`;
* `|h' θ - h'(0)| ≤ C θ` near `0` and `|h' θ - h'(π/2)| ≤ C (π/2 - θ)` near `π/2` (where
  `h'(0)`, `h'(π/2)` are the within-derivatives on `Icc 0 (π/2)`);
* `|h'' θ| ≤ C`;
* `|u θ| ≤ C` and `|u' θ| ≤ C`, where `u = SinQ h = h / sin(2θ)`.

These are precisely the estimates needed to see that every weighted integrand occurring in
`DivSinBase` is integrable and that the integration-by-parts boundary terms are continuous
at the endpoints. -/
def SliceBdd (h : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    (∀ θ ∈ Set.Ioo 0 (π / 4), |h θ| ≤ C * θ) ∧
    (∀ θ ∈ Set.Ioo 0 (π / 4),
      |deriv h θ - derivWithin h (Set.Icc 0 (π / 2)) 0| ≤ C * θ) ∧
    (∀ θ ∈ Set.Ioo 0 (π / 4), |deriv (deriv h) θ| ≤ C) ∧
    (∀ θ ∈ Set.Ioo 0 (π / 4), |SinQ h θ| ≤ C) ∧
    (∀ θ ∈ Set.Ioo 0 (π / 4), |deriv (SinQ h) θ| ≤ C) ∧
    (∀ θ ∈ Set.Ioo (π / 4) (π / 2), |h θ| ≤ C * (π / 2 - θ)) ∧
    (∀ θ ∈ Set.Ioo (π / 4) (π / 2),
      |deriv h θ - derivWithin h (Set.Icc 0 (π / 2)) (π / 2)| ≤ C * (π / 2 - θ)) ∧
    (∀ θ ∈ Set.Ioo (π / 4) (π / 2), |deriv (deriv h) θ| ≤ C) ∧
    (∀ θ ∈ Set.Ioo (π / 4) (π / 2), |SinQ h θ| ≤ C) ∧
    (∀ θ ∈ Set.Ioo (π / 4) (π / 2), |deriv (SinQ h) θ| ≤ C)

end Work.Elliptic
