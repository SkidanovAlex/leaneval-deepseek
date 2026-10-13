/-
Copyright: work module for the Elgindi finite-time singularity project.

# The measurable majorant for the level-6 slots

The final energy bound `HkNorm α 6 f ≤ B` of
`Work.FTS.StrongEps.exists_locUnif_subseq_of_uniform_H6` rests on bounding the
`∫⁻`-integral of the weighted `H^6`-integrand of the limit `f` by the `liminf` of the
corresponding quantities for the approximating sequence.

The slots of order `≤ 5` are handled by Fatou directly (they converge pointwise, resp.
almost everywhere, along the sequence).  The seven slots of order `6` are *not* known to be
a.e. measurable (`deriv` of a merely almost-everywhere measurable function need not be
measurable), so they are handled through a **measurable majorant**: the `liminf` of the
*backward difference quotients* of the level-5 slots, which is automatically measurable as
soon as the level-5 slots are.

This file collects the definitions of that majorant.  Nothing here is proved; the
definitions live in a standalone module so that they can be shared with the lemmas that
bound them.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif

set_option autoImplicit false

/-- The weight with which the level-6 slot `mixed j i` (`i + j = 6`) occurs in
`Work.Spaces.HkIntegrand α 6`: the pure `D_z^6` slot (`i = 0`) carries the radial weight
`w z / sin(2θ)^{η/2}`, while every slot with `i ≥ 1` carries the full weight
`Wt α z θ = w z · sin(2θ)^{-γ/2}`. -/
def rho6 (α : ℝ) (i : ℕ) (z θ : ℝ) : ℝ :=
  if i = 0 then Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
  else Work.Spaces.Wt α z θ

/-- The `z`-directed part of the level-6 slots of `HkIntegrand α 6 g`: the slot
`D_z^6 g = mixed 6 0 g` together with the five mixed slots `mixed (6 - i) i g` with
`1 ≤ i ≤ 5`.  (The remaining level-6 slot, `mixed 0 6 g = D_θ^6 g`, is `level6T`.) -/
def level6Z (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 6, (Work.Spaces.mixed (6 - i) i g z θ * rho6 α i z θ) ^ 2

/-- The `θ`-directed level-6 slot `D_θ^6 g = mixed 0 6 g` of `HkIntegrand α 6 g`. -/
def level6T (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.mixed 0 6 g z θ * rho6 α 6 z θ) ^ 2

/-- **The measurable majorant of the six `z`-directed level-6 slots of the limit.**

For each of the six level-5 slots `W_i = mixed (5 - i) i f` (`0 ≤ i ≤ 5`), whose child
`D_z W_i = mixed (6 - i) i f` is a level-6 slot with weight `rho6 α i`, the majorant takes
the `liminf` (as `j → ∞`) of the squared `j`-th *backward* difference quotient of `W_i`
with step `1/(j+1)`, weighted by `z · rho6 α i` — so that the limiting quantity is
`z · ∂_z W_i · rho6 α i = D_z W_i · rho6 α i`. -/
def V6z (α : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  Filter.liminf (fun j : ℕ => ∑ i ∈ Finset.range 6, ENNReal.ofReal
    (((Work.Spaces.mixed (5 - i) i f p.1 p.2
        - Work.Spaces.mixed (5 - i) i f (p.1 - 1 / ((j : ℝ) + 1)) p.2) * ((j : ℝ) + 1)
      * (p.1 * rho6 α i p.1 p.2)) ^ 2)) Filter.atTop

/-- **The measurable majorant of the `θ`-directed level-6 slot of the limit** (`mixed 0 6 f
= D_θ (mixed 0 5 f)`), built from the backward difference quotients in `θ` of the level-5
slot `mixed 0 5 f`, weighted by `sin(2θ) · Wt α`. -/
def V6t (α : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  Filter.liminf (fun j : ℕ => ENNReal.ofReal
    (((Work.Spaces.mixed 0 5 f p.1 p.2
        - Work.Spaces.mixed 0 5 f p.1 (p.2 - 1 / ((j : ℝ) + 1))) * ((j : ℝ) + 1)
      * (Real.sin (2 * p.2) * rho6 α 6 p.1 p.2)) ^ 2)) Filter.atTop

end Work.FTS.StrongEps.LocUnif
