/-
# `Work.FTS.GalBasis.cc.SlotDefs` — slot densities and the product-rule right-hand side

The `ℋ⁴`-integrand of `Work.Spaces` is a sum of squares of *slot densities*: the `D_z`-family
slots `D_z^i f · w/sin(2θ)^{η/2}` and the mixed slots `D_z^jD_θ^i f · Wt α` (`i ≥ 1`).  This
module names the two weights and the two slot densities, and defines the explicit right-hand
side `mulSlotRHS α χ f` of the pointwise product-rule bound
(`Work.FTS.GalBasis.cc.HkIntegrand_mul_le_slots`): the expansion of the `ℋ⁴`-integrand of
`χ · f` by the Leibniz rule, with the multiplier factors `mixed b a χ` kept (so that the
consumer can exploit their support), each `f`-factor replaced by the corresponding slot density.

The only subtlety of the definition is the *weight mismatch* of the terms in which all the
`θ`-derivatives fall on the multiplier (the case `i - a = 0`): there the `f`-factor is a plain
`D_z`-derivative carrying the *mixed* weight `Wt α`, which is not one of the slots of
`HkIntegrand`; those terms are `DzIter (j-b) f · Wt α` in `mulSlotRHS`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.Galerkin.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

open Work.FTS.Galerkin (Fn)

/-- The pure weight `w z / sin(2θ)^{η/2}` of the `D_z`-family slots (as it appears in
`Work.Spaces.HkIntegrand`). -/
def pw (z θ : ℝ) : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)

/-- The `D_z`-family slot density of `f` at index `a`: `D_z^a f · pw`. -/
def zslot (a : ℕ) (f : Fn) (z θ : ℝ) : ℝ := Work.Spaces.DzIter a f z θ * pw z θ

/-- The mixed slot density of `f` at indices `(j,i)`: `D_z^j D_θ^i f · Wt α`. -/
def mslot (α : ℝ) (j i : ℕ) (f : Fn) (z θ : ℝ) : ℝ :=
  Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ

/-- The `D_z`-family slot density with the **mixed** weight, `D_z^a f · Wt α`: this is the
quantity produced by the terms of the Leibniz expansion of `mixed j i (χ f)` in which all the
`θ`-derivatives fall on the multiplier `χ` (`i - a = 0`). -/
def zslotW (α : ℝ) (a : ℕ) (f : Fn) (z θ : ℝ) : ℝ :=
  Work.Spaces.DzIter a f z θ * Work.Spaces.Wt α z θ

/-- **The right-hand side of the pointwise product-rule bound.**  For a multiplier `χ` and a
function `f` it is the Leibniz expansion of the `ℋ⁴`-integrand of `χ · f`, with the multiplier
factors kept and the `f`-factors replaced by the slot densities above:
`∑_{j,s} (mixed s 0 χ)² (zslot (j-s) f)² + ∑_{i,j,a,b} (mixed b a χ)² (mslot/mixed-weight slot)²`.
The guards make the sums finite and match the ranges of `HkIntegrand` (`1 ≤ i`, `i + j ≤ 4`). -/
def mulSlotRHS (α : ℝ) (χ f : Fn) (z θ : ℝ) : ℝ :=
  (∑ j ∈ Finset.range 5, ∑ s ∈ Finset.range 5,
      (if s ≤ j then (Work.Spaces.mixed s 0 χ z θ) ^ 2 * (zslot (j - s) f z θ) ^ 2 else 0))
    + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        ∑ a ∈ Finset.range 5, ∑ b ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 ∧ a ≤ i ∧ b ≤ j then
            (Work.Spaces.mixed b a χ z θ) ^ 2 *
              (if 1 ≤ i - a then (mslot α (j - b) (i - a) f z θ) ^ 2
                else (zslotW α (j - b) f z θ) ^ 2)
            else 0)

end Work.FTS.GalBasis.cc
