/-
Copyright: work module for the Elgindi finite-time singularity project.

# The split of the `SpecialTransport` pairing (f-form)

`HardF α f g` is the sum of the five order-five "all derivatives on `∂_θ g`" terms of the
pairing `(f ∂_θ g, g)_{ℋ⁴}` in the *`f`-form* (no division by `sin(2θ)`), which is the form
in which the integration by parts of `ibp_partial` applies directly.  `EZ`, `EM` and `EC`
are the three remainders: the `D_z`-slots with at least one `D_z`-derivative on `f`, the
mixed slots with at least one derivative on `f`, and the angular commutator corrections.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.STEasy

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- The five order-five terms of the pairing in the `f`-form. -/
def HardF (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.w z) ^ 2 *
    (f z θ * Work.Spaces.pth (Work.Spaces.DzIter 4 g) z θ * Work.Spaces.DzIter 4 g z θ
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
      + f z θ * (Work.Spaces.pth (Work.Spaces.mixed 3 1 g) z θ * Work.Spaces.mixed 3 1 g z θ
              + Work.Spaces.pth (Work.Spaces.mixed 2 2 g) z θ * Work.Spaces.mixed 2 2 g z θ
              + Work.Spaces.pth (Work.Spaces.mixed 1 3 g) z θ * Work.Spaces.mixed 1 3 g z θ
              + Work.Spaces.pth (Work.Spaces.mixed 0 4 g) z θ * Work.Spaces.mixed 0 4 g z θ)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))

/-- The `D_z`-slot remainder. -/
def EZ (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ m ∈ Finset.range 5, ∑ b ∈ Finset.range (m + 1),
    (if m = 4 ∧ b = 0 then 0 else (m.choose b : ℝ)) *
      (Work.Spaces.DzIter b f z θ * Work.Spaces.DzIter (m - b) (Work.Spaces.pth g) z θ
        * Work.Spaces.DzIter m g z θ) * (Work.Spaces.w z) ^ 2
      * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)

/-- The mixed-slot remainder. -/
def EM (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
    if 1 ≤ i ∧ i + j ≤ 4 then
      ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        (if i + j = 4 ∧ a = 0 ∧ b = 0 then 0
          else ((i.choose a : ℝ) * (j.choose b : ℝ))) *
          (Work.Spaces.mixed b a f z θ * Work.Spaces.mixed (j - b) (i - a) (Work.Spaces.pth g) z θ
            * Work.Spaces.mixed j i g z θ) * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
    else 0

/-- The angular commutator correction. -/
def EC (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
    if 1 ≤ i ∧ i + j = 4 then
      f z θ * ((Work.Spaces.mixed j i (Work.Spaces.pth g) z θ
          - Work.Spaces.pth (Work.Spaces.mixed j i g) z θ) * Work.Spaces.mixed j i g z θ)
        * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
    else 0

end Work.FTS.H2
