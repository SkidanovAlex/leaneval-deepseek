/-
# `Submission/Work/FTS/StrongEps/L12Sub4/Defs.lean`

Vocabulary for the level-`4` mollifier error of the zero mode `L₁₂(·)(0)`
(`Submission/Work/FTS/StrongEps/L12_Jeps_sub_le4_proof.lean`).

The value `L₁₂(h)(0)` is a *weighted average* of `h` over the self-similar quadrant,

  `L₁₂(h)(0) = ∫_{r>0} ∫_{θ∈Iθ} K(θ) h(r,θ)/r  dθ dr`,

with the weight `K(θ)/r` which factorises as `(1/r) · K(θ)`.  In the log coordinates
`ζ = log tan θ` the angular weight becomes the *single* function

  `Glw ζ = κ(ζ) · K(arctan (e^ζ))`,   `κ ζ = (arctan ∘ exp)'(ζ) = e^ζ/(1 + e^{2ζ})`,

i.e. the density of the push-forward of `K(θ) dθ` under `θ ↦ arctan (e^ζ)`
(`HkSqAux.kappa` is exactly this derivative).  Consequently, for
`h̃(s,ζ) = h (e^s) (arctan (e^ζ))`,

  `L₁₂(h)(0) = ∫_s ∫_ζ Glw ζ · h̃(s,ζ)  ds dζ`,

and the shift of the mollifier in the `ζ`-direction becomes a *translation* of the
`ζ`-independent weight; this is what makes the level-`4` estimate hold (the weight
difference gains a factor `ε` while the profile enters only through its `ℋ⁴`-size).

This file only fixes the vocabulary; the estimates are in the sibling modules.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.HkSqAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.StrongEps.L12Sub4

/-- The angular weight of `L₁₂(·)(0)` in the log coordinate `ζ = log tan θ`:
`Glw ζ = κ(ζ) · K(arctan (e^ζ))` with `κ = (arctan ∘ exp)'`. -/
def Glw (ζ : ℝ) : ℝ :=
  Work.FTS.StrongEps.HkSqAux.kappa ζ * Work.Spaces.K (Real.arctan (Real.exp ζ))

/-- The pull-back `h̃(s,ζ) = h (e^s) (arctan (e^ζ))` of a profile to the log coordinates. -/
def logF (h : ℝ → ℝ → ℝ) (s ζ : ℝ) : ℝ := h (Real.exp s) (Real.arctan (Real.exp ζ))

/-- The `ζ`-marginal of the mollifier against the weight: `Khat ζ = ∫ p, Jker p · Glw (ζ + p.2)`. -/
def Khat (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (ζ : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p * Glw (ζ + p.2)

/-- `L₁₂(h)(0)` as the double integral over the quadrant, by unfolding the definitions. -/
theorem L12_zero_eq_double (h : ℝ → ℝ → ℝ) :
    Work.Construction.L12 h 0
      = ∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * h z θ / z := rfl

end Work.FTS.StrongEps.L12Sub4
