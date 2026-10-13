/-
Copyright: work module for the Elgindi finite-time singularity project.

# Splitting the `D_θ`-transport pairing into its "easy" and "hard" parts

`Transport1` (Elgindi, §`H2`, tex 1099) bounds `|(f D_θ g, g)_{ℋ⁴}|` by
`C/√(γ-1)·|f|_{ℋ⁴}·|g|²_{ℋ⁴}` for the flat pairing `Work.FTS.H2.H4Pair`.

Expanding the pairing integrand `H4PairInt α (f D_θ g) g` by Leibniz leaves exactly five
terms in which five derivatives fall on `g`:

* `f · D_z^4(D_θ g) · D_z^4 g · Whz²` (the `D_z`-slot, weight `sin(2θ)^{-η}`),
* `f · (D_θ D_z^jD_θ^i g) · D_z^jD_θ^i g · Wm²` for `(j,i) = (3,1),(2,2),(1,3),(0,4)`
  (the mixed slots, weight `sin(2θ)^{-γ}`).

These are the terms whose `g`-factor has order `5`; they cannot be estimated by the
weighted `L²`-norm of `g`, and are removed by integrating by parts in `θ`
(`Submission/Work/FTS/H2/T1Hard.lean`).  This file names them and the remainder:

* `T1Hard α f g` is their contribution to the pairing integrand,
* `T1Easy α f g = H4PairInt α (f D_θ g) g - T1Hard α f g` is what remains.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.Defs
import Submission.Work.FTS.H2.Transport1Aux

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

/-- The five order-`5` terms of the pairing integrand `H4PairInt α (f D_θ g) g`: the
`D_z`-slot contribution `f·D_θ(D_z^4 g)·D_z^4 g·sin(2θ)^{-η}` and the four mixed-slot
contributions `f·D_θ(D_z^jD_θ^i g)·D_z^jD_θ^i g·sin(2θ)^{-γ}`, `(j,i) = (3,1),(2,2),(1,3),(0,4)`. -/
def T1Hard (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  f z θ * (Spaces.w z) ^ 2 *
    (Spaces.Dth (Spaces.DzIter 4 g) z θ * Spaces.DzIter 4 g z θ
        * (Real.sin (2 * θ)) ^ (-Spaces.eta)
      + (Spaces.Dth (Spaces.mixed 3 1 g) z θ * Spaces.mixed 3 1 g z θ
        + Spaces.Dth (Spaces.mixed 2 2 g) z θ * Spaces.mixed 2 2 g z θ
        + Spaces.Dth (Spaces.mixed 1 3 g) z θ * Spaces.mixed 1 3 g z θ
        + Spaces.Dth (Spaces.mixed 0 4 g) z θ * Spaces.mixed 0 4 g z θ)
        * (Real.sin (2 * θ)) ^ (-Spaces.gam α))

/-- The "easy" part of the pairing integrand: everything except the five order-five terms
of `T1Hard`. -/
def T1Easy (α : ℝ) (f g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => H4PairInt α (fun z θ => f z θ * Spaces.Dth g z θ) g z θ - T1Hard α f g z θ

/-- Pointwise, the pairing integrand is the sum of its easy and hard parts. -/
theorem H4PairInt_eq_T1Easy_add_T1Hard (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    H4PairInt α (fun z θ => f z θ * Spaces.Dth g z θ) g z θ
      = T1Easy α f g z θ + T1Hard α f g z θ := by
  simp only [T1Easy]
  ring

end Work.FTS.H2
