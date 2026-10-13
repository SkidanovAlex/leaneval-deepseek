/-
# `N04aN05a_Defs` — the separated form of the two `F_*`-pieces of `N₀`

The two pieces `NP4a α w` and `NP5a α w` of the level-six `N₀`-row are, by the separation
identities `H6Pair6Aux.H6N0Aux.nzN04a_sep` / `nzN05a_sep`, products of an *angular* profile of
`θ` and a *radial* profile of `z`, up to the constant `Cc α = 3α/(2c(α))`:

  `NP4a α w z θ = CC α θ · BB4 w z`,   `NP5a α w z θ = CC5 α θ · BB5 w z`

for `z > 0`, `θ ∈ (0,π/2)`.  This file fixes the vocabulary of that separated form, together
with the two one-variable blocks (`AngBlk`, and the existing `StrongPersist.SlotSum`) into
which the order-`6` separation lemma `L6Aux.HkIntegrandSepLeGen` factorises the `ℋ⁶`-integrand
of a product `(z,θ) ↦ C θ · B z`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FM.Defs
import Submission.Work.FTS.Nonlinear.FstarPkg.DzHzDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux

set_option autoImplicit false

/-- The constant `3α/(2c(α))` of the separation identities.  For `0 < α ≤ 1` one has
`0 < Cc α ≤ 15`. -/
abbrev Cc (α : ℝ) : ℝ := 3 * α / (2 * Work.Spaces.c α)

/-- The angular profile of the separated form of `NP4a`: `Cc α · Γ(θ)·q(θ)`. -/
abbrev CC (α : ℝ) : ℝ → ℝ :=
  fun θ => Cc α * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ)

/-- The angular profile of the separated form of `NP5a`: `-Cc α · Γ(θ)·q(θ)`. -/
abbrev CC5 (α : ℝ) : ℝ → ℝ :=
  fun θ => -(Cc α) * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ)

/-- The angular block of the order-`6` separation bound: the `η`-weighted square of `C` plus the
`γ`-weighted squares of its `D_θ`-jets of orders `1..6`.  This is the first factor produced by
`L6Aux.HkIntegrandSepLeGen` at `k = 6`. -/
abbrev AngBlk (α : ℝ) (C : ℝ → ℝ) : ℝ → ℝ := fun θ =>
  (C θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    + ∑ i ∈ Finset.range 7,
        (if 1 ≤ i then (Work.Spaces.dthU^[i] C θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)

/-- The radial profile of the separated form of `NP4a`: `F_*(z)·L₁₂(w)(z)`. -/
abbrev BB4 (w : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => Work.FM.Fstar z * Work.Construction.L12 w z

/-- The radial profile of the separated form of `NP5a`: `H(z)·L₁₂(w)(z)`, where
`H = 2z(1-z)/(1+z)³` is the radial factor of `D_zF_*`. -/
abbrev BB5 (w : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => Work.FTS.Nonlinear.FstarPkg.Hz z * Work.Construction.L12 w z

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux
