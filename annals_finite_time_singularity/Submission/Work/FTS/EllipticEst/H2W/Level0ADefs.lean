/-
Copyright: work module for the Elgindi finite-time singularity project.

# `H2W.Level0ADefs` — the `A`-datum of the level-`0` elliptic estimate

The lemma `Work.FTS.EllipticEst.H2W.level0ADatum` asks for the level-`0` `η`-weighted elliptic
estimate (the paper's Steps 1–2 of Proposition `prop:H2`), applied to the *twice radially
differentiated* datum

  `A Ψ := z² ∂_z² Ψ = D_z² Ψ − D_z Ψ`      (`z2_pzIter2_eq`),

whose source is

  `G F := D_z² F − D_z F = z² ∂_z² F`,

where `bslOp α Ψ = F` on the open quadrant.  The point of the datum is that `D_z` commutes with
the operator (`Work.FTS.EllipticEst.TT.bslOp_DzIter_eq`), so that `bslOp α (A Ψ) = G F` on the
open quadrant: the `A`-datum is again a solution, and `AeData` (the almost-everywhere class of
`H2W/Ae/Defs.lean`) applies to it once the two a.e. moment conditions are supplied — which they
are, by the moment chain `H2W.PsiSlices.Fstar_DzIter_Psi_ae` / `Fstar_DzIter_F_ae`.

The three abbreviations below are the ones the assembly and the delegated pieces use.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false

/-- The `A`-datum: `A Ψ = z² ∂_z² Ψ` (the twice radially differentiated datum). -/
abbrev Aof (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ

/-- The source of the `A`-datum: `G F = D_z² F − D_z F = z² ∂_z² F`. -/
abbrev Gof (F : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ

@[simp] theorem Aof_apply (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Aof Ψ z θ = z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ := rfl

@[simp] theorem Gof_apply (F : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Gof F z θ = Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ := rfl

end Work.FTS.EllipticEst.H2W
