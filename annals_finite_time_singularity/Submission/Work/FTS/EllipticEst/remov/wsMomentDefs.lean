/-
Copyright: work module for the Elgindi finite-time singularity project.

# Definitions for the angular-moment chain `remov.wsMomentChain`

The target `Work.FTS.EllipticEst.remov.wsMomentChain` proves that for a datum
`h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ` (`k ≥ 1`) the angular moments
`F_*(D_z^j Ψ) = ∫_θ D_z^j Ψ(z,θ) sinθcos²θ dθ` vanish for `j ≤ 2` and every `z > 0`.

The only analytic input is a family of one-dimensional (`θ`-slice) energy bounds for the
radial iterates `D_z^j Ψ` (`j ≤ 3`), which are *not* directly in the hypothesis class: the
class supplies `ℋ^k`-membership (= weighted `L²`-honesty) only of `F = bslOp α Ψ`,
of `z²∂_zzΨ` and of `∂_θθΨ`.  The bridge is the slice Poincaré inequality of
`remov.wsAux` (`ws_slice_pointwise_le`): the `θ`-energy of a slice `v` is controlled by the
`θ`-energy of `v''`, and the second `θ`-derivative of a radial iterate is again a radial
iterate of `∂_θθΨ`.  Concretely, all the energies of the iterates are dominated by the four
`θ`-energies collected in `Eref` below, which are `L¹` in the radial variable by
`ws_thetaE_integrable`.

This module (`remov.wsMomentDefs`) contains only that vocabulary, so that the auxiliary
modules can state their lemmas about it.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Linarith.Frontend
import Submission.Work.FTS.EllipticEst.remov.wsAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

/-- **The reference `θ`-energy of a datum `Ψ`.**  The sum of the four `sEta`-weighted
`θ`-energies that the weak class controls: those of `∂_θθΨ`, of `D_z∂_θθΨ`, of `z²∂_zzΨ`
and of `D_z(z²∂_zzΨ)`.  Every `θ`-energy `thetaE (D_z^j Ψ)` with `1 ≤ j ≤ 3` is bounded on a
compact radial interval by a constant times `1 + Eref Ψ`, and `Eref Ψ` is locally integrable
— this is `remov.sliceEnergyBounds`. -/
def Eref (Ψ : ℝ → ℝ → ℝ) (s : ℝ) : ℝ :=
  thetaE (Work.Spaces.pthIter 2 Ψ) s
    + thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s
    + thetaE (fun u θ => u ^ 2 * Work.Spaces.pzIter 2 Ψ u θ) s
    + thetaE (Work.Spaces.DzIter 1 (fun u θ => u ^ 2 * Work.Spaces.pzIter 2 Ψ u θ)) s

theorem Eref_nonneg (Ψ : ℝ → ℝ → ℝ) (s : ℝ) : 0 ≤ Eref Ψ s := by
  unfold Eref
  have h1 := thetaE_nonneg (Work.Spaces.pthIter 2 Ψ) s
  have h2 := thetaE_nonneg (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s
  have h3 := thetaE_nonneg (fun u θ => u ^ 2 * Work.Spaces.pzIter 2 Ψ u θ) s
  have h4 := thetaE_nonneg (Work.Spaces.DzIter 1 (fun u θ => u ^ 2 * Work.Spaces.pzIter 2 Ψ u θ)) s
  linarith

end Work.FTS.EllipticEst.remov
