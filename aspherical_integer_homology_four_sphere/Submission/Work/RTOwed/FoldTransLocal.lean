/-
# The local Möbius model of a fold transition, as one named hypothesis

This file records, as a structure, the **single** analytic statement about the delivered fold charts
`Work.FoldInst.foldChart` which the area `Work.RTOwed` does not prove: the local form of a chart
transition.

For a point `z` of the source of the transition `foldChart j ∘ (foldChart i)⁻¹` of two fold charts,
the transition is, on an open neighbourhood of `z`, the Möbius transformation of a *single* Lorentz
matrix.  Equivalently: the Voronoi chamber decomposition of `X̄ = ZMod 2 × Q̄` is such that the matrix
of the transition — the transported developing matrix of the two pieces — is constant across the
chambers meeting at a point of the transition source.

Everything else about the fold block is proved: the formula on a common Voronoi piece
(`Work.RTOwed.foldTrans_piece`), its twisted form at a point related by a group element
(`Work.RTOwed.foldTrans_piece_twisted`), the Klein-transport computation
(`Work.RTOwed.foldTheta_actTransport`, `Work.RTOwed.foldTheta_actTransport_isLorentz`), the lifting
of a transition point to a pair of pieces (`Work.RTOwed.transPieceLift`), the height bounds
(`Work.RTOwed.foldTheta_height_pos`, `Work.RTOwed.foldChart_height_le`) and the gluing identity of
the developing matrices (`Work.RTOwed.foldDr_ratio_flip`, `Work.RTOwed.foldDr_flipAtSide`).

A proof of `FoldTransLocal.localModel` should combine the last two lists: at a point `z` with piece data
`(r, γ, s)` (`Work.RTOwed.transPieceLift`), the points of a small ball around `z` whose lift lies in
another Voronoi chamber are reached by applying the group element of the crossed wall, which flips
the representative of *both* classes simultaneously; `Work.RTOwed.foldDr_ratio_flip` says that the
ratio of the developing matrices, and hence the transport matrix, is unchanged.

Once `FoldTransLocal` is inhabited, the fold block is unconditional:
`Work.RTOwed.foldAnalyticOf (h : FoldTransLocal) : Work.RTInstance.FoldAnalytic`.
-/
import Mathlib
import Submission.Work.RTOwed.Defs
import Submission.Work.HypModel.mobius_mul

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function Filter Matrix
open scoped Manifold ContDiff Topology Bundle RealInnerProductSpace Matrix
open Bundle

namespace Work.RTOwed

open Work.FoldInst

/-- **The local Möbius model of a fold transition.**  For every point `z` of the source `Trans i j`
of the transition of the fold charts `i` and `j` there is an open neighbourhood `V` of `z` and a
Lorentz matrix `B` such that the transition is `mobius B` on `V ∩ Trans i j`. -/
structure FoldTransLocal where
  /-- The local form of a transition, at every point of its source. -/
  localModel : ∀ (i j : Fin 98) {z : E4}, z ∈ Trans i j →
    ∃ (V : Set E4) (B : Matrix (Fin 5) (Fin 5) ℝ), IsOpen V ∧ z ∈ V ∧
      HypModel.IsLorentzMat B ∧ ∀ z' ∈ V ∩ Trans i j, transMap i j z' = HypModel.mobius B z'

end Work.RTOwed
