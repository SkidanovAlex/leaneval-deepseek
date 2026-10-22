import Mathlib
import Submission.Work.ANALYTIC.CovPieceDefs

/-!
# The `i`-th piece of the cover, on the topological and on the condensed side

The cover `covMap Y : cov Y ⟶ Y.toLightCondSet` of `Submission/Work/ANALYTIC/HISetup.lean` is
indexed by `CovIdx Y = Σ i : skelι, Y.toLightCondSet(S)`, and the `i`-th piece is the map
`covComp Y (x i)` into `Y.toLightCondSet`.  On the topological side the same index classifies a
continuous map `covPieceMap x i : skel (x i).1 ⟶ Y` (`Submission/Work/ANALYTIC/CovPieceDefs.lean`).

This file identifies the two: the piece of the cover is the image of the continuous map under
`topCatToLightCondSet`, conjugated by the comparison isomorphism
`lightProfiniteToLightCondSetIsoTopCatToLightCondSet`.  Both maps are the one classified by the
element `(x i).2` of `Y.toLightCondSet(S)` (Yoneda), so it suffices to apply `yonedaEquiv` and
compute.

## Main result

* `covComp_eq_eta_covPieceMap`.
-/

open CategoryTheory Limits LightProfinite LightCondensed

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Work.ANALYTIC

/-- **The `i`-th piece of the cover is `topCatToLightCondSet` of `covPieceMap x i`.**

Both sides are maps `lc (skel (x i).1) ⟶ Y.toLightCondSet`.  The right hand side is the composite
of the comparison isomorphism `lightProfiniteToLightCondSet ≅ LightProfinite.toTopCat ⋙
topCatToLightCondSet` applied to `skel (x i).1` with the image under `topCatToLightCondSet` of the
continuous map `covPieceMap x i`; by Yoneda it is the map classified by the element `(x i).2`, which
is by definition `covComp Y (x i)`. -/
theorem covComp_eq_eta_covPieceMap {Y : TopCat.{0}} {n : ℕ} (x : Fin (n+1) → Work.ANALYTIC.CovIdx Y) (i : Fin (n+1)) :
    Work.ANALYTIC.covComp Y (x i) =
      CategoryTheory.CategoryStruct.comp
        (lightProfiniteToLightCondSetIsoTopCatToLightCondSet.hom.app (Work.ANALYTIC.skel (x i).1))
        (topCatToLightCondSet.map (Work.ANALYTIC.covPieceMap x i)) := by
  -- `yonedaEquiv` is a bijection, so it suffices to compare the classified elements.
  apply (coherentTopology LightProfinite.{0}).yonedaEquiv.injective
  -- On the right the composite is sent by `yonedaEquiv` to the section induced by the map.
  rw [GrothendieckTopology.yonedaEquiv_comp]
  -- On the left `yonedaEquiv` inverts the defining equivalence `covComp Y (x i) := …`.
  rw [show (coherentTopology LightProfinite.{0}).yonedaEquiv (covComp Y (x i)) = (x i).2 from by
    rw [covComp]; exact Equiv.apply_symm_apply _ _]
  -- `yonedaEquiv` of a map out of the Yoneda sheaf is evaluation at the identity.
  rw [GrothendieckTopology.yonedaEquiv_apply]
  -- The comparison isomorphism is the identity on underlying continuous maps, and the map induced
  -- by `covPieceMap x i` on sections is composition with it: both sides are `(x i).2`.
  rfl

end Work.ANALYTIC
