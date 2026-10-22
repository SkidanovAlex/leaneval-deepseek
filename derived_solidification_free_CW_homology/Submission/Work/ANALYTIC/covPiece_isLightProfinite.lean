import Mathlib
import Submission.Work.ANALYTIC.HISetup
import Submission.Work.ANALYTIC.CovPieceDefs
import Submission.Work.ANALYTIC.pieceCone_isLimit
import Submission.Work.ANALYTIC.covComp_eq_eta_covPieceMap

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-! ## Auxiliary facts about `WidePullbackShape.wideCospan` -/

/-- The value of `wideCospan` on the `some` objects. -/
lemma wideCospan_obj_some {C : Type*} [Category C] {J : Type} (B : C) (objs : J → C)
    (arrows : ∀ j : J, objs j ⟶ B) (j : J) :
    (WidePullbackShape.wideCospan B objs arrows).obj (some j) = objs j := rfl

/-- The value of `wideCospan` on the terminal arrows. -/
lemma wideCospan_map_term {C : Type*} [Category C] {J : Type} (B : C) (objs : J → C)
    (arrows : ∀ j : J, objs j ⟶ B) (j : J) :
    (WidePullbackShape.wideCospan B objs arrows).map (WidePullbackShape.Hom.term j) = arrows j :=
  rfl

/-! ## The diagrams -/

/-- The diagram in `LightCondSet` whose limit is the `(n+1)`-fold fibre power of the cover at
`x`: the wide cospan of the pieces `lc (skel (x i).1)` over `Y.toLightCondSet`. -/
abbrev covPieceDiagram {Y : TopCat.{0}} {n : ℕ} (x : Fin (n+1) → CovIdx Y) :
    WidePullbackShape (Fin (n+1)) ⥤ LightCondSet.{0} :=
  WidePullbackShape.wideCospan Y.toLightCondSet
    (fun i => lightProfiniteToLightCondSet.obj (skel (x i).1)) (fun i => covComp Y (x i))

/-- The same diagram on the topological side: the wide cospan of the pieces `skel (x i).1` over
`Y`, with structure maps `covPieceMap x i`. -/
abbrev covPieceTopDiagram {Y : TopCat.{0}} {n : ℕ} (x : Fin (n+1) → CovIdx Y) :
    WidePullbackShape (Fin (n+1)) ⥤ TopCat.{0} :=
  WidePullbackShape.wideCospan Y (fun i => LightProfinite.toTopCat.obj (skel (x i).1))
    (fun i => covPieceMap x i)

/-! ## The comparison of the two diagrams -/

/-- The `LightCondSet` diagram of the pieces is the image under `topCatToLightCondSet` of the
`TopCat` diagram of the pieces.  Its `i`-th component is the comparison isomorphism
`lightProfiniteToLightCondSetIsoTopCatToLightCondSet`, and its compatibility with the structure
maps is `Work.ANALYTIC.covComp_eq_eta_covPieceMap` (proved in
`Submission/Work/ANALYTIC/covComp_eq_eta_covPieceMap.lean`). -/
def covPieceDiagramIso {Y : TopCat.{0}} {n : ℕ} (x : Fin (n+1) → CovIdx Y) :
    covPieceDiagram x ≅ covPieceTopDiagram x ⋙ topCatToLightCondSet.{0} :=
  WidePullbackShape.functorExt (Iso.refl _)
    (fun i => lightProfiniteToLightCondSetIsoTopCatToLightCondSet.app (skel (x i).1))
    (fun i => by
      simp only [covPieceDiagram, covPieceTopDiagram, Functor.comp_map, wideCospan_map_term,
        Iso.refl_hom, Category.comp_id, Iso.app_hom, covComp_eq_eta_covPieceMap x i])

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed in
/-- **The fibre powers of the cover are (coproducts of) light profinite sets.**  Let
`covMap Y : cov Y ⟶ Y.toLightCondSet` be the sectionwise-split cover of
`Submission/Work/ANALYTIC/HISetup.lean`, with `cov Y = ∐_{y : CovIdx Y} lc (skel y.1)` and the
`y`-th piece mapped to `Y.toLightCondSet` by `covComp Y y`.  Then for every tuple
`x : Fin (n+1) → CovIdx Y` (at least one factor; the `n = 0` case of an empty tuple is false, since
then the wide pullback is `Y.toLightCondSet` itself) the wide pullback

  `widePullback Y.toLightCondSet (fun i => lc (skel (x i).1)) (fun i => covComp Y (x i))`

— the `(n+1)`-fold fibre power of the cover at `x` — is isomorphic to `lc S` for some light
profinite set `S`.

The point is that Hausdorffness of `Y` makes fibre products over `Y` closed in the product: the
above is the light condensed set of the closed subspace
`{a : ∏_i skel (x i).1 // ∀ i j, p i (a i) = p j (a j)}` of a finite product of light profinite
sets, where `p i` is the continuous map `skel (x i).1 ⟶ Y` corresponding to `covComp Y (x i)`
(Yoneda: `Y.toLightCondSet` is the sheaf of continuous maps into `Y`).  A closed subspace of a
light profinite set is light profinite (`LightProfinite.of` on the subtype: compact, Hausdorff,
totally disconnected, second countable are all inherited).  The identification of the wide pullback
with `lc S` can be obtained from the adjunction `LightCondSet.lightCondSetToTopCat ⊣
topCatToLightCondSet` plus `WidePullback.hom_ext`, or from `topCatToLightCondSet` preserving limits
(it is a right adjoint) together with `lightProfiniteToLightCondSet ≅ LightProfinite.toTopCat ⋙
topCatToLightCondSet`. -/
theorem covPiece_isLightProfinite (Y : TopCat.{0}) [T2Space Y] (n : ℕ)
    (x : Fin (n+1) → Work.ANALYTIC.CovIdx Y) :
    ∃ S : LightProfinite.{0}, Nonempty (Limits.widePullback Y.toLightCondSet
      (fun i : Fin (n+1) => lightProfiniteToLightCondSet.obj (Work.ANALYTIC.skel (x i).1))
      (fun i => Work.ANALYTIC.covComp Y (x i)) ≅ lightProfiniteToLightCondSet.obj S) := by
  haveI : Functor.IsRightAdjoint topCatToLightCondSet.{0} :=
    LightCondSet.topCatAdjunction.isRightAdjoint
  haveI : PreservesLimits topCatToLightCondSet.{0} := inferInstance
  refine ⟨pieceLightProfinite x, ⟨?_⟩⟩
  -- `topCatToLightCondSet` is a right adjoint, hence preserves the wide pullback.
  have h1 : limit (covPieceDiagram x) ≅ limit (covPieceTopDiagram x ⋙ topCatToLightCondSet.{0}) :=
    HasLimit.isoOfNatIso (covPieceDiagramIso x)
  have h2 : limit (covPieceTopDiagram x ⋙ topCatToLightCondSet.{0}) ≅
      topCatToLightCondSet.obj (limit (covPieceTopDiagram x)) :=
    limit.isoLimitCone
      ⟨topCatToLightCondSet.mapCone (limit.cone (covPieceTopDiagram x)),
        isLimitOfPreserves topCatToLightCondSet (limit.isLimit (covPieceTopDiagram x))⟩
  -- the wide pullback over `Y` is the closed subspace of the product of the pieces.
  have h3 : limit (covPieceTopDiagram x) ≅ pieceSpace x :=
    limit.isoLimitCone ⟨pieceCone x, (pieceCone_isLimit x).some⟩
  -- the closed subspace is a light profinite space.
  have h4 : topCatToLightCondSet.obj (pieceSpace x) ≅
      lightProfiniteToLightCondSet.obj (pieceLightProfinite x) :=
    (lightProfiniteToLightCondSetIsoTopCatToLightCondSet.app (pieceLightProfinite x)).symm
  exact h1.trans (h2.trans ((topCatToLightCondSet.mapIso h3).trans h4))

end

end Work.ANALYTIC
