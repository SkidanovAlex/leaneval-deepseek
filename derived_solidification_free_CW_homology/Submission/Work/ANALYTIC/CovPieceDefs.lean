import Mathlib
import Submission.Work.ANALYTIC.HISetup

/-!
# Definitions for the fibres of the cover `cov Y ⟶ Y.toLightCondSet`

This file contains the definitions used in
`Submission/Work/ANALYTIC/covPiece_isLightProfinite.lean`, which proves that the fibre powers of
the sectionwise-split cover `covMap Y : cov Y ⟶ Y.toLightCondSet` of `HISetup.lean` are (light
condensed sets of) light profinite sets.

For a tuple `x : Fin (n+1) → CovIdx Y` we define

* `covPieceMap x i : skel (x i).1 ⟶ Y`, the continuous map classifying the `i`-th piece of the
  cover (`covComp Y (x i)` is the corresponding map into `Y.toLightCondSet`);
* `pieceFibre x`, the closed subspace `{a : ∏ i, skel (x i).1 // ∀ i j, pc i (a i) = pc j (a j)}`
  of the product of the pieces — the topological fibre product over `Y`;
* `pieceSpace x`, this subspace as a `TopCat`;
* `pieceLightProfinite x`, this subspace as a light profinite set;
* `pieceCone x`, the cone over the wide cospan of the pieces with apex `pieceSpace x`.

## Main results

* `isClosed_pieceFibre`, `instCompactSpacePieceFibre`: the fibre is closed in a compact product.
* `pieceProj_comp_covPieceMap`: the cone `pieceCone x` is well defined.
-/

open CategoryTheory Limits LightProfinite LightCondensed

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Work.ANALYTIC

/-- The `i`-th piece of the cover as a continuous map `skel (x i).1 ⟶ Y`.  This is the map
classified by the element `(x i).2` of `Y.toLightCondSet` (Yoneda); its image under
`topCatToLightCondSet` is `covComp Y (x i)`. -/
def covPieceMap {Y : TopCat.{0}} {n : ℕ} (x : Fin (n+1) → CovIdx Y) (i : Fin (n+1)) :
    LightProfinite.toTopCat.obj (skel (x i).1) ⟶ Y :=
  TopCat.ofHom (x i).2

/-- The topological fibre product of the pieces at the tuple `x`: the closed subspace of
`∏ i, skel (x i).1` on which all the maps `covPieceMap x i` to `Y` agree. -/
def pieceFibre {Y : TopCat.{0}} {n : ℕ} (x : Fin (n+1) → CovIdx Y) :
    Set ((i : Fin (n+1)) → ↥(skel (x i).1)) :=
  {a | ∀ i j, covPieceMap x i (a i) = covPieceMap x j (a j)}

/-- The fibre of the cover is closed in the product of the pieces (Hausdorffness of `Y`). -/
lemma isClosed_pieceFibre {Y : TopCat.{0}} [T2Space Y] {n : ℕ} (x : Fin (n+1) → CovIdx Y) :
    IsClosed (pieceFibre x) := by
  have h : pieceFibre x = ⋂ (i : Fin (n+1)) (j : Fin (n+1)),
      {a | covPieceMap x i (a i) = covPieceMap x j (a j)} := by
    ext a
    simp [pieceFibre]
  rw [h]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq ?_ ?_
  · exact ((covPieceMap x i).hom.continuous).comp (continuous_apply i)
  · exact ((covPieceMap x j).hom.continuous).comp (continuous_apply j)

/-- The fibre of the cover is compact: it is closed in the compact product of the pieces. -/
instance instCompactSpacePieceFibre {Y : TopCat.{0}} [T2Space Y] {n : ℕ}
    (x : Fin (n+1) → CovIdx Y) : CompactSpace ↥(pieceFibre x) :=
  isCompact_iff_compactSpace.mp (isClosed_pieceFibre x).isCompact

/-- The fibre of the cover at `x`, as a topological space. -/
def pieceSpace {Y : TopCat.{0}} [T2Space Y] {n : ℕ} (x : Fin (n+1) → CovIdx Y) : TopCat.{0} :=
  TopCat.of ↥(pieceFibre x)

/-- The fibre of the cover at `x`, as a light profinite set: a closed subspace of the finite
product of the light profinite sets `skel (x i).1`. -/
def pieceLightProfinite {Y : TopCat.{0}} [T2Space Y] {n : ℕ} (x : Fin (n+1) → CovIdx Y) :
    LightProfinite.{0} :=
  LightProfinite.of ↥(pieceFibre x)

/-- The `i`-th projection of the fibre of the cover onto its `i`-th piece. -/
def pieceProj {Y : TopCat.{0}} [T2Space Y] {n : ℕ} (x : Fin (n+1) → CovIdx Y) (i : Fin (n+1)) :
    pieceSpace x ⟶ LightProfinite.toTopCat.obj (skel (x i).1) :=
  TopCat.ofHom
    { toFun := fun a => a.1 i
      continuous_toFun := (continuous_apply i).comp continuous_subtype_val }

/-- The canonical map from the fibre of the cover to `Y` (the `i`-th component of the cone,
composed with `covPieceMap x i`). -/
def pieceBase {Y : TopCat.{0}} [T2Space Y] {n : ℕ} (x : Fin (n+1) → CovIdx Y) : pieceSpace x ⟶ Y :=
  pieceProj x ⟨0, Nat.succ_pos n⟩ ≫ covPieceMap x ⟨0, Nat.succ_pos n⟩

/-- The defining property of the fibre: the maps of the pieces to `Y` agree on it. -/
lemma pieceProj_comp_covPieceMap {Y : TopCat.{0}} [T2Space Y] {n : ℕ} (x : Fin (n+1) → CovIdx Y)
    (i j : Fin (n+1)) :
    pieceProj x i ≫ covPieceMap x i = pieceProj x j ≫ covPieceMap x j := by
  apply TopCat.hom_ext
  ext a
  exact a.2 i j

/-- `pieceBase` is the common composite `pieceProj x i ≫ covPieceMap x i`. -/
lemma pieceProj_comp_covPieceMap_base {Y : TopCat.{0}} [T2Space Y] {n : ℕ}
    (x : Fin (n+1) → CovIdx Y) (i : Fin (n+1)) :
    pieceProj x i ≫ covPieceMap x i = pieceBase x :=
  pieceProj_comp_covPieceMap x i ⟨0, Nat.succ_pos n⟩

/-- The cone over the wide cospan of the pieces, with apex the fibre `pieceSpace x`. -/
def pieceCone {Y : TopCat.{0}} [T2Space Y] {n : ℕ} (x : Fin (n+1) → CovIdx Y) :
    WidePullbackCone (fun i : Fin (n+1) => covPieceMap x i) :=
  WidePullbackCone.mk (pieceBase x) (fun i => pieceProj x i)
    (fun i => pieceProj_comp_covPieceMap_base x i)

/-- The canonical map from an arbitrary cone over the wide cospan of the pieces to the fibre
`pieceSpace x`, sending `z` to the tuple `fun i => t.π i z`; the components agree by the cone
condition. -/
def pieceLift {Y : TopCat.{0}} [T2Space Y] {n : ℕ} (x : Fin (n+1) → CovIdx Y)
    (t : WidePullbackCone (fun i : Fin (n+1) => covPieceMap x i)) : t.pt ⟶ pieceSpace x :=
  TopCat.ofHom
    { toFun := fun z =>
        ⟨fun i => t.π i z, by
          have h : ∀ i, covPieceMap x i (t.π i z) = t.base z :=
            fun i => congrArg (fun g => g z) (t.condition i)
          intro i j
          exact (h i).trans (h j).symm⟩
      continuous_toFun := Continuous.subtype_mk (continuous_pi fun i => (t.π i).hom.continuous) _ }

/-- The `pieceLift` maps are the components of `t`. -/
lemma pieceLift_π {Y : TopCat.{0}} [T2Space Y] {n : ℕ} (x : Fin (n+1) → CovIdx Y)
    (t : WidePullbackCone (fun i : Fin (n+1) => covPieceMap x i)) (i : Fin (n+1)) :
    pieceLift x t ≫ pieceProj x i = t.π i := by
  apply TopCat.hom_ext
  rfl

end Work.ANALYTIC
