import Mathlib
import Submission.Work.ANALYTIC.CovPieceDefs

/-!
# The fibre `pieceSpace x` is the wide pullback of the pieces

This file proves `pieceCone_isLimit`: for a Hausdorff topological space `Y` and a tuple
`x : Fin (n+1) → CovIdx Y` of indices of the sectionwise-split cover of
`Submission/Work/ANALYTIC/HISetup.lean`, the cone `pieceCone x` of
`Submission/Work/ANALYTIC/CovPieceDefs.lean` — with apex the fibre
`pieceSpace x = {a : ∏ i, skel (x i).1 // ∀ i j, p i (a i) = p j (a j)}` and projections
`pieceProj x i` — is a limit cone over the wide cospan of the pieces `covPieceMap x i : skel (x i).1
⟶ Y` in `TopCat`.

Since `TopCat` is the category of topological spaces, this is a purely point-set statement: the
subspace `↥(pieceFibre x)` with the subspace topology of the product and the maps
`a ↦ a i` is the wide pullback.  The lift of an arbitrary cone `t` is the map
`z ↦ fun i => t.π i z` (`pieceLift x t`, already in `CovPieceDefs.lean`), which lands in the fibre
by the cone condition of `t`; it is continuous as a `subtype_mk` of a continuous map
(`continuous_pi`).  Uniqueness is pointwise.
-/

open CategoryTheory Limits

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Work.ANALYTIC

variable {Y : TopCat.{0}} [T2Space Y] {n : ℕ} (x : Fin (n+1) → CovIdx Y)

/-- The base of the wide pullback cone `pieceCone x` is `pieceBase x`. -/
lemma pieceCone_base : (pieceCone x).base = pieceBase x := rfl

/-- The `i`-th projection of the wide pullback cone `pieceCone x` is `pieceProj x i`. -/
lemma pieceCone_π (i : Fin (n+1)) : (pieceCone x).π i = pieceProj x i := rfl

/-- The cone `pieceCone x` is a cone over the wide cospan of the pieces, i.e. its base is the
composite of a projection with the corresponding piece map. -/
lemma pieceCone_base_eq (i : Fin (n+1)) :
    (pieceCone x).π i ≫ covPieceMap x i = (pieceCone x).base :=
  pieceProj_comp_covPieceMap_base x i

/-- `pieceLift` really is a morphism of cones: it commutes with the base. -/
lemma pieceLift_base (t : WidePullbackCone (fun i : Fin (n+1) => covPieceMap x i)) :
    pieceLift x t ≫ pieceBase x = t.base := by
  apply TopCat.hom_ext
  ext z
  exact congrArg (fun g : t.pt ⟶ Y => g z) (t.condition ⟨0, Nat.succ_pos n⟩)

/-- **Uniqueness**: a map into `pieceSpace x` whose composites with all the projections
`pieceProj x i` are the components of `t` equals `pieceLift x t`. -/
lemma pieceLift_uniq (t : WidePullbackCone (fun i : Fin (n+1) => covPieceMap x i))
    (m : t.pt ⟶ pieceSpace x)
    (_hbase : m ≫ (pieceCone x).base = t.base)
    (hπ : ∀ i, m ≫ (pieceCone x).π i = t.π i) :
    m = pieceLift x t := by
  apply TopCat.hom_ext
  ext z
  apply Subtype.ext
  funext i
  exact congrArg (fun g => g z) (hπ i)

/-- **The fibre of the cover is the wide pullback of the pieces.**  For a Hausdorff space `Y` and
a tuple `x : Fin (n+1) → CovIdx Y`, the cone `pieceCone x`, whose apex is the fibre
`pieceSpace x` of the pieces `skel (x i).1` over `Y` and whose projections are the restrictions of
the product projections, is a limit cone. -/
theorem pieceCone_isLimit {Y : TopCat.{0}} [T2Space Y] {n : ℕ} (x : Fin (n+1) → Work.ANALYTIC.CovIdx Y) :
    Nonempty (CategoryTheory.Limits.IsLimit (Work.ANALYTIC.pieceCone x)) :=
  ⟨WidePullbackCone.IsLimit.mk (pieceCone x) (fun t => pieceLift x t)
    (fun t => by rw [pieceCone_base]; exact pieceLift_base x t)
    (fun t i => by rw [pieceCone_π]; exact pieceLift_π x t i)
    (fun t m hb hπ => pieceLift_uniq x t m hb hπ)⟩

end Work.ANALYTIC
