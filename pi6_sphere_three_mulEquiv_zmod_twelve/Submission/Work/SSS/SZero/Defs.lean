import Mathlib
import Submission.Work.SSS.pieceAlongZero
import Submission.Work.SSS.serreE1EZ

/-!
# Shared vocabulary for the base case `P = 0` of `Work.SSS.serreE1PieceIso_iota`

This file collects the few definitions that both `Submission/Work/SSS/serreE1PieceIsoZero.lean`
and the lemmas delegated for it use.

* `Work.SSS.SZero.castSimp` — the transport of simplices of a simplicial set along an equality of
  degrees `m = n` (`Eq.mp` of `congrArg (fun k => Y _⦋k⦌)`); for the canonical identifications of
  degrees it is reindexing by the corresponding map of the simplex category.
* `Work.SSS.SZero.fibreTrans` — the transport of the singular simplicial set of the fibre along an
  equality of base points `sigmaVert σ = b`, i.e. the map underlying `Work.SSS.fibreConj`.
* `Work.SSS.SZero.fibreIso` — the iso `Sing F_{σ(v₀)} ≅ T_σ` of `Work.SSS.phiAlong`, bundled.
-/

set_option autoImplicit false

namespace Work.SSS.SZero

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial

noncomputable section

/-- **Degree transport of simplices.**  For an equality of degrees `h : m = n`, a simplex
`x : Y _⦋m⦌` is transported to `Y _⦋n⦌` along `congrArg (fun k => Y _⦋k⦌) h`. -/
def castSimp {Y : SSet.{0}} {m n : ℕ} (h : m = n) (x : Y _⦋m⦌) : Y _⦋n⦌ :=
  Eq.mp (congrArg (fun k => Y _⦋k⦌) h) x

/-- **Transport of the fibre of a map along an equality of base points**, as a morphism of
simplicial sets: `Sing F_x ⟶ Sing F_y` for `h : x = y`.  It underlies the chain level
`Work.SSS.fibreConj`. -/
def fibreTrans {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b) :
    Work.SSS.sSing (Work.StemsB.fibre p (Work.SSS.sigmaVert σ)) ⟶
      Work.SSS.sSing (Work.StemsB.fibre p b) :=
  eqToHom (congrArg (fun X => Work.SSS.sSing (Work.StemsB.fibre p X)) h)

/-- **The canonical iso `Sing F_{σ(v₀)} ≅ T_σ`** of `Work.SSS.phiAlong`, bundled as an iso so
that its inverse can be used without re-establishing `IsIso`. -/
def fibreIso {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSS.sSing B) :
    Work.SSS.sSing (Work.StemsB.fibre p (Work.SSS.sigmaVert σ)) ≅
      Work.SSS.pullAlong (Work.SSS.sSingP p) σ :=
  @asIso _ _ _ _ (Work.SSS.phiAlong p σ) (Work.SSS.phiAlong_isIso p σ)

end

end Work.SSS.SZero
