import Mathlib
import Submission.Work.SSSR.pieceAlongZero
import Submission.Work.SSSR.serreE1EZ
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false

namespace Work.SSSR.SZero

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial
noncomputable section

/-- **Degree transport of simplices.**  For an equality of degrees `h : m = n`, a simplex
`x : Y _⦋m⦌` is transported to `Y _⦋n⦌` along `congrArg (fun k => Y _⦋k⦌) h`. -/
def castSimp {Y : SSet.{0}} {m n : ℕ} (h : m = n) (x : Y _⦋m⦌) : Y _⦋n⦌ :=
  Eq.mp (congrArg (fun k => Y _⦋k⦌) h) x

/-- **Transport of the fibre of a map along an equality of base points**, as a morphism of
simplicial sets: `Sing F_x ⟶ Sing F_y` for `h : x = y`.  It underlies the chain level
`Work.SSSR.fibreConj`. -/
def fibreTrans {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b) :
    Work.SSSR.sSing (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert σ)) ⟶
      Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b) :=
  eqToHom (congrArg (fun X => Work.SSSR.sSing (Work.SSSR.StemsB.fibre p X)) h)

end

end Work.SSSR.SZero
