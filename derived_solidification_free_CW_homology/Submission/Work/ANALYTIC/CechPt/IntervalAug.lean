import Mathlib
import ChallengeDeps
import Submission.Work.ANALYTIC.Basic

/-!
# The augmentation of the interval `ℤ[[0,1]] ⟶ ℤ`

The map induced by the terminal map `[0,1] ⟶ ∗` on free light condensed abelian groups.  This is
the map whose solid-equivalence is the base case `Work.ANALYTIC.profinite_HI_pt` of homotopy
invariance; it is recorded here (in a module with no other dependencies) so that statements about
the Čech resolution of the interval can refer to it.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.ANALYTIC.CechPt

/-- The point, as a topological space. -/
abbrev ptTopC : TopCat.{0} := LightProfinite.toTopCat.obj (LightProfinite.of PUnit.{1})

/-- The unique map `[0,1] ⟶ ∗`. -/
def termIC : TopCat.of unitInterval ⟶ ptTopC :=
  TopCat.ofHom ⟨fun _ => (PUnit.unit : ↥ptTopC), continuous_const⟩

/-- **The augmentation of the interval**: `ℤ[[0,1]] ⟶ ℤ[∗]`. -/
abbrev intervalAug :
    freeLightCondAbOfTopFunctor.obj (TopCat.of unitInterval) ⟶
      freeLightCondAbOfTopFunctor.obj ptTopC :=
  freeLightCondAbOfTopFunctor.map termIC

end Work.ANALYTIC.CechPt
