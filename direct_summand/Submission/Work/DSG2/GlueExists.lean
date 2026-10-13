import Mathlib
import Submission.Work.DSG2.Setup
import Submission.Work.DSG2.Glue
import Submission.Work.DSG2.gluePiExists

/-!
# DSG2: existence of the glued morphism `π : X' ⟶ X`

This is the contents of `Work.DSG2.gluePiExists` (proved in
`Submission/Work/DSG2/gluePiExists.lean`), repackaged as a `Work.DSG2.ChowSetup.GluedPi`.
-/

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace Work.DSG2

namespace ChowSetup

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {f : X ⟶ Spec (.of A)}

theorem nonempty_gluedPi (D : ChowSetup A X f) [IsSeparated f] : Nonempty (GluedPi D) := by
  obtain ⟨g, hg⟩ := gluePiExists D
  exact ⟨⟨g, hg⟩⟩

end ChowSetup

end Work.DSG2
