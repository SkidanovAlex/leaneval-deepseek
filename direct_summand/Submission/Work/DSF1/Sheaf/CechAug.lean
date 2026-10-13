import Mathlib
import Submission.Work.DSF1.Sheaf.AcycDefs
import Submission.Work.DSF1.Sheaf.CechSheafRestr
import Submission.Work.DSF1.Sheaf.CechSheafTerm
import Submission.Work.DSF1.Sheaf.SSEBasic

/-!
# The augmentation of the sheaf-level Čech complex

For a scheme `X`, a presheaf `P` of abelian groups and a family `U : ι → X.Opens`, we define the
augmentation

`cechAug U P : restrL P (iSup U) ⟶ cechSheafTerm U P 0`

whose component at an open `W` is the `Pi.lift` of the restrictions
`P ((iSup U) ⊓ W) ⟶ P ((⋂ a, U (x a)) ⊓ W)` along the inclusions `⋂ a, U (x a) ≤ iSup U`.
-/

namespace Work.DSF1.Sheaf

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

universe u

variable {X : AlgebraicGeometry.Scheme.{u}}

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

/-- The inclusion `(⋂ a, U (x a)) ≤ ⨆ i, U i`, for `x` a simplex of the Čech nerve. -/
lemma cechN_obj_le_iSup {ι : Type u} (U : ι → X.Opens) (n : ℕ) (x : (cechN U n).I) :
    (cechN U n).obj x ≤ iSup U :=
  le_trans (leOfHom (Pi.π (U ∘ x) 0)) (le_iSup U (x 0))

end Work.DSF1.Sheaf
