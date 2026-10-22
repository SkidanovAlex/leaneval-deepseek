import Mathlib
import ChallengeDeps
import Submission.Blueprint.Interfaces

/-!
# The projection `Y × [0,1] ⟶ Y`

`Work.ANALYTIC.prTop Y` is the projection, mirroring `Submission.Blueprint.i₀`; it is the map whose
solid-equivalence (for Hausdorff `Y`) is the content of `HIProp` (the inclusion `i₀` is a
solid-equivalence because `prTop ≫ i₀ = 𝟙` and `prTop` is one, by 2-out-of-3).
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

namespace Work.ANALYTIC

open _root_.LightCondensed _root_.LightCondensed.Solid

/-- The projection `Y × [0,1] ⟶ Y`. -/
def prTop (Y : TopCat.{0}) : TopCat.of (Y × unitInterval) ⟶ Y :=
  TopCat.ofHom ⟨fun x => x.1, by fun_prop⟩

/-- `prTop` is a retraction of `Submission.Blueprint.i₀`. -/
@[simp] theorem i₀_prTop (Y : TopCat.{0}) :
    Submission.Blueprint.i₀ Y ≫ prTop Y = 𝟙 Y := by
  ext x
  rfl

end Work.ANALYTIC
