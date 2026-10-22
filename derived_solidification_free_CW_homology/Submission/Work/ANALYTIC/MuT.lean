import Submission.Work.ANALYTIC.SolidDual
import Submission.Work.ANALYTIC.exists_muT
import Submission.Work.TOOLKIT.Main

/-!
# The evaluation pairing `μ_T : ℤ[T] ⟶ ℤ■[T]` (AN3)

`Work.ANALYTIC.exists_muT` (module `Submission.Work.ANALYTIC.exists_muT`) proves that for every light
profinite `T` there is a solid-equivalence `ℤ[T] ⟶ ℤ■[T] = ihom(C(T,ℤ)_disc, ℤ)`.  Here we name one
such map `muT T` (by choice) and record that it is a solid-equivalence.  Everything is unconditional:
`ToolkitProp` is proved in area TOOLKIT (`Work.TOOLKIT.toolkit_prop`).
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

namespace Work.ANALYTIC

open _root_.LightCondensed _root_.LightCondensed.Solid

/-- `ToolkitProp` holds (area TOOLKIT). -/
theorem toolkitProp : Submission.Blueprint.ToolkitProp := _root_.Work.TOOLKIT.toolkit_prop

/-- **The evaluation pairing `μ_T : ℤ[T] ⟶ ℤ■[T]`** of REFS/03 §4, chosen so that it is a
solid-equivalence (see `muT_solidEquiv`). -/
noncomputable def muT (T : LightProfinite) :
    (LightCondensed.free (R := ℤ)).obj T.toCondensed ⟶ solidDual T :=
  Classical.choose (exists_muT T toolkitProp)

/-- **AN3 (REFS/03 §4)**: the evaluation pairing `μ_T` is a solid-equivalence. -/
theorem muT_solidEquiv (T : LightProfinite) :
    Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map (muT T)) :=
  Classical.choose_spec (exists_muT T toolkitProp)

end Work.ANALYTIC
