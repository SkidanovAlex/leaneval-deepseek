import Mathlib
import Submission.Work.ZeroDensity.LogFree.Defs
import Submission.Work.LinnikAreas.FarBoundOfJutilaMontgomery
import Submission.Work.LinnikAreas.FarBoundOfJutilaCrudeWide
import Submission.Work.LinnikAreas.Assembly
import Submission.Work.LinnikAreas.ClassIdentity

/-!
# Wiring Area 2 to the unified log-free estimate (`JUTILA_UNIFIED_LEAD.md`)

`Work.ZeroDensity.LogFree.logFreeNP (3979/5000) 4` — the single log-free non-principal estimate
that the unified chapter `Submission/Work/ZeroDensity/LogFree` is building — implies the crude
wide-range input of Area 2, hence `FarBoundHyp`, hence `Work.LinnikContract.Area2`.

This file identifies the two forms (the chapter's `logFreeNP` is literally the hypothesis of
`Work.LinnikAreas.FamilyZeroDensityJutilaCrudeWide_of_logFreeNP`, through
`famCountNP = Σ_{χ ∈ univ.erase 1} zCount χ` and `zCount = zeroCountIn`) and records the instant
closure term, so that the moment `logFreeNP (3979/5000) 4` is proved `area2` is closed by
composing `Work.LinnikAreas.area2_of_classIdentity ClassIdentity` with
`FarBoundOfJutilaCrudeWide` and the bridges below.

Nothing in `Work.LinnikAreas.area2` imports this file: the deliverable keeps its gap as the
single self-contained statement `FamilyZeroDensityJutilaCrudeWide`, which this file shows to be
equivalent in practice to the chapter's `logFreeNP (3979/5000) 4`.
-/

open DirichletCharacter
open scoped Classical BigOperators

namespace Work.LinnikAreas

/-- The unified estimate, in the chapter's vocabulary, *is* the hypothesis of the Area 2 bridge. -/
theorem FamilyZeroDensityJutilaCrudeWide_of_logFreeNP_def
    (h : Work.ZeroDensity.LogFree.logFreeNP (3979 / 5000) 4) :
    FamilyZeroDensityJutilaCrudeWide :=
  FamilyZeroDensityJutilaCrudeWide_of_logFreeNP (by
    simpa only [Work.ZeroDensity.LogFree.logFreeNP, Work.ZeroDensity.LogFree.famCountNP,
      Work.ZeroDensity.zCount] using h)

/-- **Instant closure of the far-zero bound** from the unified estimate. -/
theorem FarBoundHyp_of_logFreeNP (h : Work.ZeroDensity.LogFree.logFreeNP (3979 / 5000) 4) :
    FarBoundHyp :=
  FarBoundOfJutilaCrudeWide (FamilyZeroDensityJutilaCrudeWide_of_logFreeNP_def h)

/-- **Instant closure of Area 2** from the unified estimate. -/
theorem area2_of_logFreeNP (h : Work.ZeroDensity.LogFree.logFreeNP (3979 / 5000) 4) :
    Work.LinnikContract.Area2 :=
  area2_of_classIdentity ClassIdentity (FarBoundHyp_of_logFreeNP h)

end Work.LinnikAreas
