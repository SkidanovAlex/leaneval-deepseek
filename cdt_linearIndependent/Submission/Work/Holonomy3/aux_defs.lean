import Mathlib
import Submission.CDTPlan.Interfaces

/-!
# Light-weight import module for the `auxSeries_injective` development

`Submission.CDTPlan.Interfaces` (`ℚ⟦x⟧`, `PolyIndependent`, `embedVar`, `auxSeries`, …) is all
that the lemmas about `Work.Holonomy3.auxSeries_injective` need from the blueprint, and importing
it alone keeps the dependency closure of those lemmas small.  Colleagues proving pieces of
`Work.Holonomy3.auxSeries_injective` should import this module.
-/
