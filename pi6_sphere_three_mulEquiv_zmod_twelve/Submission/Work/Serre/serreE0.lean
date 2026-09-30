import Submission.Work.Serre.serreE0OfRange
import Submission.Work.Serre.serreAugmentationZero

/-!
# E0

**`Work.Serre.SerreE0` is proved**: the range form `Work.Serre.serreE0Range` (ADDENDUM 1 (C): the
singular cone construction, in `serreE0Range.lean`) together with the degree-`0` augmentation
`Work.Serre.serreAugmentationZero` (`serreAugmentationZero.lean`) gives the unrestricted statement
via `Work.Serre.serreE0OfRange` (`serreE0OfRange.lean`).
-/

namespace Work.Serre

/-- **E0 (blueprint §1)**: a weakly contractible space is rationally acyclic. -/
theorem serreE0 : SerreE0 := serreE0_of_range serreAugmentationZero

end Work.Serre
