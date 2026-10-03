/-
# `Submission.Work.FITop4.AreaShims`

The abbreviations shared by **both** `Submission.Work.FITop4.Areas4` and
`Submission.Work.FITop4.Areas6`.  They used to be declared in each of the two area files, inside
`namespace Work.FITop4`, which made the two files *mutually un-importable*
(`environment already contains 'Work.FITop4.boxN'`).  They are now declared here once, and both area
files import this module, so any module may import `Areas4` and `Areas6` together.

No statement changes: every abbreviation is still the same reducible definition
(`Work.FITop.radN`, `Work.FITop.boxN`, `Work.FIPlan.gnorm`), so all downstream uses elaborate to the
same terms as before.
-/
import Mathlib
import Submission.Work.FITop.Defs
import Submission.Work.FIPlan.Interface

set_option autoImplicit false

namespace Work.FITop4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

abbrev radN := Work.FITop.radN
abbrev boxN := Work.FITop.boxN
abbrev gnorm := Work.FIPlan.gnorm

end

end Work.FITop4
