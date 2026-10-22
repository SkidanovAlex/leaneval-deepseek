/-
AREA RESOL — the closure properties of the class of solid-cofibrant complexes, assembled.

This file assembles the structure `Work.RESOL.CofibrantClosure` (defined in `RESOL/Basic.lean`)
from the four separate closure statements, each proved in its own module:

* `iso`   : `RESOL/solidCofibrantH_of_iso.lean`
* `shift` : `RESOL/solidCofibrantH_shift.lean`
* `cone`  : `RESOL/solidCofibrantH_of_distinguishedTriangle.lean`
* `sigma` : `RESOL/solidCofibrant_sigma.lean`

The bundled structure is what the construction of functorial resolutions consumes
(`RESOL/hasBoundedResolution.lean`, `RESOL/hasFunctorialResolution_of_bounded.lean`).
-/
import Submission.Work.RESOL.Basic
import Submission.Work.RESOL.solidCofibrantH_of_iso
import Submission.Work.RESOL.solidCofibrantH_shift
import Submission.Work.RESOL.solidCofibrantH_of_distinguishedTriangle
import Submission.Work.RESOL.solidCofibrant_sigma

noncomputable section

namespace Work.RESOL

/-- **B4**: solid-cofibrant complexes are closed under isomorphisms in `K(LightCondAb)`, shifts,
mapping cones (i.e. the third object of a distinguished triangle whose first two objects have all
shifts solid-cofibrant) and small coproducts. -/
theorem cofibrantClosure : CofibrantClosure where
  iso := solidCofibrantH_of_iso
  shift := fun n K h => solidCofibrantH_shift K n h
  cone := solidCofibrantH_of_distinguishedTriangle
  sigma := solidCofibrant_sigma

end Work.RESOL
