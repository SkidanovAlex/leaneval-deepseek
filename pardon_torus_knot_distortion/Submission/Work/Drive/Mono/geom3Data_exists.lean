import Mathlib
import Submission.Work.Drive.Mono.Geom3Defs
import Submission.Work.Drive.Mono.g3Wrapper
import Submission.Work.Drive.Mono.g3OneEvAE
import Submission.Work.Drive.Mono.g3Producer

/-!
# The target: the `BoxGenE` data producer of the third package

The target is the fixed statement `Work.Drive.Mono.geom3Data_exists :
Work.Drive.Mono.Geom3DataExists`.

The almost-everywhere bookkeeping of the target is *discharged* in
`Submission/Work/Drive/Mono/g3Wrapper.lean`, whose `Work.Drive.Mono.geom3Data_exists_of_atU` proves

  `Geom3DataExists`   from   `(∀ᵐ u, G3OneEv ψ s u c σ)` and
  `hAtU : at every cutting level carrying the pointwise facts Work.Drive.Mono.G3Pointwise, one can
  produce Work.Drive.Mono.Geom3Data`.

The first ingredient is `Work.Drive.Mono.g3_ae_oneEv`
(`Submission/Work/Drive/Mono/g3OneEvAE.lean`), the a.e.-`u` one-event slice nullity on a countable
family of directions (from `Work.Drive.Mono.ae_oneEvBad_slice_null`), and the second is the
single-level producer `Work.Drive.Mono.geom3DataAtU_exists`
(`Submission/Work/Drive/Mono/g3Producer.lean`), the composition of the `Q`-provenance witness
`Work.Drive.Mono.geom3_witnessData_Q` and the assembly `Work.Drive.Mono.g3_assembly` (with
`Work.Drive.Mono.edgeFreeBox_of_margin` for the `EdgeFree` clause and
`Work.Drive.Mono.g3_tripleBad_null` for the twentieth conjunct of `Work.Drive.Mono.Geom2Data`).
-/

namespace Work.Drive.Mono

theorem geom3Data_exists : Work.Drive.Mono.Geom3DataExists :=
  Work.Drive.Mono.geom3Data_exists_of_atU
    (fun ψ s c σ => Work.Drive.Mono.g3_ae_oneEv ψ s c σ)
    Work.Drive.Mono.geom3DataAtU_exists

end Work.Drive.Mono
