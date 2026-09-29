import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Kernel.Raw
import Submission.Work.Kernel.consV
import Submission.Work.Kernel.unconsV
import Submission.Work.Kernel.ifZero
import Submission.Work.Kernel.ifNil
import Submission.Work.Kernel.dropValue
import Submission.Work.Kernel.swap
import Submission.Work.Kernel.loopV2
import Submission.Work.Kernel.dup
import Submission.Work.Kernel.roll
import Submission.Work.Kernel.pick
import Submission.Work.Kernel.zipWith
import Submission.Work.Kernel.mapList
import Submission.Work.Kernel.foldList

/-!
# Kernel: `HvdH.KernelLib` (area Kernel)

The bundle of generic value-stack words of `Submission/HvdH/Interfaces.lean` (v2/v3), assembled from

* the raw `Eval`/`WordR` toolkit `Submission/Work/Kernel/Raw.lean`
  (`WordR_seq`, `WordR_conseq`, `WordR_skip`, `WordR_self`, `kernelLib_pushVal`),
* `consV` / `unconsV` / `ifZero` / `ifNil` (single-glyph cells and flag tests),
* `dropValue` / `swap` / `loopV2` (marker-based value movers) and, once they land,
* `dup` / `pick` / `roll` / `mapList` / `zipWith` / `foldList`.

Note: `Submission/Work/Kernel/loopRefute.lean` refutes the *v1* text of the `loop` field
(`m * (c + K) + K`, false at `m = 0`); it is a historical record and is **not** imported here.
-/

set_option autoImplicit false

namespace Work.Kernel

open HvdH

/-- Generic value-stack words and laws of StackLang (the `KernelLib` bundle of the interface). -/
theorem kernelLib : HvdH.KernelLib :=
  { seq := fun main p q P Q C P' Q' C' B hp hq hmid =>
      @WordR_seq main p q P Q C P' Q' C' B hp hq hmid
    conseq := fun main p P P' Q Q' C C' h hP hQ hC =>
      @WordR_conseq main p P P' Q Q' C C' h hP hQ hC
    skip := WordR_skip
    selfLaw := fun main P Q C h => @WordR_self main P Q C h
    dup := dup
    drop := dropValue
    swap := swap
    pick := pick
    roll := roll
    pushVal := kernelLib_pushVal
    consV := consV
    unconsV := unconsV
    ifZero := ifZero
    ifNil := ifNil
    mapList := mapList
    zipWith := zipWith
    foldList := foldList
    loop := loopV2 }

end Work.Kernel
