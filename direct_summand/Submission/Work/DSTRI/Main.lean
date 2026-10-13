import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSTRI.Regime.char_trichotomy

/-!
# DSTRI: the characteristic trichotomy of a local domain (deliverable)

This module contains the deliverable of the subproject `DSTRI`:

`DSMap.area_TRI_proved`, whose type is *definitionally identical* to the frozen

`DSMap.area_TRI` of `Submission/Work/DSMap/Map.lean`

(the identity is machine-checked at the end of this file).

The statement is the paper's case split: a complete regular local ring `A` in the
direct-summand argument is of characteristic `0`, of characteristic a prime `p`, or of mixed
characteristic `(0, p)`; the three branches are then handled by the areas `EQ0`, `EQP` and
`MIX` respectively (see `DSMap.main_dsplit`).

The mathematics is in the area's main result `Work.DSTRI.Regime.char_trichotomy`
(`Submission/Work/DSTRI/Regime/char_trichotomy.lean`), which has this very statement; the
present theorem is the copy under the name the assembly expects.  That main result is proved
from `Work.DSTRI.Regime.regime_trichotomy`, the split of a local domain into the three regimes
`EqualCharZero`, `EqualCharPos`, `MixedChar`; see `Submission/Work/DSTRI/All.lean` for the
whole area.

`Submission.Work.DSMap.Map` is imported here only for the type-identity check below: the proof
of `DSMap.area_TRI_proved` uses nothing from the frozen map, so a caller who cannot import the
frozen map (for instance because it would create an import cycle) can equally use
`Work.DSTRI.Regime.char_trichotomy`, which is the same statement without the dependency.
-/

universe u

open IsLocalRing

namespace DSMap

/-- **TRI** (DSTRI deliverable): characteristic trichotomy for a local domain.  Same type as
the frozen `DSMap.area_TRI`. -/
theorem area_TRI_proved.{a} (R : Type a) [CommRing R] [IsLocalRing R] [IsDomain R] :
    CharZero (ResidueField R) ∨ (∃ p : ℕ, p.Prime ∧ CharP R p) ∨
      (∃ p : ℕ, p.Prime ∧ CharZero R ∧ CharP (ResidueField R) p) :=
  Work.DSTRI.Regime.char_trichotomy R

/-- The type of the deliverable is definitionally identical to the type of the frozen
`DSMap.area_TRI`.  The universe level is made explicit: without it `type_of%` introduces two
distinct level metavariables on the two sides, and `rfl` is not even applicable to
`type_of% @f = type_of% @f` for a fixed `f`. -/
example : type_of% (@area_TRI_proved.{u}) = type_of% (@DSMap.area_TRI.{u}) := rfl

end DSMap
