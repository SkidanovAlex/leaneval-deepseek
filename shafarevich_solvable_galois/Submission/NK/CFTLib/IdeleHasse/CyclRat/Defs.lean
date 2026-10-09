import Mathlib
import Submission.NK.GlobalCFT.Place
import Submission.NK.LocalKW.Setup
import Submission.NK.LocalReciprocityLubinTate.Basic
import Submission.NK.NUV2.LC.cylArtinValues
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary definitions for the cyclotomic Artin symbol over `ℚ`

This file collects the basic vocabulary used by
`NK.CFTLib.IdeleHasse.cyclotomicRat_artinSymbol_exists`:

* `placeOfPrime p` — the place of `ℚ` at the rational prime `p`;
* `ratUnit p` — the unit of the completion `ℚ_[p]` given by the rational prime `p`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NK.CFTLib.IdeleHasse

open NK.GlobalCFT

/-- The place of `ℚ` at the rational prime `p`. -/
noncomputable abbrev placeOfPrime (p : ℕ) [Fact p.Prime] : Place ℚ := Place.ofFinite (NK.LocalKW.ratPrime p)

/-- The unit of the completion of `ℚ` at the rational prime `p` given by the rational prime `p`
itself.  (This is the uniformiser used throughout: `N(1 - ζ_{p^n}) = p`.) -/
noncomputable def ratUnit (p : ℕ) [Fact p.Prime] :
    ((NK.LocalKW.ratPrime p).adicCompletion ℚ)ˣ :=
  Units.mk0 (((p : ℚ) : (NK.LocalKW.ratPrime p).adicCompletion ℚ)) (by
    haveI : CharZero ((NK.LocalKW.ratPrime p).adicCompletion ℚ) := inferInstance
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)

@[simp] theorem ratUnit_coe (p : ℕ) [Fact p.Prime] :
    ((ratUnit p : ((NK.LocalKW.ratPrime p).adicCompletion ℚ)ˣ) :
        (NK.LocalKW.ratPrime p).adicCompletion ℚ) =
      (((p : ℚ) : (NK.LocalKW.ratPrime p).adicCompletion ℚ)) := rfl


end NK.CFTLib.IdeleHasse
