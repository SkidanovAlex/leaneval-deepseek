import Mathlib
import Submission.Work.ShafarevichKoch.card_VTwoUnramified_mod_squares_Kc

/-!
# `Work.ShafarevichKoch.unrClassTwoTor_surjective`

The restricted Kummer two-descent `unrClassTwoTor M : V^{unr}/Kc^{×2} → Cl(Kc)[2]` of
`card_VTwoUnramified_mod_squares_Kc.lean` is **surjective**: every class of order dividing `2`
in the class group of `Kc = ℚ(√-30030)` is the class of the square root of an element of the
unramified Kummer radical `V^{unr}`.

The map was already proved *injective* there (`unrClassTwoTor_injective`), and both its source
and its target have cardinality `32`:

* `Nat.card (V^{unr}/Kc^{×2}) = 32 = 2 ^ rank₂ Cl(Kc)` (`card_VTwoUnramified_mod_squares_Kc`);
* `Nat.card Cl(Kc)[2] = 32` (`card_KcTwoTorsion`).

An injective self-map of a finite set of cardinality `32` between two finite types of equal
cardinality is surjective (`Finite.injective_iff_surjective_of_equiv`), which gives the result.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower

/-- **The restricted Kummer two-descent onto the `2`-torsion of the class group is surjective.**

Both sides of `unrClassTwoTor M` have `32` elements and the map is injective, so it is bijective. -/
theorem unrClassTwoTor_surjective
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2) :
    Function.Surjective (Work.ShafarevichKoch.unrClassTwoTor M) := by
  haveI hfin : Finite (↥(VTwoUnramified Kc M) ⧸ KcN M) :=
    Finite.of_injective (unrClassTwoTor M) (unrClassTwoTor_injective M)
  haveI : Fintype (↥(VTwoUnramified Kc M) ⧸ KcN M) := Fintype.ofFinite _
  haveI : Fintype KcTwoTorsion := Fintype.ofFinite _
  have hcard :
      Fintype.card (↥(VTwoUnramified Kc M) ⧸ KcN M) = Fintype.card KcTwoTorsion := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      card_VTwoUnramified_mod_squares_Kc M, card_KcTwoTorsion]
  exact (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hcard)).mp
    (unrClassTwoTor_injective M)

end Work.ShafarevichKoch
