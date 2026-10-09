import Mathlib
import Submission.Work.Properness.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.Properness

/-- In `trivialSetup` the group `H` is `PUnit`, hence a subsingleton; recorded as a named theorem
because `Setup.H` is a structure projection and instance search does not unfold it. -/
theorem trivialSetup_subsingleton_H : Subsingleton Work.Properness.trivialSetup.H :=
  inferInstanceAs (Subsingleton PUnit)

/-- **No lift of `trivialSetup` is proper.**  The group `H` is trivial, so the image of any
homomorphism `H →* ℤ/2` is a singleton, while `E = ℤ/2` has more than one element; hence no lift
is surjective, i.e. `trivialSetup` has no proper solution. -/
theorem trivialSetup_no_properLift : ¬ Work.Properness.trivialSetup.HasProperLift := by
  rintro ⟨ψ, hψ⟩
  haveI : Subsingleton Work.Properness.trivialSetup.H := trivialSetup_subsingleton_H
  haveI : Subsingleton (Multiplicative (ZMod 2)) := hψ.subsingleton
  have h : Multiplicative.ofAdd (0 : ZMod 2) = Multiplicative.ofAdd (1 : ZMod 2) :=
    Subsingleton.elim _ _
  exact absurd (Multiplicative.ofAdd.injective h) (by decide)

end Work.Properness
