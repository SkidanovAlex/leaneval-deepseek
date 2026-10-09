import Mathlib
import Submission.Work.Properness.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Properness

/-- **The trivial embedding problem has a plain solution.**

In the trivial setting `H = Q = 1`, `E = ℤ/2` with `π` and `ρ` the trivial maps
(`Work.Properness.trivialSetup`), the trivial homomorphism `ψ = 1 : 1 →* ℤ/2` is a lift: both
`π ∘ ψ` and `ρ` are homomorphisms into the trivial group `PUnit`, hence equal.  This is the
abstract instance of "a split embedding problem always has the section as a plain solution".

Note that this lift is not proper (`Work.Properness.trivialSetup_no_properLift`), which is why
this example shows that `Setup.HasLift` is strictly weaker than `Setup.HasProperLift`. -/
theorem trivialSetup_hasLift : Work.Properness.trivialSetup.HasLift :=
  ⟨⟨1, by
    show Work.Properness.trivialSetup.π.comp 1 = Work.Properness.trivialSetup.ρ
    ext x
    rfl⟩⟩

end Work.Properness
