import Mathlib
import ChallengeDeps

/-!
# DSG1: `SheafOfModules` over a scheme has enough injectives (pinned universe)

`SheafOfModules X.ringCatSheaf` is Grothendieck abelian, hence has enough injectives, but the
module universe of `SheafOfModules` is a free parameter and Mathlib's instances only apply when it
is pinned to the universe of the structure sheaf, i.e. to `X.Modules`.  This file records the
instance at that universe; it is what the `DSMap` vocabulary uses (`DSMap.GammaA` takes
`SheafOfModules X.ringCatSheaf ⥤ ModuleCat A` with the same module universe, and
`AlgebraicGeometry.Scheme.Modules` is exactly `SheafOfModules.{u} X.ringCatSheaf`).
-/

open CategoryTheory AlgebraicGeometry Limits

universe a

namespace Work.DSG1

/-- `SheafOfModules` over a scheme has enough injectives (at the universe of the structure
sheaf). -/
theorem enoughInjectives_sheafOfModules (X : Scheme.{a}) :
    EnoughInjectives (SheafOfModules.{a} X.ringCatSheaf) :=
  inferInstance

end Work.DSG1
