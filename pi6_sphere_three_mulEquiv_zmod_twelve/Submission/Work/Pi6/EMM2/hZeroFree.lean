import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.RatHurewicz.ConnectivityBridge
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.EMM2

open CategoryTheory CategoryTheory.Limits

set_option linter.style.haveILetI false

/-- `H_0` of a space with trivial `π₀` is free: for a space `X` and a point `x` with
`Subsingleton (π₀(X,x))` (equivalently `X` path connected), the zeroth integral singular homology
`H_0(X;ℤ)` is a free `ℤ`-module (of rank one).  Route: Mathlib's `singularHomology₀Iso` identifies
`H_0` with the coproduct of copies of `ℤ` indexed by the path components of the singular simplicial
set of `X`, and that index type is a nonempty subsingleton (`TopCat.zerothHomotopyEquiv`,
`HomotopyGroup.pi0EquivZerothHomotopy`, `pathConnectedSpace_iff_zerothHomotopy`), so the coproduct
is isomorphic to `ℤ` itself (the `IsIso` instance `singularHomology₀ε` under `PathConnectedSpace X`
does this directly); `Module.Free.of_equiv` transfers freeness along the resulting linear
equivalence. -/
theorem hZeroFree {X : Type} [TopologicalSpace X] (x : X)
    (h : Subsingleton (HomotopyGroup (Fin 0) X x)) :
    Module.Free ℤ ↥(Work.Pi6.HR ℤ X 0) := by
  -- Cube-based `π₀`-triviality makes `X` path connected
  -- (`Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero`).
  haveI : PathConnectedSpace X :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero x h
  -- Under path connectedness the degree-`0` augmentation `H_0(X;ℤ) ⟶ ℤ` is an isomorphism
  -- (Mathlib: `TopCat.singularHomology₀ε` is an iso as soon as `X` is path connected).
  have hI : IsIso ((TopCat.of X).singularHomology₀ε (C := ModuleCat ℤ) (ModuleCat.of ℤ ℤ)) :=
    inferInstance
  -- An isomorphism of `ℤ`-modules is a bijective linear map.
  have hbij : Function.Bijective
      (⇑(((TopCat.of X).singularHomology₀ε (C := ModuleCat ℤ) (ModuleCat.of ℤ ℤ)).hom)) :=
    (ConcreteCategory.isIso_iff_bijective _).mp hI
  -- Transport freeness of `ℤ` over itself along the resulting linear equivalence.
  exact Module.Free.of_equiv (LinearEquiv.ofBijective _ hbij).symm

end Work.Pi6.EMM2
