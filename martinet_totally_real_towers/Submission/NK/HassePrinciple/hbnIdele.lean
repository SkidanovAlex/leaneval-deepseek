import Mathlib
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.HassePrinciple.LocalUnitsSub
import Submission.NK.HassePrinciple.IdelesLevel
import Submission.NK.HassePrinciple.IdeleCocycle
import Submission.NK.HassePrinciple.HBNIdeleProof

namespace NK.HassePrinciple

open CategoryTheory Representation
open NK.GlobalCFT
open scoped NumberField

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## The local units as a `Γ_w`-representation

The definitions of this layer (`localUnitsEquiv_mem`, `localUnitsSubRep`, `localUnitsIncl`) now
live in `Submission.NK.HassePrinciple.LocalUnitsSub`, so that the orbit layer could be developed
on top of them without a circular import.
-/

end

set_option maxHeartbeats 1600000 in
/-- **Shapiro's result for the idèles**: the localisation of `H²(Gal(L/K), 𝕀_L)` at the places of
`L` is injective.

Mathematical content: for a finite group `Γ = Gal(L/K)`, the idèle group `𝕀_L` (a *restricted*
product `∏ʳ_w L_wˣ`) is the filtered union of its `Γ`-stable submodules `𝕀_L^S` (idèles that are
local units outside a finite `Γ`-stable set `S` of places), each of which is a product over the
`Γ`-set `Place L` and hence, orbit by orbit, a product of coinduced modules
`Coind_{Γ_w}^Γ (-)` (`Γ_w = MulAction.stabilizer (L ≃ₐ[K] L) w`, the action on `L_wˣ` being
`NK.HassePrinciple.localUnitsEquiv`).  By Shapiro's isomorphism
`H^n(Γ, Coind_{Γ_w}^Γ M) ≅ H^n(Γ_w, M)` (Mathlib: `groupCohomology.coindIso`) the `w`-component of
the localisation `NK.HassePrinciple.ideleLoc K L w` realizes, orbit by orbit, the corresponding
projection, so a class all of whose localisations vanish has every orbit component zero.

The vanishing at the *units* summands of the cofinite part is what the restricted product buys: for
an orbit of places outside the finite set `S` the component is a local unit, and the cohomology of
the local units of a decomposition group vanishes.  (Caveat recorded by the reviewers: `H^n` of a
finite group does *not* commute with arbitrary infinite products in general, so the argument has to
be made on the filtered system of finite `Γ`-stable `S`.) -/
theorem hbnIdele {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] : NK.HassePrinciple.HBNIdele K L :=
  hbnIdele_proof

end NK.HassePrinciple
