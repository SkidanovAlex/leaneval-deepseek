import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSG8Escape.class_field_data_ssg8
import Submission.Work.SSGRoute.ZConstruction.P2CoreTwin
import Submission.Work.SSGRoute.ZConstruction.ZDataGeneral
import Submission.Work.SSGRoute.ZDataTwo.mu2ThreeHalves
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `p = 2` one-dimensional gate from the `ZDataTwo` lane's live Kummer core

The `p = 2` half of `Work.SSGRoute.z_data_general` used to be wired to
`Work.SSGRoute.shafarevich_z_data_two` (`shafarevich_z_data_two.lean`), i.e. to the statement
`Work.SSGRoute.shafarevich_z_data_two_kummerCore` --- the single `sorry` of that (229 kB) file.

The **live** route of the `ZDataTwo` lane is the file
`Submission/Work/SSGRoute/ZDataTwo/shafarevichZDataTwoKummerCoreH.lean`, where

  `Work.SSGRoute.ZDataTwo.shafarevichZDataTwoKummerCoreH`

has the *same* statement as `shafarevich_z_data_two_kummerCore` and is *proved* --- from the escape
realisation `Work.SSGRoute.ZDataTwo.mu2EscapeRealisationH` and the "three halves" core
`Work.SSGRoute.ZDataTwo.mu2ThreeHalves` (the `p = 2` analogue of the odd lane's chain, and the
deepest statement of the `p = 2` route).

This file wires the `p = 2` case to that route: `isMupZData_of_kummerCoreTwo` is
`Work.SSGRoute.IsMupZData 2 k Ω K` from

* `Work.SSGRoute.shafarevich_z_data_two_of_kummerCore` (proved) --- the reduction of the general
  one-dimensional coefficient module to the Kummer core, and
* `Work.SSGRoute.ZDataTwo.shafarevichZDataTwoKummerCoreH` (proved from `mu2ThreeHalves`) ---
  instantiated at every admissible datum.

Consequently the node `Work.SSGRoute.shafarevich_z_construction` (whose `p = 2` branch,
`ZConstruction/ZDataFinal.lean`, uses this gate) is unblocked as soon as the `ZDataTwo` lane's
`mu2ThreeHalves` lands, with no dependence on the `sorry` of `shafarevich_z_data_two.lean`
(that file's `sorry` is the same statement, so either route closing also closes the other).
-/

set_option linter.unusedVariables false

open scoped Pointwise

namespace Work.SSGRoute

/-- **The one-dimensional gate `Work.SSGRoute.IsMupZData` at `p = 2`, from the `ZDataTwo` lane's
Kummer core.**  Same conversion of "additive on `G_K`" into the `1`-cocycle identity as
`Work.SSGRoute.isMupZData_of_core_two` (`ZConstruction/ZDataGeneral.lean`). -/
theorem isMupZData_of_kummerCoreTwo (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [Fintype (K ≃ₐ[k] K)] (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K) :
    IsMupZData 2 k Ω K := by
  intro E _instE _instMod _instAct _instSMC _instFin h1 Λ _instΛf _instΛg hKΛ S hSfin hSdisj
    hSram y hy hyc hyS hyT hy0 hyinf
  haveI : IsAlgClosed Ω := (inferInstance : IsAlgClosure k Ω).isAlgClosed
  obtain ⟨z, hcoc, hloc, h3, h4, h5, h6⟩ :=
    shafarevich_z_data_two_of_kummerCore k Ω K Λ hKΛ ζ hζ hζK E h1 S hSfin hSdisj hSram y hy hyc
      hyS hyT hy0 hyinf
      (fun y' hy' hyc' hyS' hyT' hy0' hyinf' =>
        -- wired to the `NodeS37` twin of the `p = 2` three-halves recursion (see
        -- `ZConstruction/P2CoreTwin.lean`): the node then depends on the *live* frontier node
        -- `ZDataTwo.TwoRec.claimOfPreTwo_diagonal` instead of the stale `sorry` of
        -- `ZDataTwo.mu2ThreeHalves`.
        ZConstruction.shafarevichZDataTwoKummerCoreH_twin k Ω K Λ hKΛ ζ hζ hζK S hSfin hSdisj
          hSram y' hy' hyc' hyS' hyT' hy0' hyinf')
  exact ⟨z, (isCocycleOn_fixingSubgroup_iff_additive z).mp hcoc, hloc, h3, h4, h5, h6⟩

end Work.SSGRoute
