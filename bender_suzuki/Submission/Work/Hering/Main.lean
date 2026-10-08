import Submission.Blueprint.Interfaces
import Submission.Work.Hering.Reduction
import Submission.Work.Hering.HardCore.no_reduced_config
import Submission.Work.Hering.Perm.appII5
import Submission.Work.Hering.Wagner.wagner_prop
import Submission.Work.Hering.AppVII.appVII

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The area theorem: `HeringProp`

`Work.Hering.Hering` is the theorem delivered by the area: a finite group of even order acting
doubly transitively by conjugation on its involutions has 2-rank one.

It is assembled from
* `Work.Hering.hering_of_noReducedConfig_of` (the reduction §2, with `AppII5Prop`,
  `WagnerProp`, `AppVIIProp`),
* `Work.Hering.no_reduced_config` (the hard core §3–§4, from the abelian case and the named
  non-abelian hypothesis `Work.Hering.NonAbelianCaseProp`).

`Work.Hering.Hering_of_higman` discharges `NonAbelianCaseProp` from the Higman area's
`Work.Higman.HigmanClassProp` together with the App. VIII inputs stated in
`Submission/Work/Hering/AppVIII/Defs.lean` and App. IX (`Work.Hering.AppIXProp`).
-/

set_option autoImplicit false

namespace Work.Hering

open LeanEval.GroupTheory.Defs

/-- The local copy of `Submission.Blueprint.IsSuzukiTwoGroup` used in `HardCore.Defs` agrees with
the blueprint's. -/
theorem isSuzukiTwoGroup_iff (P : Type) [Group P] [Finite P] :
    IsSuzukiTwoGroup P ↔ Submission.Blueprint.IsSuzukiTwoGroup P := Iff.rfl

/-- **Hering's theorem** from the hard core and the three named inputs of the reduction. -/
theorem Hering_of_noReducedConfig (hNoRed : NoReducedConfigProp) (hAppVII : AppVIIProp.{0, 0}) :
    Submission.Blueprint.HeringProp := by
  intro G _ _ hEven hDT h4
  exact hering_of_noReducedConfig_of hNoRed Perm.appII5.{0, 0} Wagner.wagner_prop.{0}
    hAppVII G hEven hDT h4

/-- **Hering's theorem** from the non-abelian case of the hard core. -/
theorem Hering_of_nonAbelian
    (hNonAb : ∀ {G : Type} [Group G] [Finite G], NonAbelianCaseProp (G := G))
    (hAppVII : AppVIIProp.{0, 0}) : Submission.Blueprint.HeringProp :=
  Hering_of_noReducedConfig (no_reduced_config hNonAb) hAppVII

end Work.Hering
