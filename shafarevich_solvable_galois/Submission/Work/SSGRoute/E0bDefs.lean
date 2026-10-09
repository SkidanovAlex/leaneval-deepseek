import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.projRes_homologyAddEquiv_extMk
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The E0b isomorphism `Hⁿ(G, A) ≃+ Extⁿ_G(ℤ, A)`

`eCoh`: Mathlib's `groupCohomologyIso` for the bar resolution, composed with
`projRes_homologyAddEquiv_extMk` (the bridge proved in
`Submission/Work/SSGRoute/projRes_homologyAddEquiv_extMk.lean`).  Clause 1 (naturality) and clause 2
(connecting maps) of `Work.SSGRoute.extH_groupCohomology_iso` are statements about this definition.
-/

open CategoryTheory Limits

namespace SSGRoute.PTExt

noncomputable section

/-- **The E0b isomorphism.**  `Hⁿ(G, A) ≃+ Extⁿ_G(ℤ, A)`, built from the bar resolution. -/
noncomputable def eCoh (n : ℕ) (G : Type) [Group G] (A : Rep.{0} Coeff G) :
    groupCohomology A n ≃+ extH A n :=
  (Iso.toLinearEquiv (groupCohomologyIso A n (Rep.barResolution Coeff G))).toAddEquiv.trans
    (Classical.choose (Work.SSGRoute.projRes_homologyAddEquiv_extMk (X := unitRep G) (Y := A)
      (Rep.barResolution Coeff G) n))

end

end SSGRoute.PTExt
