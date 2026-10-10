import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Submission.NK.CFTLib.HR.TransferAux.localLevelMap_injective_vanishing
import Submission.Work.SSGRoute.exists_finiteDimensional_normal_fixingSubgroup_le
import Submission.Work.SSGRoute.sha2_hasse.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END


open CategoryTheory

namespace Work.SSGRoute.sha2_hasse

/-- The value of `groupCohomology.cochainsMap₂` at a pair: the `k`-linear map sending a two-cochain
`x` on `H` to the two-cochain `(g₁, g₂) ↦ φ (x (f g₁, f g₂))` on `G`. -/
theorem cochainsMap₂_apply {𝕜 G H : Type} [CommRing 𝕜] [Group G] [Group H]
    {A : Rep 𝕜 H} {B : Rep 𝕜 G} (f : G →* H) (φ : Rep.res f A ⟶ B)
    (x : H × H → A.V) (g : G × G) :
    (⇑(groupCohomology.cochainsMap₂ f φ)) x g = φ.hom (x (f g.1, f g.2)) := rfl

end Work.SSGRoute.sha2_hasse
