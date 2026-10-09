/-
# Gateway: the library surface the `sha2_hasse` local-condition lemmas are stated in

Re-exports the (already proved) parts of the library that the statements of the
`Work.SSGRoute.sha2_hasse` local-condition lemmas mention, so that the statements can be
elaborated in a small environment.
-/
import Submission.Work.SSGRoute.sha2_hasse.Defs
import Submission.NK.NUV2.LC.RouteB.locUnits_tower_eq_zero
import Submission.NK.CFTLib.HR.TransferAux.localLevelMap_injective_vanishing
import Submission.NeukirchUchida.Local.Transitivity
import Submission.Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime
import Submission.Commons.FieldTheory.Galois.exists_finite_galois_containing
import Submission.Work.SSGRoute.exists_finiteDimensional_normal_fixingSubgroup_le
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
