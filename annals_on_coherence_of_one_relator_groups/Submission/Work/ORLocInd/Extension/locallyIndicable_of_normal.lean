import Mathlib
import Submission.Work.ORLocInd.Basic
import Submission.Work.ORLocInd.LI.subgroup_locallyIndicable
import Submission.Work.ORLocInd.LI.locallyIndicable_of_injective
import Submission.Work.ORLocInd.LI.indicable_of_locallyIndicable_fg
import Submission.Work.ORLocInd.LI.locallyIndicable_prod

namespace Work.ORLocInd.Extension

/-- **Local indicability is closed under extensions.**

If `N ◁ G` is a normal subgroup with `N` and `G ⧸ N` both locally indicable, then so is `G`.

Let `H ≤ G` be a nontrivial finitely generated subgroup.  Under the quotient map `f : G →* G ⧸ N`
its image `H.map f` is again finitely generated.  If that image is trivial, then `H ≤ N` and `H`
embeds into the locally indicable group `N`, hence is itself locally indicable
(`locallyIndicable_of_injective`) and so, being finitely generated and nontrivial, indicable
(`indicable_of_locallyIndicable_fg`).  Otherwise `H.map f` is a nontrivial finitely generated
subgroup of the locally indicable quotient `G ⧸ N`, hence indicable, and a surjection
`H.map f →* Multiplicative ℤ` pulls back along the surjection `H ↠ H.map f`. -/
theorem locallyIndicable_of_normal {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (hN : Work.ORLocInd.Group.LocallyIndicable N)
    (hQ : Work.ORLocInd.Group.LocallyIndicable (G ⧸ N)) :
    Work.ORLocInd.Group.LocallyIndicable G := by
  intro H hHfg hHne
  by_cases him : H.map (QuotientGroup.mk' N) = ⊥
  · -- the image of `H` in `G ⧸ N` is trivial, so `H ≤ N`
    have hHN : H ≤ N := by
      have h := (Subgroup.map_eq_bot_iff H).mp him
      rwa [QuotientGroup.ker_mk' N] at h
    -- `H` embeds into the locally indicable group `N`, hence is locally indicable,
    -- and being finitely generated and nontrivial it is indicable.
    have hLI : Group.LocallyIndicable ↥H :=
      LI.locallyIndicable_of_injective
        (H.subtype.codRestrict N fun x => hHN x.2)
        (fun a b hab => Subtype.ext (congrArg (Subtype.val : ↥N → G) hab)) hN
    exact @LI.indicable_of_locallyIndicable_fg ↥H _ ((Group.fg_iff_subgroup_fg H).mpr hHfg) hLI
      ((Subgroup.nontrivial_iff_ne_bot H).mpr hHne)
  · -- otherwise the image is a nontrivial finitely generated subgroup of `G ⧸ N`
    exact LI.indicable_of_map_ne_bot (QuotientGroup.mk' N) hQ hHfg him

end Work.ORLocInd.Extension
