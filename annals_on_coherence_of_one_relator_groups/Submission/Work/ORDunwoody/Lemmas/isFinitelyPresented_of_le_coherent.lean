import Mathlib
import Submission.Work.ORDunwoody.Basic

namespace Work.ORDunwoody.Lemmas

/-- If `L` is a coherent group and `K ≤ L` is a finitely generated subgroup,
then `K` is finitely presented.  Indeed `K` is isomorphic to the subgroup
`K.subgroupOf L` of `L`, which is finitely generated, and coherence of `L`
then exhibits it as finitely presented. -/
theorem isFinitelyPresented_of_le_coherent {G : Type*} [Group G] (K L : Subgroup G)
    (hcoh : Group.Coherent L) (hK : K.FG) (hle : K ≤ L) :
    Group.IsFinitelyPresented K := by
  have hK' : Group.FG K := (Group.fg_iff_subgroup_fg K).mpr hK
  have hHfg : Group.FG (K.subgroupOf L) :=
    Group.fg_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hle).symm.surjective
  have hH : (K.subgroupOf L).FG := (Group.fg_iff_subgroup_fg _).mp hHfg
  exact Group.IsFinitelyPresented.equiv (Subgroup.subgroupOfEquivOfLe hle)
    (h := hcoh (K.subgroupOf L) hH)

end Work.ORDunwoody.Lemmas
