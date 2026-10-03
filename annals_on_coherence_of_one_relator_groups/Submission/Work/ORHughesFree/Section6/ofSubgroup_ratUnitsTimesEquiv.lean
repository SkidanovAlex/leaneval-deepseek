import Mathlib
import Submission.Work.ORHughesFree.Rat.MapHom
import Submission.Work.ORHughesFree.Section6.UnitsTimesEquiv

namespace Work.ORHughesFree.Section6

theorem ofSubgroup_ratUnitsTimesEquiv {K : Type} [Field K] {G : Type} [Group G]
    (H : Subgroup G) (x : Work.ORHughesFree.RatU (Kˣ × H)) :
    Work.ORHughesFree.RatU.ofSubgroup (Work.ORHughesFree.unitsTimesSubgroup (K := K) H)
        (Work.ORHughesFree.ratUnitsTimesEquiv (K := K) H x)
      = Work.ORHughesFree.RatU.mapHom
          (MonoidHom.prodMap (MonoidHom.id Kˣ) (Subgroup.subtype H)) x := by
  -- `ratUnitsTimesEquiv` is `mapHom` of the group isomorphism `unitsTimesMulEquiv`.
  have hcongr : Work.ORHughesFree.ratUnitsTimesEquiv (K := K) H x
      = Work.ORHughesFree.RatU.mapHom
          (Work.ORHughesFree.unitsTimesMulEquiv (K := K) (G := G) H) x := by
    rw [Work.ORHughesFree.ratUnitsTimesEquiv,
      Work.ORHughesFree.Rat.transportRingEquiv_apply]
    exact DFunLike.congr_fun (Work.ORHughesFree.Rat.transport_eq_mapHom _) x
  -- The underlying group homomorphism of `unitsTimesMulEquiv` composed with the inclusion of
  -- `unitsTimesSubgroup H` in `Kˣ × G` is `prodMap id H.subtype`.
  have hhom : (Work.ORHughesFree.unitsTimesSubgroup (K := K) H).subtype.comp
        ((Work.ORHughesFree.unitsTimesMulEquiv (K := K) (G := G) H) :
          Kˣ × H →* ↥(Work.ORHughesFree.unitsTimesSubgroup (K := K) H))
      = MonoidHom.prodMap (MonoidHom.id Kˣ) (Subgroup.subtype H) := rfl
  have hpoint : Work.ORHughesFree.RatU.mapHom
          (Work.ORHughesFree.unitsTimesSubgroup (K := K) H).subtype
        (Work.ORHughesFree.RatU.mapHom
          ((Work.ORHughesFree.unitsTimesMulEquiv (K := K) (G := G) H) :
            Kˣ × H →* ↥(Work.ORHughesFree.unitsTimesSubgroup (K := K) H)) x)
      = Work.ORHughesFree.RatU.mapHom
          (MonoidHom.prodMap (MonoidHom.id Kˣ) (Subgroup.subtype H)) x := by
    rw [← hhom]
    have hcomp := DFunLike.congr_fun (Work.ORHughesFree.RatU.mapHom_comp
        ((Work.ORHughesFree.unitsTimesMulEquiv (K := K) (G := G) H) :
          Kˣ × H →* ↥(Work.ORHughesFree.unitsTimesSubgroup (K := K) H))
        (Work.ORHughesFree.unitsTimesSubgroup (K := K) H).subtype) x
    simp only [RingHom.comp_apply] at hcomp
    exact hcomp.symm
  rw [hcongr]
  rw [Work.ORHughesFree.RatU.ofSubgroup_eq_mapHom]
  exact hpoint

end Work.ORHughesFree.Section6
