import Mathlib
import Submission.Work.ORHughesFree.Rat.MapHom

namespace Work.ORHughesFree.Rat

theorem mapHom_ofSubgroup {N N' : Type} [Group N] [Group N'] (f : N →* N') (W : Subgroup N)
    (x : Work.ORHughesFree.RatU ↥W) :
    Work.ORHughesFree.RatU.mapHom f (Work.ORHughesFree.RatU.ofSubgroup W x)
      = Work.ORHughesFree.RatU.ofSubgroup (W.map f)
          (Work.ORHughesFree.RatU.mapHom (f.subgroupMap W) x) := by
  -- Both `ofSubgroup` maps are `mapHom` of the corresponding subgroup inclusions.
  rw [Work.ORHughesFree.RatU.ofSubgroup_eq_mapHom W,
    Work.ORHughesFree.RatU.ofSubgroup_eq_mapHom (W.map f)]
  -- Rewrite the two composites as `mapHom` of the composite group homomorphisms.
  rw [← RingHom.comp_apply, ← RingHom.comp_apply]
  rw [← Work.ORHughesFree.RatU.mapHom_comp W.subtype f,
    ← Work.ORHughesFree.RatU.mapHom_comp (f.subgroupMap W) (W.map f).subtype]
  -- The two composite group homomorphisms `↥W →* N'` agree.
  rw [show (W.map f).subtype.comp (f.subgroupMap W) = f.comp W.subtype from by
    ext w; rfl]

end Work.ORHughesFree.Rat
