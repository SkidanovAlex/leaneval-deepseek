import Mathlib
import Submission.Work.ORHughesFree.Section6.Reduce

namespace Work.ORHughesFree.Section6

theorem map_map_snd_insertion {K : Type} [Monoid K] {G : Type} [Group G]
    (H : Subgroup G) (V : Subgroup (Kˣ × H)) :
    (V.map (MonoidHom.prodMap (MonoidHom.id Kˣ) (Subgroup.subtype H))).map (MonoidHom.snd Kˣ G)
      = (V.map (MonoidHom.snd Kˣ H)).map (Subgroup.subtype H) := by
  have hcomp : (MonoidHom.snd Kˣ G).comp (MonoidHom.prodMap (MonoidHom.id Kˣ) (Subgroup.subtype H))
      = (Subgroup.subtype H).comp (MonoidHom.snd Kˣ H) := by
    ext x
    simp [MonoidHom.prodMap]
  rw [Subgroup.map_map, Subgroup.map_map, hcomp]

end Work.ORHughesFree.Section6
