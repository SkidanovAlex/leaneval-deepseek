import Mathlib
import Submission.Work.Models.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Models.Abstract

theorem invertedBy_map {G G' : Type*} [Group G] [Group G'] (f : G →* G') (X : Subgroup G) (t : G)
    (hf : Function.Injective f) :
    Submission.Blueprint.invertedBy (X.map f) (f t) = f '' Submission.Blueprint.invertedBy X t := by
  ext y
  constructor
  · rintro ⟨hy, hconj⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨x, ⟨hx, hf (by simpa only [map_mul, map_inv] using hconj)⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hconj⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem f hx, by
      simpa only [map_mul, map_inv] using congrArg f hconj⟩

end Work.Models.Abstract
