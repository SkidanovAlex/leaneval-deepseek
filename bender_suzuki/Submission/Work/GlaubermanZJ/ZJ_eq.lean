import Mathlib
import Submission.Work.GlaubermanZJ.Basic
import Submission.Work.GlaubermanZJ.thompsonJ_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The bridge `Blueprint.ZJ = Work.PGroup.ZJ`

`Submission.Blueprint.ZJ P` is `J(P) ∩ C_G(J(P))` (the blueprint's `thompsonJ`, described as the
supremum of the abelian subgroups of `P` of maximal order, intersected with its centralizer),
whereas `Work.PGroup.ZJ P` is the centre of `J(P)` viewed as a subgroup of the ambient group
(`Work.PGroup.centerIn` applied to the delivered `Work.PGroup.thompsonJ`).

Two ingredients give the identification:

* `Work.GlaubermanZJ.thompsonJ_eq` (`thompsonJ_eq.lean`, same directory): the two Thompson
  subgroups coincide, so it is enough to compare `H ∩ C_G(H)` with `Z(H)` for a single `H`;
* `inf_centralizer_eq_centerIn` below: for any subgroup `H ≤ G`, the centre of `H` regarded as a
  subgroup of `G` is exactly `H ∩ C_G(H)` — an element of `H` centralizes `H` exactly when it is
  central in `H`.
-/

namespace Work.GlaubermanZJ

/-- The centre of a subgroup `H`, as a subgroup of the ambient group (`Work.PGroup.centerIn H`),
is the intersection of `H` with its centralizer in the ambient group. -/
theorem inf_centralizer_eq_centerIn {G : Type*} [Group G] (H : Subgroup G) :
    H ⊓ Subgroup.centralizer (H : Set G) = Work.PGroup.centerIn H := by
  ext x
  constructor
  · rintro ⟨hxH, hx⟩
    refine Subgroup.mem_map.mpr ⟨⟨x, hxH⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx (y : G) y.2)
  · rintro ⟨z, hz, hzx⟩
    rw [← hzx]
    exact ⟨z.2, fun y hy => congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩)⟩

theorem ZJ_eq {G : Type*} [Group G] (P : Subgroup G) [Finite P] :
    Submission.Blueprint.ZJ P = Work.PGroup.ZJ P := by
  have hJ : Submission.Blueprint.thompsonJ P = Work.PGroup.thompsonJ P := thompsonJ_eq P
  rw [Submission.Blueprint.ZJ, Work.PGroup.ZJ, hJ]
  exact inf_centralizer_eq_centerIn _

end Work.GlaubermanZJ
