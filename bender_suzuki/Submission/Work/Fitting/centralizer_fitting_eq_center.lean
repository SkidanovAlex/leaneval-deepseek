import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.centralizer_fitting_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Fitting

/-- The center of the Fitting subgroup is contained in the centralizer of the Fitting
subgroup: an element of `Z(F)` commutes with every element of `F`. -/
theorem subgroupCenter_fitting_le_centralizer (G : Type*) [Group G] :
    Work.Fitting.subgroupCenter (Work.Fitting.fitting G) ≤
      Subgroup.centralizer (Work.Fitting.fitting G : Set G) := by
  rintro x ⟨z, hz, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h := (Subgroup.mem_center_iff.mp hz) ⟨y, hy⟩
  simpa using congrArg Subtype.val h

/-- In a finite solvable group, an element centralizing the Fitting subgroup lies in the
Fitting subgroup, hence in its center. -/
theorem centralizer_fitting_le_subgroupCenter (G : Type*) [Group G] [Finite G]
    [Group.IsSolvable G] :
    Subgroup.centralizer (Work.Fitting.fitting G : Set G) ≤
      Work.Fitting.subgroupCenter (Work.Fitting.fitting G) := by
  intro x hx
  have hxF : x ∈ fitting G := centralizer_fitting_le G hx
  rw [subgroupCenter, Subgroup.mem_map]
  refine ⟨⟨x, hxF⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx (y : G) y.2)

theorem centralizer_fitting_eq_center (G : Type*) [Group G] [Finite G] [Group.IsSolvable G] :
    Subgroup.centralizer (Work.Fitting.fitting G : Set G) =
      Work.Fitting.subgroupCenter (Work.Fitting.fitting G) :=
  le_antisymm (centralizer_fitting_le_subgroupCenter G) (subgroupCenter_fitting_le_centralizer G)

end Work.Fitting
