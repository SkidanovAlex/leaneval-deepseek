import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PGroup

variable {G : Type*} [Group G]

/-- The center of a subgroup, transported to the ambient group, is the intersection of the
subgroup with its centralizer: `Z(C) = C ∩ C_G(C)`. -/
theorem centerIn_eq_inf_centralizer (C : Subgroup G) :
    centerIn C = C ⊓ Subgroup.centralizer (C : Set G) := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_inf]
    refine ⟨centerIn_le C hx, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rcases hx with ⟨z, hz, hzx⟩
    rw [← hzx]
    have h1 := Subgroup.mem_center_iff.mp hz ⟨h, hh⟩
    show h * (C.subtype z) = (C.subtype z) * h
    simpa using congrArg (fun w : ↥C => (w : G)) h1
  · intro hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxC, hxcent⟩ := hx
    refine ⟨⟨x, hxC⟩, ?_, rfl⟩
    refine Subgroup.mem_center_iff.mpr ?_
    intro g
    apply Subtype.ext
    show (g : G) * x = x * (g : G)
    exact (Subgroup.mem_centralizer_iff.mp hxcent) (g : G) g.2

theorem center_eq_centralizer_of_isCriticalSubgroup {G : Type*} [Group G] {p : ℕ}
    (P C : Subgroup G) (hC : Work.PGroup.IsCriticalSubgroup p P C) :
    P ⊓ Subgroup.centralizer (C : Set G) = Work.PGroup.centerIn C := by
  rw [centerIn_eq_inf_centralizer C]
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Subgroup.mem_inf] at hx ⊢
    exact ⟨hC.self_centralizing hx, hx.2⟩
  · intro x hx
    rw [Subgroup.mem_inf] at hx ⊢
    exact ⟨hC.le_self hx.1, hx.2⟩

end Work.PGroup
