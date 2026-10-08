import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.centerIn_le_thompsonJ
import Submission.Work.PGroup.center_eq_centralizer_of_isCriticalSubgroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PGroup

/-- The centre of a finite subgroup `P` is contained in `ZJ P = Z(J(P))`.

`z ∈ Z(P)` lies in `P`, hence in `J(P)` (this is `centerIn_le_thompsonJ`, which only needs
that `Z(P)` is abelian and can therefore be adjoined to an abelian subgroup of `P` of maximal
order), and it centralises `P`, hence `J(P) ≤ P`.  Thus `z ∈ J(P) ∩ C_G(J(P)) = Z(J(P))`. -/
theorem centerIn_le_ZJ {G : Type*} [Group G] (P : Subgroup G) [Finite P] :
    Work.PGroup.centerIn P ≤ Work.PGroup.ZJ P := by
  intro z hz
  obtain ⟨zp, hzpcenter, hzpe⟩ := Subgroup.mem_map.mp hz
  -- `z` centralises `P`
  have hzcent : z ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := Subgroup.mem_center_iff.mp hzpcenter (⟨y, hy⟩ : ↥P)
    have h' : y * (zp : G) = (zp : G) * y := by
      have := congrArg Subtype.val h
      simpa using this
    have hzpe' : (zp : G) = z := hzpe
    rw [hzpe'] at h'
    exact h'
  -- `z` lies in `J(P)`
  have hzJ : z ∈ thompsonJ P := centerIn_le_thompsonJ P hz
  -- and `z` centralises `J(P)`, since `J(P) ≤ P`
  have hzcentJ : z ∈ Subgroup.centralizer (thompsonJ P : Set G) :=
    Subgroup.centralizer_le (thompsonJ_le P) hzcent
  rw [ZJ, centerIn_eq_inf_centralizer]
  exact ⟨hzJ, hzcentJ⟩

end Work.PGroup
