import Mathlib
import Submission.Work.Models.PSL2.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Models.PSL2

/-- The unipotent radical `U` and the standard split torus `D` of `SL(2,F)` (char. `2`)
intersect trivially: an upper unitriangular matrix `1 + b E₀₁` which is diagonal forces
`b = 0`, hence equals the identity. -/
theorem inf_U_D {F : Type*} [Field F] [CharP F 2] :
    Work.Models.PSL2.U (F := F) ⊓ Work.Models.PSL2.D (F := F) = ⊥ := by
  apply le_bot_iff.mp
  intro A hA
  rw [Subgroup.mem_inf, Work.Models.PSL2.mem_U_iff] at hA
  obtain ⟨⟨b, rfl⟩, hD⟩ := hA
  rw [Work.Models.PSL2.mem_D_iff'] at hD
  have hb : b = 0 := by
    have h := hD.1
    rw [Work.Models.PSL2.unip_coe] at h
    simpa using h
  rw [Subgroup.mem_bot, hb, Work.Models.PSL2.unip_zero]

end Work.Models.PSL2
