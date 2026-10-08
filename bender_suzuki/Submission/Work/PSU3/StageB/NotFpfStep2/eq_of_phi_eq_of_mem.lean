import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.StageB.NotFpfStep2.center_le_P
import Submission.Work.PSU3.StageB.NotFpfStep2.center_le_centD

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB.NotFpfStep2

theorem eq_of_phi_eq_of_mem {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    {U : Subgroup G}
    (hinf : Q ⊓ Submission.Blueprint.twoPoint H t = ⊥)
    {Y : Type} [Group Y] {φ : ↥U →* Y} (hker : φ.ker = Subgroup.center ↥U)
    (hZ : ∀ z ∈ Subgroup.center ↥U,
      ((z : ↥U) : G) ∈ Submission.Blueprint.twoPoint H t)
    {a b : ↥U} (ha : a ∈ (Q ⊓ U).subgroupOf U) (hb : b ∈ (Q ⊓ U).subgroupOf U)
    (h : φ a = φ b) : a = b := by
  -- `φ a = φ b` forces `a * b⁻¹` into the kernel of `φ`, i.e. into the center of `U`.
  have hkerz : a * b⁻¹ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  have hcent : a * b⁻¹ ∈ Subgroup.center ↥U := by rw [← hker]; exact hkerz
  -- `a, b` lie in `Q ⊓ U`, hence so does `a * b⁻¹`.
  have hzK : a * b⁻¹ ∈ (Q ⊓ U).subgroupOf U :=
    ((Q ⊓ U).subgroupOf U).mul_mem ha (((Q ⊓ U).subgroupOf U).inv_mem hb)
  have hzQ : (((a * b⁻¹ : ↥U)) : G) ∈ Q := (Subgroup.mem_subgroupOf.mp hzK).1
  -- by hypothesis, the center of `U` lies in `D = twoPoint H t`.
  have hzD : (((a * b⁻¹ : ↥U)) : G) ∈ Submission.Blueprint.twoPoint H t := hZ _ hcent
  -- so `a * b⁻¹` lies in `Q ⊓ D = ⊥`, hence is trivial in `G`, hence in `U`.
  have hbot : (((a * b⁻¹ : ↥U)) : G) ∈ (⊥ : Subgroup G) := by
    rw [← hinf]; exact ⟨hzQ, hzD⟩
  have hG : ((a * b⁻¹ : ↥U) : G) = 1 := Subgroup.mem_bot.mp hbot
  have hG' : (a : G) * (b : G)⁻¹ = 1 := by simpa using hG
  have hab : (a : G) = (b : G) := mul_inv_eq_one.mp hG'
  exact Subtype.coe_injective hab

end Work.PSU3.StageB.NotFpfStep2
