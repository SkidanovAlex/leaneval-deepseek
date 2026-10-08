import Mathlib
import Submission.Work.NormalComplement.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement.NC4

/-- In a group, if `S ⊓ T = ⊥` then a product `a * c` with `a ∈ S` and `c ∈ T` determines its two
factors: the decomposition of an element of `S ⊔ T` along `S` and `T` is unique. -/
theorem mul_eq_mul_unique {G : Type} [Group G] {S T : Subgroup G} (hinf : S ⊓ T = ⊥)
    {a b c d : G} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ T) (hd : d ∈ T)
    (h : a * c = b * d) : a = b ∧ c = d := by
  -- Rearrange `a * c = b * d` into `a⁻¹ * b = c * d⁻¹`, an element of both `S` and `T`.
  have h2 : a⁻¹ * b = c * d⁻¹ := by
    have key : a⁻¹ * (a * c) * d⁻¹ = a⁻¹ * (b * d) * d⁻¹ := by rw [h]
    simpa [mul_assoc] using key.symm
  have hmS : a⁻¹ * b ∈ S := S.mul_mem (S.inv_mem ha) hb
  have hmT : c * d⁻¹ ∈ T := T.mul_mem hc (T.inv_mem hd)
  have hmem : a⁻¹ * b ∈ S ⊓ T := ⟨hmS, by rw [h2]; exact hmT⟩
  rw [hinf] at hmem
  have hone : a⁻¹ * b = 1 := Subgroup.mem_bot.mp hmem
  have hab : a = b := inv_mul_eq_one.mp hone
  refine ⟨hab, ?_⟩
  subst hab
  exact mul_left_cancel h

end Work.NormalComplement.NC4
