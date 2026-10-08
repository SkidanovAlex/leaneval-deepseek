import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSLit.Wielandt

/-- If `P` normalizes `K` and together `K` and `P` generate the whole group,
then `K` is normal. Indeed both `K` and `P` lie in the normalizer of `K`
(`P` because it is closed under inverses and `K` trivially), so the normalizer,
being a subgroup, contains `K ⊔ P = ⊤`. -/
theorem NormalOfNorm {F : Type*} [Group F] (K P : Subgroup F)
    (hsup : K ⊔ P = ⊤)
    (hnorm : ∀ g ∈ P, ∀ k ∈ K, g * k * g⁻¹ ∈ K) :
    K.Normal := by
  rw [← Subgroup.normalizer_eq_top_iff]
  rw [eq_top_iff, ← hsup]
  apply sup_le
  · exact Subgroup.le_normalizer
  · intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · exact hnorm g hg n
    · intro h
      have hmem : g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ ∈ K :=
        hnorm g⁻¹ (P.inv_mem hg) (g * n * g⁻¹) h
      have heq : g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n := by group
      rwa [heq] at hmem

end Work.BSLit.Wielandt
