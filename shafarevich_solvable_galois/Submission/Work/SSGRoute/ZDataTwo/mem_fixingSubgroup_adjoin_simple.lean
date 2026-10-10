import Mathlib.FieldTheory.Galois.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataTwo

theorem mem_fixingSubgroup_adjoin_simple
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (β : Ω) (σ : Ω ≃ₐ[K] Ω) (h : σ β = β) :
    σ ∈ (IntermediateField.adjoin K ({β} : Set Ω)).fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx => simp only [Set.mem_singleton_iff] at hx; rw [hx, h]
  | algebraMap x => exact σ.commutes x
  | add x y hx hy ihx ihy => rw [map_add, ihx, ihy]
  | inv x hx ihx => rw [map_inv₀, ihx]
  | mul x y hx hy ihx ihy => rw [map_mul, ihx, ihy]

end Work.SSGRoute.ZDataTwo
