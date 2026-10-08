import Mathlib

namespace Work.ZJB2.Step1

/-- If every element of `H` commutes with every element of `K`, then the subgroup
`H ⊔ K` consists exactly of the products `x * y` with `x ∈ H`, `y ∈ K`. -/
theorem memSupIffOfCommute {G : Type*} [Group G] {H K : Subgroup G}
    (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) {a : G} :
    a ∈ H ⊔ K ↔ ∃ x ∈ H, ∃ y ∈ K, x * y = a := by
  -- The set of products `x * y` is a subgroup: it contains `H` and `K`, so it
  -- contains `H ⊔ K`; and it is contained in `H ⊔ K` by construction.
  let S : Subgroup G :=
  { carrier := {a | ∃ x ∈ H, ∃ y ∈ K, x * y = a}
    one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
    mul_mem' := by
      rintro a b ⟨x1, hx1, y1, hy1, rfl⟩ ⟨x2, hx2, y2, hy2, rfl⟩
      refine ⟨x1 * x2, H.mul_mem hx1 hx2, y1 * y2, K.mul_mem hy1 hy2, ?_⟩
      rw [mul_assoc x1 x2 (y1 * y2), ← mul_assoc x2 y1 y2,
          hc x2 hx2 y1 hy1, mul_assoc y1 x2 y2, ← mul_assoc x1 y1 (x2 * y2)]
    inv_mem' := by
      rintro a ⟨x, hx, y, hy, rfl⟩
      refine ⟨x⁻¹, H.inv_mem hx, y⁻¹, K.inv_mem hy, ?_⟩
      rw [mul_inv_rev, hc x⁻¹ (H.inv_mem hx) y⁻¹ (K.inv_mem hy)] }
  constructor
  · intro ha
    have leH : H ≤ S := fun x hx => ⟨x, hx, 1, K.one_mem, mul_one x⟩
    have leK : K ≤ S := fun y hy => ⟨1, H.one_mem, y, hy, one_mul y⟩
    exact sup_le leH leK ha
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hy)

end Work.ZJB2.Step1
