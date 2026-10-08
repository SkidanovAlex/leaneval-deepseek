import Mathlib
import Submission.Work.Transitivity.API.relIndex_inf_eq_relIndex_sup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.LocalPrelim

/-- If `H` normalizes `W`, then the relative index of `H` in `H ⊔ W` equals the relative
index of `H ⊓ W` in `W`.  Equivalently, the cosets of `H` in `H W` are in bijection with the
cosets of `H ⊓ W` in `W`. -/
theorem relIndex_sup_eq_relIndex_inf_auxL {X : Type*} [Group X] {H W : Subgroup X}
    (h : H ≤ Subgroup.normalizer (W : Set X)) :
    H.relIndex (H ⊔ W) = (H ⊓ W).relIndex W := by
  -- The right-hand side is `H.relIndex W`.
  rw [Subgroup.inf_relIndex_right]
  -- Express both relative indices as cardinalities of images under `X → X ⧸ H`.
  rw [Work.Transitivity.API.relIndex_eq_card_image_mk W H,
    Work.Transitivity.API.relIndex_eq_card_image_mk (H ⊔ W) H]
  -- It remains to show that `W` and `H ⊔ W` have the same image in `X ⧸ H`.
  have himage :
      (QuotientGroup.mk '' (W : Set X) : Set (X ⧸ H)) =
        (QuotientGroup.mk '' ((H ⊔ W : Subgroup X) : Set X) : Set (X ⧸ H)) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact ⟨w, Subgroup.mem_sup_right hw, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      -- Write `x = a * b` with `a ∈ H`, `b ∈ W`, using `H ≤ N(W)`.
      rw [Subgroup.coe_mul_of_left_le_normalizer_right H W h] at hx
      rw [Set.mem_mul] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      -- The element `a * b * a⁻¹` lies in `W` and determines the same coset as `a * b`.
      refine ⟨a * b * a⁻¹, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (h ha) b).mp hb
      · rw [QuotientGroup.eq]
        simp only [mul_inv_rev, inv_inv]
        simpa [mul_assoc] using ha
  rw [himage]

end Work.LocalPrelim
