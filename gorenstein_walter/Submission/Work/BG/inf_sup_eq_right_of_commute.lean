import Mathlib

namespace Work.BG

/-- If every element of `P` commutes with every element of `Q`, then the product
subgroup `P ⊔ Q` meets `R` exactly in `Q`, provided `Q ≤ R` and `P ⊓ R = ⊥`.

The key point is that the commutativity hypothesis makes every element of `P ⊔ Q`
a product `p * q` with `p ∈ P`, `q ∈ Q`; the `P`-part of an element lying in `R`
must then also lie in `P ⊓ R = ⊥`. -/
theorem inf_sup_eq_right_of_commute {G : Type*} [Group G] (P Q R : Subgroup G)
    (hcomm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) (hQR : Q ≤ R) (hPR : P ⊓ R = ⊥) :
    (P ⊔ Q) ⊓ R = Q := by
  refine le_antisymm ?_ (le_inf le_sup_right hQR)
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxH, hxR⟩ := hx
  -- `P` normalizes `Q`, hence `Q` is normal in `P ⊔ Q`.
  have hle : P ≤ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro h hh k hk
    rw [hcomm h hh k hk, mul_assoc, mul_inv_cancel, mul_one]
    exact hk
  have ht : (Q.subgroupOf (P ⊔ Q)).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hle
  -- Hence `Q.subgroupOf (P ⊔ Q)` is normal with complement `P.subgroupOf (P ⊔ Q)`.
  have hst : P.subgroupOf (P ⊔ Q) ⊔ Q.subgroupOf (P ⊔ Q) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have hx' : (⟨x, hxH⟩ : ↥(P ⊔ Q)) ∈ P.subgroupOf (P ⊔ Q) ⊔ Q.subgroupOf (P ⊔ Q) :=
    hst ▸ Subgroup.mem_top _
  -- Decompose `x = y * z` with `y ∈ P`, `z ∈ Q`.
  obtain ⟨y, hy, z, hz, hyz⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := P.subgroupOf (P ⊔ Q))
      (t := Q.subgroupOf (P ⊔ Q)) (x := ⟨x, hxH⟩)).mp hx'
  have hyP : (y : G) ∈ P := Subgroup.mem_subgroupOf.mp hy
  have hzQ : (z : G) ∈ Q := Subgroup.mem_subgroupOf.mp hz
  have hyz' : (y : G) * (z : G) = x := by
    simpa using congrArg (Subtype.val) hyz
  -- Since `x ∈ R` and `z ∈ Q ≤ R`, the `P`-part `y` lies in `P ⊓ R = ⊥`.
  have hyR : (y : G) ∈ R := by
    have h1 : (y : G) = x * (z : G)⁻¹ := by
      rw [← hyz', mul_assoc, mul_inv_cancel, mul_one]
    rw [h1]
    exact R.mul_mem hxR (R.inv_mem (hQR hzQ))
  have hy1 : (y : G) = 1 := by
    have hb : (y : G) ∈ (⊥ : Subgroup G) := by
      rw [← hPR]; exact ⟨hyP, hyR⟩
    exact Subgroup.mem_bot.mp hb
  rw [← hyz', hy1, one_mul]
  exact hzQ

end Work.BG
