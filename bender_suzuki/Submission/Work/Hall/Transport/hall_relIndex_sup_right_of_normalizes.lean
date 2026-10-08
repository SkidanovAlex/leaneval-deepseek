import Mathlib
import Submission.Work.Hall.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hall.Transport

set_option linter.style.haveILetI false

/-- If a subgroup `K` normalizes `H` (i.e. `K ≤ N_G(H)`), then `H ⊔ K = H K` and the coset space
`(H ⊔ K)/K` is in bijection with `H/(H ⊓ K)`.  Consequently the relative index of `K` in `H ⊔ K`
agrees with the relative index of `K` in `H`. -/
theorem hall_relIndex_sup_right_of_normalizes {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (h : K ≤ Subgroup.normalizer (H : Set G)) : K.relIndex (H ⊔ K) = K.relIndex H := by
  -- Noether's second isomorphism theorem for the pair `(K, H)`: as `K` normalizes `H`, the
  -- natural map `K → (K ⊔ H)/H` induces `K/(K ⊓ H) ≃ (K ⊔ H)/H`, hence the swapped identity
  -- `H.relIndex (H ⊔ K) = H.relIndex K`.
  have hK0 : H.relIndex K ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hiso : H.relIndex (K ⊔ H) = H.relIndex K := by
    haveI := Subgroup.normal_subgroupOf_of_le_normalizer h
    haveI := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
    have hh := Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient K H h).toEquiv
    exact hh.symm
  have hiso' : H.relIndex (H ⊔ K) = H.relIndex K := by rw [sup_comm]; exact hiso
  -- Multiplicativity of the relative index in the tower `H ⊓ K ≤ K ≤ H ⊔ K`,
  have e1 : H.relIndex K * K.relIndex (H ⊔ K) = (H ⊓ K).relIndex (H ⊔ K) := by
    have h1 := Subgroup.relIndex_mul_relIndex (H ⊓ K) K (H ⊔ K) inf_le_right le_sup_right
    rwa [Subgroup.inf_relIndex_right] at h1
  -- and in the tower `H ⊓ K ≤ H ≤ H ⊔ K`,
  have e2 : K.relIndex H * H.relIndex (H ⊔ K) = (H ⊓ K).relIndex (H ⊔ K) := by
    have h2 := Subgroup.relIndex_mul_relIndex (H ⊓ K) H (H ⊔ K) inf_le_left le_sup_left
    rwa [Subgroup.inf_relIndex_left] at h2
  -- both give the same value for the relative index of `H ⊓ K` in `H ⊔ K`.
  have key : H.relIndex K * K.relIndex (H ⊔ K) = H.relIndex K * K.relIndex H := by
    calc H.relIndex K * K.relIndex (H ⊔ K) = (H ⊓ K).relIndex (H ⊔ K) := e1
      _ = K.relIndex H * H.relIndex (H ⊔ K) := e2.symm
      _ = K.relIndex H * H.relIndex K := by rw [hiso']
      _ = H.relIndex K * K.relIndex H := Nat.mul_comm _ _
  exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hK0) key

end Work.Hall.Transport
