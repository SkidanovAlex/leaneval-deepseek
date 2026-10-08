import Mathlib.GroupTheory.OrderOfElement

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.StronglyEmbedded

theorem centralizer_le_of_isStronglyEmbedded {G : Type*} [Group G] [Finite G]
    (M : Subgroup G)
    (hodd : ∀ g : G, g ∉ M → Odd (Nat.card ↥(M ⊓ M.map (MulAut.conj g).toMonoidHom)))
    {t : G} (ht : t ∈ M) (ht2 : orderOf t = 2) :
    Subgroup.centralizer ({t} : Set G) ≤ M := by
  intro x hx
  by_contra hxM
  -- `x` commutes with `t`
  have hcomm : t * x = x * t :=
    (Subgroup.mem_centralizer_iff.mp hx) t (Set.mem_singleton t)
  -- hence conjugation by `x` fixes `t`
  have hconj : (MulAut.conj x) t = t := by
    rw [MulAut.conj_apply, ← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  -- so `t` lies in `M ⊓ M.map (conj x)`
  have htK : t ∈ (M ⊓ M.map (MulAut.conj x).toMonoidHom : Subgroup G) := by
    rw [Subgroup.mem_inf, Subgroup.mem_map]
    exact ⟨ht, t, ht, hconj⟩
  -- its order as an element of that intersection is still 2
  have horder : orderOf (⟨t, htK⟩ : (M ⊓ M.map (MulAut.conj x).toMonoidHom : Subgroup G)) = 2 := by
    rw [← Subgroup.orderOf_coe (⟨t, htK⟩ : (M ⊓ M.map (MulAut.conj x).toMonoidHom : Subgroup G))]
    exact ht2
  -- but that order divides the (odd) order of the intersection, contradiction
  have hdvd : orderOf (⟨t, htK⟩ : (M ⊓ M.map (MulAut.conj x).toMonoidHom : Subgroup G)) ∣
      Nat.card (M ⊓ M.map (MulAut.conj x).toMonoidHom : Subgroup G) :=
    orderOf_dvd_natCard _
  have hoddK : Odd (Nat.card (M ⊓ M.map (MulAut.conj x).toMonoidHom : Subgroup G)) :=
    hodd x hxM
  have hoddorder : Odd (orderOf (⟨t, htK⟩ : (M ⊓ M.map (MulAut.conj x).toMonoidHom : Subgroup G))) :=
    Odd.of_dvd_nat hoddK hdvd
  rw [horder] at hoddorder
  exact absurd hoddorder (by decide)

end Commons.GroupTheory.StronglyEmbedded