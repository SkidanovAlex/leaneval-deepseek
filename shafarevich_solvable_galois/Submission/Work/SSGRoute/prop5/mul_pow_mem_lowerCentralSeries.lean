import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.prop5

open scoped commutatorElement

/-- If `u` and `v` both lie in the `(m-1)`-st term of the lower central series of a group `P`,
then `(u*v)^k * ((v^k)*(u^k))⁻¹` lies in the `m`-th term.

This expresses that, modulo the `m`-th term, the elements of the `(m-1)`-st term are central,
so that `u*v` commutes with `u` and `v`, whence `(u*v)^k` and `v^k * u^k` agree modulo that
term. -/
theorem mul_pow_mem_lowerCentralSeries (P : Type) [Group P] (m k : ℕ) (hm : 1 ≤ m) (u v : P)
    (hu : u ∈ (⊤ : Subgroup P).lowerCentralSeries (m - 1))
    (hv : v ∈ (⊤ : Subgroup P).lowerCentralSeries (m - 1)) :
    (u * v) ^ k * ((v ^ k) * (u ^ k))⁻¹ ∈ (⊤ : Subgroup P).lowerCentralSeries m := by
  -- γ_m is the commutator of γ_{m-1} with the whole group, since `m = (m-1) + 1`.
  have hm_eq : m = (m - 1) + 1 := (Nat.sub_add_cancel hm).symm
  have hK : (⊤ : Subgroup P).lowerCentralSeries m
      = ⁅(⊤ : Subgroup P).lowerCentralSeries (m - 1), ⊤⁆ := by
    conv_lhs => rw [hm_eq]
    rw [Subgroup.lowerCentralSeries_succ]
  -- Hence `u` and `v` commute modulo γ_m.
  have hcomm : ⁅u, v⁆ ∈ (⊤ : Subgroup P).lowerCentralSeries m := by
    rw [hK]
    exact Subgroup.commutator_mono le_rfl le_top (Subgroup.commutator_mem_commutator hu hv)
  -- Pass to the quotient `P ⧸ γ_m`, where `u` and `v` commute.
  let N := (⊤ : Subgroup P).lowerCentralSeries m
  let φ : P →* P ⧸ N := QuotientGroup.mk' N
  have hmemker : ⁅u, v⁆ ∈ φ.ker := by
    show ⁅u, v⁆ ∈ (QuotientGroup.mk' N).ker
    rw [QuotientGroup.ker_mk']
    exact hcomm
  have hcommφ : φ ⁅u, v⁆ = 1 := MonoidHom.mem_ker.mp hmemker
  have hcomm1 : ⁅φ u, φ v⁆ = 1 := by
    rw [← map_commutatorElement φ u v]; exact hcommφ
  have hcu : Commute (φ u) (φ v) := commutatorElement_eq_one_iff_commute.mp hcomm1
  -- The image of the target element is `1`.
  have hz : φ ((u * v) ^ k * ((v ^ k) * (u ^ k))⁻¹) = 1 := by
    have e1 : φ ((u * v) ^ k * ((v ^ k) * (u ^ k))⁻¹)
        = (φ u * φ v) ^ k * ((φ v) ^ k * (φ u) ^ k)⁻¹ := by
      simp only [map_mul, map_pow, map_inv]
    rw [e1, hcu.mul_pow k, ← (hcu.pow_pow k k).eq, mul_inv_cancel]
  -- So the element lies in the kernel of `φ`, which is γ_m.
  have hmem : (u * v) ^ k * ((v ^ k) * (u ^ k))⁻¹ ∈ N := by
    rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
    exact hz
  exact hmem

end Work.SSGRoute.prop5
