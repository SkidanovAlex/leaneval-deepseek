import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

/-- The automorphism group of a cyclic group is commutative.

Indeed `IsCyclic.mulAutMulEquiv` identifies `MulAut H` with the units of `ZMod (Nat.card H)`. -/
theorem mulAut_comm_of_isCyclic {H : Type*} [Group H] (hcyc : IsCyclic H)
    (f g : MulAut H) : f * g = g * f := by
  let e : MulAut H ≃* (ZMod (Nat.card H))ˣ := @IsCyclic.mulAutMulEquiv H _ hcyc
  exact e.injective (by rw [map_mul, map_mul, mul_comm])

/-- If `U` is cyclic, then the commutator `⁅a, b⁆ = a * b * a⁻¹ * b⁻¹` of two elements of the
normalizer of `U` lies in the centralizer of `U`.

Conjugation by `N_G(U)` defines a homomorphism `N_G(U) →* MulAut U` with kernel `C_G(U)`
(`Subgroup.normalizerMonoidHom`, `Subgroup.normalizerMonoidHom_ker`).  Since `U` is cyclic its
automorphism group is commutative (`mulAut_comm_of_isCyclic`), so any commutator of normalizing
elements is mapped to `1`, i.e. lies in the kernel `C_G(U)`. -/
theorem comm_mem_centralizer_of_isCyclic {G : Type*} [Group G] {U : Subgroup G} (hcyc : IsCyclic U)
    {a b : G} (ha : a ∈ Subgroup.normalizer (U : Set G))
    (hb : b ∈ Subgroup.normalizer (U : Set G)) :
    a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (U : Set G) := by
  -- Conjugation by the normalizer is a homomorphism into the automorphism group of `U`.
  let φ : Subgroup.normalizer (U : Set G) →* MulAut U := Subgroup.normalizerMonoidHom U
  let a' : Subgroup.normalizer (U : Set G) := ⟨a, ha⟩
  let b' : Subgroup.normalizer (U : Set G) := ⟨b, hb⟩
  -- By commutativity of `MulAut U` the commutator lies in the kernel of `φ`.
  have hmem : a' * b' * a'⁻¹ * b'⁻¹ ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [mulAut_comm_of_isCyclic hcyc (φ a') (φ b')]
    group
  -- The kernel of `φ` is `C_G(U) ∩ N_G(U) = C_G(U)`.
  have hker : φ.ker =
      (Subgroup.centralizer (U : Set G)).subgroupOf (Subgroup.normalizer (U : Set G)) :=
    Subgroup.normalizerMonoidHom_ker U
  rw [hker, Subgroup.mem_subgroupOf] at hmem
  simpa using hmem

end Work.NormalComplement
