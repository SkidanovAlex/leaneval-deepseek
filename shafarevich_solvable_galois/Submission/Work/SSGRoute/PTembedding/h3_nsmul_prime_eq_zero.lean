import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Pi
import Mathlib.Topology.Defs.Basic
import Submission.Work.SSGRoute.H3Map.mapC3c_mem_Z3_mem_B3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PTembedding

/-- An element of a module over `ZMod p` is killed by the natural number `p`: the two `nsmul`
structures agree and `(p : ZMod p) = 0`. -/
theorem zmod_nsmul_self_eq_zero (p : ℕ) {M : Type} [AddCommGroup M] [Module (ZMod p) M]
    (m : M) : p • m = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod p) p m, ZMod.natCast_self, zero_smul]

/-- Each `3`-cochain `c : Z³_c(G,M)` is killed by `p`, since `Z³_c(G,M)` is a subgroup of the
pointwise `ZMod p`-module `G × G × G → M`. -/
theorem h3_cocycle_nsmul_prime_eq_zero (p : ℕ) [Fact p.Prime] {G : Type} [TopologicalSpace G]
    [Group G] {M : Type} [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    (c : Work.SSGRoute.Z3 (M := M) G) : p • c = 0 := by
  apply Subtype.ext
  rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero, zmod_nsmul_self_eq_zero]

/-- `H³_c(G, M)` is a quotient of the pointwise `ZMod p`-module `Z³_c(G,M)`: the quotient map is
additive, hence preserves `nsmul`, so `p • x = 0` for every `x ∈ H³_c(G,M)`. -/
theorem h3_nsmul_prime_eq_zero (p : ℕ) [Fact p.Prime] {G : Type} [TopologicalSpace G] [Group G]
    {M : Type} [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    (x : Work.SSGRoute.H3 (M := M) G) : p • x = 0 := by
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective
    ((Work.SSGRoute.B3 (M := M) G).comap (Work.SSGRoute.Z3 (M := M) G).subtype) x
  rw [← map_nsmul, h3_cocycle_nsmul_prime_eq_zero, map_zero]

end Work.SSGRoute.PTembedding
