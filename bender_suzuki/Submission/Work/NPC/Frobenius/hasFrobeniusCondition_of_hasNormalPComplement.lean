/-
Area A9 of the Feit--Thompson drive: the *easy direction* of Frobenius' normal `p`-complement
theorem.

## Main result

* `Work.NPC.Frobenius.hasFrobeniusCondition_of_hasNormalPComplement`: if `G` has a normal
  `p`-complement then Frobenius' condition holds, i.e. for every non-identity `p`-subgroup
  `Q ≤ G` the group `N_G(Q)/C_G(Q)` of automorphisms of `Q` induced by `G` is a `p`-group.

The mathematical content is that a normal subgroup `N` of order coprime to `p` which normalizes
a `p`-subgroup `Q` already centralizes it: `N_N(Q) = C_N(Q)`.  Indeed `[N_N(Q), Q] ≤ N ∩ Q`
(the commutator lies in `N` by normality and in `Q` because `N_N(Q)` normalizes `Q`), and
`N ∩ Q = ⊥` since `|N|` is coprime to `|Q|` (a power of `p`).  Consequently the natural map
`N_G(Q) → G ⧸ N` has kernel `N_N(Q)`, which lies in `C_G(Q)`, so `N_G(Q)/C_G(Q)` is a quotient
of the `p`-group `N_G(Q)/N_N(Q)` (a subgroup of the `p`-group `G ⧸ N`).
-/
import Mathlib
import Submission.Work.NPC.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

open scoped Pointwise

namespace Work.NPC.Frobenius

variable {G : Type*} [Group G]

/-- **The key point.**  Let `N ⊴ G` have order coprime to the prime `p`, and let `Q ≤ G` be a
`p`-subgroup.  Then every element of `N` which normalizes `Q` already centralizes it:
`N ⊓ N_G(Q) ≤ C_G(Q)`.

Indeed for `x ∈ N ⊓ N_G(Q)` and `q ∈ Q` the commutator `[x, q] = x * q * x⁻¹ * q⁻¹` lies in `N`
(conjugate of `x⁻¹` times `x`) and in `Q` (`x * q * x⁻¹ ∈ Q` because `x` normalizes `Q`); but
`N ∩ Q = ⊥` because `|N ∩ Q|` divides both `|N|` (coprime to `p`) and `|Q|` (a power of `p`).
Hence `[x, q] = 1` and `x` centralizes `Q`. -/
theorem inf_normalizer_le_centralizer {p : ℕ} [Fact p.Prime] {N Q : Subgroup G} [Finite G]
    (hN : N.Normal) (hcop : (Nat.card N).Coprime p) (hQ : IsPGroup p Q) :
    N ⊓ Subgroup.normalizer (Q : Set G) ≤ Subgroup.centralizer (Q : Set G) := by
  -- `|N|` is coprime to `|Q| = p ^ m`, so `N ∩ Q = ⊥`.
  obtain ⟨m, hm⟩ := hQ.exists_card_eq
  have hinf : N ⊓ Q = ⊥ :=
    disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard (by rw [hm]; exact hcop.pow_right m))
  intro x hx
  obtain ⟨hxN, hxA⟩ := hx
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hxq : x * q * x⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hxA q).mp hq
  -- the commutator `[x, q]` lies in `N` ...
  have hcN : x * q * x⁻¹ * q⁻¹ ∈ N := by
    have h1 : x * (q * x⁻¹ * q⁻¹) ∈ N := N.mul_mem hxN (hN.conj_mem x⁻¹ (N.inv_mem hxN) q)
    simpa only [mul_assoc] using h1
  -- ... and in `Q`.
  have hcQ : x * q * x⁻¹ * q⁻¹ ∈ Q := Q.mul_mem hxq (Q.inv_mem hq)
  have hc1 : x * q * x⁻¹ * q⁻¹ = 1 := by
    have hmem : x * q * x⁻¹ * q⁻¹ ∈ N ⊓ Q := ⟨hcN, hcQ⟩
    rw [hinf] at hmem
    exact Subgroup.mem_bot.mp hmem
  -- `x * q * x⁻¹ = q`, i.e. `x` and `q` commute.
  have h2 : x * q * x⁻¹ = q := mul_inv_eq_one.mp hc1
  calc q * x = (x * q * x⁻¹) * x := by rw [h2]
    _ = x * q := by group

theorem hasFrobeniusCondition_of_hasNormalPComplement {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (h : Work.NPC.HasNormalPComplement p G) :
    Work.NPC.HasFrobeniusCondition p G := by
  obtain ⟨N, hNnorm, hNcop, hNquot⟩ := h
  haveI : N.Normal := hNnorm
  intro Q hQp _
  unfold Work.NPC.IsConjPGroup
  -- `N_G(Q)/C_G(Q)` is a quotient of `N_G(Q)/N_N(Q)`, where `N_N(Q) ≤ C_G(Q)`.
  intro y
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective
    ((Subgroup.centralizer (Q : Set G)).subgroupOf (Subgroup.normalizer (Q : Set G))) y
  -- the order of `a` in `G ⧸ N` is a power of `p`
  obtain ⟨k, hk⟩ := hNquot (QuotientGroup.mk' N (a : G))
  refine ⟨k, ?_⟩
  rw [← map_pow]
  have hmemN : (a : G) ^ p ^ k ∈ N := by
    have h : (QuotientGroup.mk' N) ((a : G) ^ p ^ k) = 1 := by rw [map_pow]; exact hk
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at h
    exact h
  have hmemA : (a : G) ^ p ^ k ∈ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normalizer (Q : Set G)).pow_mem a.2 (p ^ k)
  have hmemC : (a : G) ^ p ^ k ∈ Subgroup.centralizer (Q : Set G) :=
    inf_normalizer_le_centralizer hNnorm hNcop hQp ⟨hmemN, hmemA⟩
  have hmemK : a ^ p ^ k ∈ (Subgroup.centralizer (Q : Set G)).subgroupOf
      (Subgroup.normalizer (Q : Set G)) := by
    rw [Subgroup.mem_subgroupOf]
    simpa only [Subgroup.coe_pow] using hmemC
  rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  exact hmemK

end Work.NPC.Frobenius
