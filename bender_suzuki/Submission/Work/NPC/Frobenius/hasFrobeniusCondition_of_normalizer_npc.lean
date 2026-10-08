/-
Area A9 of the Feit--Thompson drive: the implication
"local normal `p`-complements ⟹ Frobenius' condition".

## Main result

* `Work.NPC.Frobenius.hasFrobeniusCondition_of_normalizer_npc`: if `N_G(Q)` has a normal
  `p`-complement for every non-identity `p`-subgroup `Q ≤ G`, then Frobenius' condition
  `HasFrobeniusCondition p G` holds, i.e. `N_G(Q)/C_G(Q)` is a `p`-group for every non-identity
  `p`-subgroup `Q`.

The mathematical content is the same commutator computation as in
`Work.NPC.Frobenius.hasFrobeniusCondition_of_hasNormalPComplement`, but performed inside the
normalizer `H = N_G(Q)` rather than in the ambient group:

let `H = N_G(Q)` and let `N ⊴ H` be a normal `p`-complement of `H`.  Since `Q ≤ H` is a
`p`-subgroup and `|N|` is coprime to `p`, the intersection `N ∩ Q` is trivial.  Hence for
`x ∈ N` and `q ∈ Q` the commutator `[x, q] = x*q*x⁻¹*q⁻¹` lies in `N` (because `N ⊴ H` and
`q ∈ H`) and in `Q` (because `x ∈ H = N_G(Q)`), so it is trivial and `N ≤ C_G(Q) ≤ H`.
Therefore `H/C_H(Q) = H/(C_G(Q) ∩ H)` is a quotient of `H/N`, which is a `p`-group by
hypothesis; a quotient of a `p`-group is a `p`-group.
-/
import Mathlib
import Submission.Work.NPC.Defs
import Submission.Work.NPC.Frobenius.hasFrobeniusCondition_of_hasNormalPComplement

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

open scoped Pointwise

namespace Work.NPC.Frobenius

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- **The key point, relative form.**  Let `H ≤ G`, let `N ⊴ H` have order coprime to the prime
`p`, and let `Q ≤ H` be a `p`-subgroup which is normalized by `H`.  Then the image of `N` in `G`
centralizes `Q`: `N ≤ C_G(Q)`.

Indeed for `x ∈ N` and `q ∈ Q` the commutator `[x, q] = x * q * x⁻¹ * q⁻¹` lies in `N` (it is the
product of `x` with the conjugate of `x⁻¹` by `q ∈ H`, and `N ⊴ H`) and in `Q` (`x ∈ H` normalizes
`Q`, and `Q` is a subgroup), while `N ∩ Q = ⊥` because `|N ∩ Q|` divides both `|N|` (coprime to
`p`) and `|Q|` (a power of `p`).  Hence `[x, q] = 1`. -/
theorem map_subtype_le_centralizer_of_normal {H : Subgroup G} {N : Subgroup ↥H}
    (hN : N.Normal) (hcop : (Nat.card N).Coprime p) {Q : Subgroup G}
    (hQH : Q ≤ H) (hQp : IsPGroup p Q) (hH : H ≤ Subgroup.normalizer (Q : Set G)) :
    N.map H.subtype ≤ Subgroup.centralizer (Q : Set G) := by
  -- `N ∩ Q = ⊥`, since `|N|` is coprime to `|Q| = p ^ m`.
  obtain ⟨m, hm⟩ := hQp.exists_card_eq
  have hdisj : N.map H.subtype ⊓ Q = ⊥ := by
    rw [← disjoint_iff]
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [Subgroup.card_map_of_injective H.subtype_injective, hm]
    exact hcop.pow_right m
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hqH : q ∈ H := hQH hq
  -- `x ∈ H` normalizes `Q`, so `x * q * x⁻¹ ∈ Q`.
  have hxH : (x : G) ∈ Subgroup.normalizer (Q : Set G) := hH x.2
  have hxq : (x : G) * q * (x : G)⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp hxH q).mp hq
  -- The commutator `x * q * x⁻¹ * q⁻¹`, computed in `↥H`, lies in `N`.
  have hwN : x * ⟨q, hqH⟩ * x⁻¹ * ⟨q, hqH⟩⁻¹ ∈ N := by
    have h1 : x * (⟨q, hqH⟩ * x⁻¹ * ⟨q, hqH⟩⁻¹) ∈ N :=
      N.mul_mem hx (hN.conj_mem x⁻¹ (N.inv_mem hx) ⟨q, hqH⟩)
    simpa only [mul_assoc] using h1
  have hw : ((x * ⟨q, hqH⟩ * x⁻¹ * ⟨q, hqH⟩⁻¹ : ↥H) : G)
      = (x : G) * q * (x : G)⁻¹ * q⁻¹ := by
    simp
  -- It also lies in `Q`, hence it is trivial.
  have hcomm : (x : G) * q * (x : G)⁻¹ * q⁻¹ = 1 := by
    have hmem : (x : G) * q * (x : G)⁻¹ * q⁻¹ ∈ N.map H.subtype ⊓ Q :=
      ⟨Subgroup.mem_map.mpr ⟨x * ⟨q, hqH⟩ * x⁻¹ * ⟨q, hqH⟩⁻¹, hwN, hw⟩,
        Q.mul_mem hxq (Q.inv_mem hq)⟩
    rw [hdisj] at hmem
    exact Subgroup.mem_bot.mp hmem
  -- `x * q * x⁻¹ = q`, i.e. `x` and `q` commute.
  calc q * (x : G) = ((x : G) * q * (x : G)⁻¹) * (x : G) := by
        rw [mul_inv_eq_one.mp hcomm]
    _ = (x : G) * q := by group

theorem hasFrobeniusCondition_of_normalizer_npc {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (h : ∀ Q : Subgroup G, IsPGroup p Q → Q ≠ ⊥ →
      Work.NPC.HasNormalPComplement p ↥(Subgroup.normalizer (Q : Set G))) :
    Work.NPC.HasFrobeniusCondition p G := by
  intro Q hQp hQne
  show IsPGroup p (Subgroup.normalizer (Q : Set G) ⧸
    (Subgroup.centralizer (Q : Set G)).subgroupOf (Subgroup.normalizer (Q : Set G)))
  -- A normal `p`-complement `N` of the normalizer `H = N_G(Q)`.
  obtain ⟨N, hNnorm, hNcop, hNquot⟩ := h Q hQp hQne
  haveI : N.Normal := hNnorm
  -- `N` centralizes `Q` (inside `G`), hence lies in `C_H(Q) = C_G(Q) ∩ H`.
  have hcen : N.map (Subgroup.normalizer (Q : Set G)).subtype ≤
      Subgroup.centralizer (Q : Set G) :=
    map_subtype_le_centralizer_of_normal hNnorm hNcop Subgroup.le_normalizer hQp le_rfl
  have hNC : N ≤ (Subgroup.centralizer (Q : Set G)).subgroupOf
      (Subgroup.normalizer (Q : Set G)) := by
    rw [← Subgroup.comap_subtype]
    exact Subgroup.map_le_iff_le_comap.mp hcen
  -- So `N_G(Q)/C_G(Q)` is a quotient of the `p`-group `N_G(Q)/N`.
  exact hNquot.of_surjective
    (QuotientGroup.map N
      ((Subgroup.centralizer (Q : Set G)).subgroupOf (Subgroup.normalizer (Q : Set G)))
      (MonoidHom.id ↥(Subgroup.normalizer (Q : Set G))) (by simpa using hNC))
    (by
      intro y
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ y
      exact ⟨QuotientGroup.mk' N a, by rw [QuotientGroup.map_mk']; rfl⟩)

end Work.NPC.Frobenius
