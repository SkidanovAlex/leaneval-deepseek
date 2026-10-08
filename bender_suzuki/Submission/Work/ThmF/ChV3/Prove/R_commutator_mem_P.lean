import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV3.Prove

open scoped commutatorElement

/-- If `N` is a normal subgroup of a group `H` such that `H ⧸ N` has order `p ^ 2` for a
prime `p`, then `H ⧸ N` is commutative, and consequently the image of every commutator
`⁅a, b⁆` of elements of `H` lies in `N`. -/
theorem commutator_mem_of_card_quotient {H : Type*} [Group H] (N : Subgroup H) [N.Normal]
    {p : ℕ} [Fact p.Prime] (hcard : Nat.card (H ⧸ N) = p ^ 2) :
    ∀ a b : H, ⁅a, b⁆ ∈ N := by
  intro a b
  -- A group of order `p ^ 2` is commutative.
  have hcomm : ∀ x y : H ⧸ N, x * y = y * x :=
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard).is_comm.comm
  have h1 : (QuotientGroup.mk' N) ⁅a, b⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm _ _)
  have h2 : ⁅a, b⁆ ∈ (QuotientGroup.mk' N).ker := MonoidHom.mem_ker.mpr h1
  rwa [QuotientGroup.ker_mk' N] at h2

/-- If `R` is a subgroup of order `27` whose center (realised as
`centralizer R ⊓ R` inside the ambient group) has order `3`, then every commutator of two
elements of `R` lies in that center.

Indeed `R` has order `3 ^ 3` and its center has order `3`, so `R / Z(R)` has order `9 = 3 ^ 2`
and is therefore abelian; hence `[R, R] ≤ Z(R)`. -/
theorem R_commutator_mem_P {G : Type} [Group G] [Finite G] {R P : Subgroup G}
    (hcardR : Nat.card R = 27) (hcardP : Nat.card P = 3)
    (hZR : Subgroup.centralizer (R : Set G) ⊓ R = P) :
    ∀ a ∈ R, ∀ b ∈ R, a * b * a⁻¹ * b⁻¹ ∈ P := by
  -- `P` is contained in `R` and centralizes `R`.
  have hPR : P ≤ R := hZR ▸ inf_le_right
  have hPcent : P ≤ Subgroup.centralizer (R : Set G) := hZR ▸ inf_le_left
  -- Regard `P` as a subgroup of the abstract group `↥R`.
  let N : Subgroup ↥R := P.subgroupOf R
  -- `P` is central in `R`, so `N` lies in the center of `↥R` (and is normal).
  have hNle : N ≤ Subgroup.center ↥R := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hxP : (x : G) ∈ P := Subgroup.mem_subgroupOf.mp hx
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hPcent hxP) (y : G) y.2)
  have hNnormal : N.Normal := Subgroup.normal_of_le_center hNle
  -- `N` has the same cardinality as `P`, namely `3`.
  have hcardN : Nat.card N = 3 := by
    rw [← hcardP]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPR).toEquiv
  have hcardR' : Nat.card ↥R = 27 := hcardR
  -- Hence `↥R ⧸ N` has order `9 = 3 ^ 2`.
  have hcard_quot : Nat.card (↥R ⧸ N) = 3 ^ 2 := by
    rw [← Subgroup.index_eq_card N]
    have h := Subgroup.index_mul_card N
    rw [hcardN, hcardR'] at h
    omega
  intro a ha b hb
  -- The commutator of the corresponding elements of `↥R` lies in `N = P.subgroupOf R`,
  -- i.e. its image in `G` lies in `P`.
  have key : ⁅(⟨a, ha⟩ : ↥R), (⟨b, hb⟩ : ↥R)⁆ ∈ N :=
    commutator_mem_of_card_quotient N hcard_quot _ _
  have hmem : ((⁅(⟨a, ha⟩ : ↥R), (⟨b, hb⟩ : ↥R)⁆ : ↥R) : G) ∈ P :=
    Subgroup.mem_subgroupOf.mp key
  have hval : ((⁅(⟨a, ha⟩ : ↥R), (⟨b, hb⟩ : ↥R)⁆ : ↥R) : G) = ⁅a, b⁆ :=
    map_commutatorElement R.subtype (⟨a, ha⟩ : ↥R) (⟨b, hb⟩ : ↥R)
  rw [hval] at hmem
  rwa [commutatorElement_def] at hmem

end Work.ThmF.ChV3.Prove
