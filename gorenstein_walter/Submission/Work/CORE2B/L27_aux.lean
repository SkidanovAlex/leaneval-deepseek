import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.BenderCtx_sylow_not_cyclic
import Submission.Work.RED.DihedralSubgroup
import Submission.Work.Dihedral.Defs

/-!
# AREA CORE2B — auxiliary group-theoretic lemmas for `L27_normal_contains_t`

* `unique_involution_of_cyclic`: a finite cyclic group has at most one element of order two.
* `center_of_cyclic_index_two`: the unique involution of a cyclic index-two subgroup `S₀ ≤ S` is
  central in `S`.
* `twoResidual_le_map_of_index_two`: `O²(G) ≤ O²(K).map K.subtype` for `K ≤ G` of index two.
* `twoResidual_odd_of_cyclic_sylow_two` (Burnside): a group with cyclic Sylow `2`-subgroup has
  `O²(G)` of odd order.
* `center_involution_unique_dihedral`, `center_unique_of_dihedral_subgroup`: the centre of a
  subgroup of a dihedral group of order `≥ 8` has at most one involution.
-/

open scoped MatrixGroups

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.CORE2B

open Subgroup

/-! ## 1. Elementary facts about cyclic index-two subgroups -/

/-- A finite cyclic group has at most one element of order two. -/
theorem unique_involution_of_cyclic {H : Type*} [Group H] [Finite H] [IsCyclic H]
    {a b : H} (ha : orderOf a = 2) (hb : orderOf b = 2) : a = b := by
  classical
  haveI : Fintype H := Fintype.ofFinite H
  have hd : 2 ∣ Fintype.card H := by
    rw [← Nat.card_eq_fintype_card, ← ha]
    exact orderOf_dvd_natCard a
  have hcard : Fintype.card {x : H // orderOf x = 2} = 1 := by
    rw [Fintype.card_subtype, IsCyclic.card_orderOf_eq_totient (α := H) hd, Nat.totient_two]
  exact Subtype.ext_iff.mp (Fintype.card_le_one_iff.mp (le_of_eq hcard) ⟨a, ha⟩ ⟨b, hb⟩)

/-- `t`, the unique involution of a cyclic index-two subgroup `S₀ ≤ S`, is central in `S`. -/
theorem center_of_cyclic_index_two {G : Type*} [Group G]
    (S S0 : Subgroup G) (hS0 : S0 ≤ S) (hidx : S0.relIndex S = 2) {t : G} (ht : t ∈ S0)
    (ht2 : orderOf t = 2) (huniq : ∀ x ∈ S0, orderOf x = 2 → x = t) :
    ∀ y ∈ S, y * t = t * y := by
  intro y hy
  have hN : (S0.subgroupOf S).Normal := Subgroup.normal_of_index_eq_two hidx
  have hconj : y * t * y⁻¹ ∈ S0 := by
    have h := hN.conj_mem (⟨t, hS0 ht⟩ : ↥S)
      (by rw [Subgroup.mem_subgroupOf]; exact ht) (⟨y, hy⟩ : ↥S)
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h
  have hsem : SemiconjBy y t (y * t * y⁻¹) := by
    show y * t = (y * t * y⁻¹) * y
    group
  have hord : orderOf (y * t * y⁻¹) = 2 := (SemiconjBy.orderOf_eq y hsem).symm.trans ht2
  have hEq : y * t * y⁻¹ = t := huniq (y * t * y⁻¹) hconj hord
  calc y * t = (y * t * y⁻¹) * y := by group
    _ = t * y := by rw [hEq]

/-! ## 2. The `2`-residual and index-two subgroups -/

/-- `O²(G)` is contained in the image of `O²(K)` when `K ≤ G` has index two: every element of
odd order lies in `K` (its image in `G/K` has order dividing both an odd number and `2`). -/
theorem twoResidual_le_map_of_index_two {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) (hK : K.Normal) (hidx : K.index = 2) :
    Work.GW2.twoResidual G ≤ (Work.GW2.twoResidual ↥K).map K.subtype := by
  haveI : K.Normal := hK
  rw [Work.GW2.twoResidual, Subgroup.closure_le]
  intro g hg
  have hgord : Odd (orderOf g) := hg
  have hgK : g ∈ K := by
    have h1 : orderOf ((QuotientGroup.mk' K) g) ∣ 2 := by
      rw [← hidx, Subgroup.index_eq_card K]
      exact orderOf_dvd_natCard _
    have h2 : orderOf ((QuotientGroup.mk' K) g) ∣ orderOf g := orderOf_map_dvd _ g
    have hodd : Odd (orderOf ((QuotientGroup.mk' K) g)) := Odd.of_dvd_nat hgord h2
    have hone : orderOf ((QuotientGroup.mk' K) g) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
      · exact h
      · rw [h] at hodd; exact absurd hodd (by norm_num)
    have hmem : g ∈ (QuotientGroup.mk' K).ker := by
      rw [MonoidHom.mem_ker]
      show ((QuotientGroup.mk' K) g : G ⧸ K) = 1
      exact orderOf_eq_one_iff.mp hone
    rwa [QuotientGroup.ker_mk'] at hmem
  refine Subgroup.mem_map.mpr ⟨(⟨g, hgK⟩ : ↥K), ?_, rfl⟩
  refine Subgroup.subset_closure (show Odd (orderOf (⟨g, hgK⟩ : ↥K)) from ?_)
  rw [Subgroup.orderOf_mk g hgK]; exact hgord


/-! ## 3. Uniqueness of central involutions of subgroups of a dihedral group -/

/-- In `DihedralGroup m` with `m ≥ 4`, the centre has at most one involution. -/
theorem center_involution_unique_dihedral {m : ℕ} (hm : 4 ≤ m) {a b : DihedralGroup m}
    (ha : a ∈ Subgroup.center (DihedralGroup m)) (hb : b ∈ Subgroup.center (DihedralGroup m))
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) : a = b := by
  rcases Nat.even_or_odd m with hev | hodd
  · rw [DihedralGroup.center_eq_closure_of_even_ne_two hev (by omega)] at ha hb
    rw [Subgroup.mem_zpowers_iff] at ha hb
    obtain ⟨i, hi⟩ := ha
    obtain ⟨j, hj⟩ := hb
    set z : DihedralGroup m := DihedralGroup.r ((m / 2 : ℕ) : ZMod m) with hz
    have hord : orderOf z = 2 := by
      apply orderOf_eq_prime
      · rw [hz, sq, DihedralGroup.r_mul_r]
        have h2 : ((m / 2 : ℕ) : ZMod m) + ((m / 2 : ℕ) : ZMod m) = 0 := by
          have hm2 : m / 2 + m / 2 = m := by
            have h := Nat.div_mul_cancel (even_iff_two_dvd.mp hev)
            omega
          rw [← Nat.cast_add, hm2, ZMod.natCast_self]
        rw [h2, DihedralGroup.r_zero]
      · intro h1
        rw [hz] at h1
        have h2 : ((m / 2 : ℕ) : ZMod m) = 0 := DihedralGroup.r.inj h1
        have h3 : m ∣ m / 2 := (ZMod.natCast_eq_zero_iff (m / 2) m).mp h2
        have := Nat.le_of_dvd (by omega) h3
        omega
    have key : ∀ k : ℤ, z ^ k = z ^ (k % 2) := fun k => by
      rw [← zpow_mod_orderOf z k]
      congr 1
      rw [hord]
      norm_num
    have ha' : a = z := by
      have hodd2 : i % 2 = 1 := by
        rcases Int.emod_two_eq_zero_or_one i with h0 | h1
        · exfalso
          have h1' : a = 1 := by rw [← hi, key i, h0, zpow_zero]
          rw [h1', orderOf_one] at ha2
          norm_num at ha2
        · exact h1
      rw [← hi, key i, hodd2, zpow_one]
    have hb' : b = z := by
      have hodd2 : j % 2 = 1 := by
        rcases Int.emod_two_eq_zero_or_one j with h0 | h1
        · exfalso
          have h1' : b = 1 := by rw [← hj, key j, h0, zpow_zero]
          rw [h1', orderOf_one] at hb2
          norm_num at hb2
        · exact h1
      rw [← hj, key j, hodd2, zpow_one]
    rw [ha', hb']
  · rw [DihedralGroup.center_eq_bot_of_odd_ne_one hodd (by omega)] at ha hb
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb]

/-- In a subgroup `Q` of a dihedral group with `|Q| ≥ 8`, the centre has at most one
involution. -/
theorem center_unique_of_dihedral_subgroup {G : Type*} [Group G] [Finite G]
    {S Q : Subgroup G} {n : ℕ} (hS : Nonempty (S ≃* DihedralGroup n)) (hn : 2 ≤ n)
    (hQ : Q ≤ S) (hcard : 8 ≤ Nat.card Q) {a b : G}
    (haQ : a ∈ Q) (hbQ : b ∈ Q) (ha : ∀ y ∈ Q, y * a = a * y) (hb : ∀ y ∈ Q, y * b = b * y)
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) : a = b := by
  classical
  obtain ⟨e⟩ := hS
  haveI : NeZero n := ⟨by omega⟩
  have hψ : ↥Q ≃* ↥((Q.subgroupOf S).map e.toMonoidHom) :=
    (Subgroup.subgroupOfEquivOfLe hQ).symm.trans
      (Subgroup.equivMapOfInjective (Q.subgroupOf S) e.toMonoidHom e.injective)
  rcases Work.RED.DihedralSubgroup n ((Q.subgroupOf S).map e.toMonoidHom) with hcyc | ⟨m, ⟨f⟩⟩
  · -- `Q` is cyclic
    haveI : IsCyclic ↥Q := (MulEquiv.isCyclic hψ).mpr hcyc
    have h1 : (⟨a, haQ⟩ : ↥Q) = ⟨b, hbQ⟩ :=
      unique_involution_of_cyclic (H := ↥Q)
        (by rw [← Subgroup.orderOf_coe (⟨a, haQ⟩ : ↥Q)]; exact ha2)
        (by rw [← Subgroup.orderOf_coe (⟨b, hbQ⟩ : ↥Q)]; exact hb2)
    exact Subtype.ext_iff.mp h1
  · -- `Q ≅ DihedralGroup m`
    have hm : 4 ≤ m := by
      have hcard' : Nat.card ↥((Q.subgroupOf S).map e.toMonoidHom) = Nat.card ↥Q := by
        rw [Subgroup.card_map_of_injective e.injective]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ).toEquiv
      have h1 : Nat.card ↥((Q.subgroupOf S).map e.toMonoidHom) = 2 * m := by
        rw [Nat.card_congr f.toEquiv, DihedralGroup.nat_card]
      omega
    set ψ : ↥Q ≃* DihedralGroup m := hψ.trans f with hψdef
    have hcena : (⟨a, haQ⟩ : ↥Q) ∈ Subgroup.center ↥Q := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (ha (y : G) y.2)
    have hcenb : (⟨b, hbQ⟩ : ↥Q) ∈ Subgroup.center ↥Q := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hb (y : G) y.2)
    have hca : ψ (⟨a, haQ⟩ : ↥Q) ∈ Subgroup.center (DihedralGroup m) := by
      rw [Subgroup.mem_center_iff]
      intro x
      obtain ⟨y, rfl⟩ := ψ.surjective x
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hcena y]
    have hcb : ψ (⟨b, hbQ⟩ : ↥Q) ∈ Subgroup.center (DihedralGroup m) := by
      rw [Subgroup.mem_center_iff]
      intro x
      obtain ⟨y, rfl⟩ := ψ.surjective x
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hcenb y]
    have hoa : orderOf (ψ (⟨a, haQ⟩ : ↥Q)) = 2 := by
      rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe (⟨a, haQ⟩ : ↥Q)]; exact ha2
    have hob : orderOf (ψ (⟨b, hbQ⟩ : ↥Q)) = 2 := by
      rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe (⟨b, hbQ⟩ : ↥Q)]; exact hb2
    have h1 : ψ (⟨a, haQ⟩ : ↥Q) = ψ (⟨b, hbQ⟩ : ↥Q) :=
      center_involution_unique_dihedral hm hca hcb hoa hob
    exact Subtype.ext_iff.mp (ψ.injective h1)

/-! ## 3. Burnside's normal `2`-complement theorem in the form we need -/

/-- If `G` has a cyclic Sylow 2-subgroup then `O²(G)` has odd order (Burnside's normal
`2`-complement theorem). -/
theorem twoResidual_odd_of_cyclic_sylow_two {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (hcyc : IsCyclic ↥(P : Subgroup G)) :
    Odd (Nat.card ↥(Work.GW2.twoResidual G)) := by
  by_cases hodd : Odd (Nat.card G)
  · have htop : Work.GW2.twoResidual G = ⊤ := by
      rw [Work.GW2.twoResidual, eq_top_iff]
      intro g _
      exact Subgroup.subset_closure (Odd.of_dvd_nat hodd (orderOf_dvd_natCard g))
    rw [htop, Subgroup.card_top]; exact hodd
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp2 : (Nat.card G).minFac = 2 :=
      Nat.minFac_eq_two_iff _ |>.mpr (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd))
    have hle : Subgroup.normalizer (P : Set G) ≤ Subgroup.centralizer (P : Set G) :=
      IsCyclic.normalizer_le_centralizer (G := G) hp2 hcyc
    set K : Subgroup G := (MonoidHom.transferSylow P hle).ker with hKdef
    haveI hKnorm : K.Normal := by rw [hKdef]; exact MonoidHom.normal_ker _
    have hcomp : K.IsComplement' (P : Subgroup G) :=
      MonoidHom.ker_transferSylow_isComplement' P hle
    have hcard : Nat.card (G ⧸ K) = Nat.card ↥(P : Subgroup G) := by
      rw [← Subgroup.index_eq_card K, hcomp.symm.index_eq_card]
    have hQuot : Work.GW2.twoResidual G ≤ K := by
      rw [Work.GW2.twoResidual, Subgroup.closure_le]
      intro g hg
      have hgord : Odd (orderOf g) := hg
      have h1 : orderOf ((QuotientGroup.mk' K) g) ∣ Nat.card (G ⧸ K) := orderOf_dvd_natCard _
      rw [hcard] at h1
      have h2 : orderOf ((QuotientGroup.mk' K) g) ∣ orderOf g := orderOf_map_dvd _ g
      have hodd' : Odd (orderOf ((QuotientGroup.mk' K) g)) := Odd.of_dvd_nat hgord h2
      have hone : orderOf ((QuotientGroup.mk' K) g) = 1 := by
        obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
        have hpow : orderOf ((QuotientGroup.mk' K) g) ∣ 2 ^ k := by rw [← hk]; exact h1
        exact ((Nat.coprime_two_right.mpr hodd').pow_right k).eq_one_of_dvd hpow
      have hmem : g ∈ (QuotientGroup.mk' K).ker := by
        rw [MonoidHom.mem_ker]
        show ((QuotientGroup.mk' K) g : G ⧸ K) = 1
        exact orderOf_eq_one_iff.mp hone
      rwa [QuotientGroup.ker_mk'] at hmem
    have hKodd : ¬ 2 ∣ Nat.card ↥K := by
      rw [hKdef]; exact MonoidHom.not_dvd_card_ker_transferSylow P hle
    have h2 : ¬ 2 ∣ Nat.card ↥(Work.GW2.twoResidual G) :=
      fun h => hKodd (h.trans (Subgroup.card_dvd_of_le hQuot))
    exact Nat.not_even_iff_odd.mp fun he => h2 (even_iff_two_dvd.mp he)

end Work.CORE2B
