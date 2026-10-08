import Mathlib
import Submission.Work.BG.Defs
import Submission.Work.BG.t_mem_zpowers_of_mem_T
import Submission.Work.GLUE.InBridge
import Submission.OddOrder.Mathlib.Subgroup

/-!
# Area BG: Bender–Glauberman 1981, Hypothesis 1.1 ⟹ Hypothesis 1.2

This file proves `Work.BG.hyp12OfBGData`: given the data of Bender–Glauberman
Hypothesis 1.1 (`Work.GW2.BGData`) together with the centralizer-splitting hypothesis
`Work.GW2.CentralizerSplitProp`, the group satisfies Hypothesis 1.2 for
`H₀ = U S₀`, `H = C_G(t)`, `U = O(H)`: `U ≤ H₀ ⊴ H`, `[H : H₀] = 2`, and `T = H₀ ∖ U`
is a TI-subset of `G` with normalizer `H`.
-/

set_option linter.style.haveILetI false

open scoped Pointwise

namespace Work.BG

open Subgroup

/-! ## Auxiliary arithmetic: the `2`-torsion of a cyclic group has at most one
non-identity element -/

private theorem arith_key (d n : ℕ) (hd : 0 < d) (h1 : d ∣ 2 * n) (h2 : ¬ d ∣ n) :
    n % d = d / 2 := by
  have h2' : n % d ≠ 0 := fun h => h2 (Nat.dvd_of_mod_eq_zero h)
  have h3 : d ∣ 2 * (n % d) := by
    rw [Nat.dvd_iff_mod_eq_zero]
    have hmeq : 2 * (n % d) % d = 2 * n % d := (Nat.ModEq.refl 2).mul (Nat.mod_modEq n d)
    have hzero : 2 * n % d = 0 := Nat.dvd_iff_mod_eq_zero.mp h1
    rw [hmeq, hzero]
  obtain ⟨k, hk⟩ := h3
  have hkpos : 0 < k := by
    have hpos : 0 < 2 * (n % d) := Nat.mul_pos (by norm_num) (Nat.pos_of_ne_zero h2')
    rw [hk] at hpos
    exact Nat.pos_of_ne_zero (fun h => by rw [h, Nat.mul_zero] at hpos; exact lt_irrefl _ hpos)
  have hklt : k < 2 := by
    have hlt : 2 * (n % d) < 2 * d := Nat.mul_lt_mul_of_pos_left (Nat.mod_lt n hd) (by norm_num)
    rw [hk] at hlt
    exact (Nat.mul_lt_mul_left hd).mp (by rw [mul_comm d 2]; exact hlt)
  have hk1 : k = 1 := by omega
  rw [hk1, Nat.mul_one] at hk
  omega

/-- **The `2`-torsion of a cyclic group is trivial or of order two.** If `z` and `w` are two
non-identity involutions in the cyclic group `⟨y⟩`, then `z = w`. -/
theorem eqOfMemZpowersOfSqEqOne {G : Type*} [Group G] [Finite G] {y z w : G}
    (hz : z ∈ Subgroup.zpowers y) (hw : w ∈ Subgroup.zpowers y)
    (hz2 : z ^ 2 = 1) (hw2 : w ^ 2 = 1) (hz1 : z ≠ 1) (hw1 : w ≠ 1) : z = w := by
  let K := Subgroup.zpowers y
  haveI : IsCyclic K := Subgroup.isCyclic_zpowers y
  let z' : K := ⟨z, hz⟩
  let w' : K := ⟨w, hw⟩
  have hordz : orderOf z' = 2 := by
    rw [← Subgroup.orderOf_coe z']
    exact (orderOf_eq_prime_iff (p := 2)).mpr ⟨hz2, hz1⟩
  have hordw : orderOf w' = 2 := by
    rw [← Subgroup.orderOf_coe w']
    exact (orderOf_eq_prime_iff (p := 2)).mpr ⟨hw2, hw1⟩
  have hz'1 : z' ≠ 1 := by intro h; rw [h, orderOf_one] at hordz; omega
  have hw'1 : w' ≠ 1 := by intro h; rw [h, orderOf_one] at hordw; omega
  have hcardz : Nat.card ↥(Subgroup.zpowers z') = 2 := by rw [Nat.card_zpowers]; exact hordz
  have hcardw : Nat.card ↥(Subgroup.zpowers w') = 2 := by rw [Nat.card_zpowers]; exact hordw
  have heq : Subgroup.zpowers z' = Subgroup.zpowers w' := by
    rw [IsCyclic.subgroup_eq_iff_card_eq]; rw [hcardz, hcardw]
  have hmem : z' ∈ Subgroup.zpowers w' := heq ▸ Subgroup.mem_zpowers z'
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hw'2 : w' ^ 2 = 1 := by ext; simpa using hw2
  have hw'2z : w' ^ (2 : ℤ) = 1 := by rw [zpow_two]; simpa [pow_two] using hw'2
  have hk' : z' = w' ^ (k % (2:ℤ)) := by rw [← hk, zpow_eq_zpow_emod k hw'2z]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [h, zpow_zero] at hk'; exact absurd hk' hz'1
  · rw [h, zpow_one] at hk'; exact Subtype.ext_iff.mp hk'

/-- The central involution `t` of `S₀` is central in the dihedral Sylow `2`-subgroup `S`:
`S ≤ C_G(t)`. -/
theorem BGData_S_le_centralizer_t {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) :
    (D.S : Subgroup G) ≤ Subgroup.centralizer ({D.t} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hS0norm : (D.S0.subgroupOf (D.S : Subgroup G)).Normal :=
    Subgroup.normal_of_index_eq_two D.S0_index
  have htconj : x * D.t * x⁻¹ ∈ D.S0 := by
    have hmem : (⟨x, hx⟩ * ⟨D.t, D.S0_le D.t_mem⟩ * ⟨x, hx⟩⁻¹ : ↥(D.S : Subgroup G))
        ∈ D.S0.subgroupOf (D.S : Subgroup G) := by
      refine hS0norm.conj_mem (⟨D.t, D.S0_le D.t_mem⟩ : ↥(D.S : Subgroup G)) ?_ (⟨x, hx⟩ : ↥(D.S : Subgroup G))
      rw [Subgroup.mem_subgroupOf]; exact D.t_mem
    rw [Subgroup.mem_subgroupOf] at hmem
    simpa using hmem
  have ht2 : D.t ^ 2 = 1 := ((orderOf_eq_prime_iff (p:=2)).mp D.t_order).1
  have ht1 : D.t ≠ 1 := ((orderOf_eq_prime_iff (p:=2)).mp D.t_order).2
  have hconj2 : (x * D.t * x⁻¹) ^ 2 = 1 := by
    have hh : (x * D.t * x⁻¹) ^ 2 = x * D.t ^ 2 * x⁻¹ := by rw [pow_two, pow_two]; group
    rw [hh, ht2]; group
  have hconj1 : x * D.t * x⁻¹ ≠ 1 := by
    intro h
    apply ht1
    have h2 : x⁻¹ * (x * D.t * x⁻¹) * x = D.t := by group
    rw [h, mul_one] at h2
    simpa using h2.symm
  have hkey := eqOfMemZpowersOfSqEqOne (y := D.t1 * D.t2)
      (by rw [← D.gen]; exact htconj) (by rw [← D.gen]; exact D.t_mem)
      hconj2 ht2 hconj1 ht1
  calc x * D.t = x * D.t * x⁻¹ * x := by group
    _ = D.t * x := by rw [hkey]

/-- The index computation `[H : H₀] = 2` of Bender–Glauberman Hypothesis 1.2, where
`H = U S` and `H₀ = U S₀`: the two subgroups of `H` differ by the index-two subgroup
`S₀` of `S`. -/
theorem relIndex_H1_H {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G)
    (hUS : D.U ⊔ (D.S : Subgroup G) = D.H) :
    (Work.BG.H1 D).relIndex D.H = 2 := by
  have hS_le_H : (D.S : Subgroup G) ≤ D.H := by rw [← hUS]; exact le_sup_right
  have hS0_le_H : D.S0 ≤ D.H := D.S0_le.trans hS_le_H
  have hH0_le_H : Work.BG.H1 D ≤ D.H := sup_le (Subgroup.map_subtype_le _) hS0_le_H
  have hUnorm : D.U = Work.GW2.oddCoreIn D.H := rfl
  have hSnormU : (D.S : Subgroup G) ≤ Subgroup.normalizer (D.U : Set G) := by
    refine hS_le_H.trans ?_
    rw [hUnorm, Work.GW2.oddCoreIn_eq_opiCoreInG]
    exact OddOrder.GroupTheory.le_normalizer_opiCoreInG _ _
  have hUpi : Subgroup.IsPiSubgroup ({q : ℕ | q ≠ 2}) D.U := by
    rw [hUnorm, Work.GW2.oddCoreIn_eq_opiCoreInG]
    exact OddOrder.GroupTheory.isPiSubgroup_opiCoreInG _ _
  have hUinfS : D.U ⊓ (D.S : Subgroup G) = ⊥ :=
    OddOrder.GroupTheory.inf_eq_bot_of_isPiSubgroup_of_isPiSubgroup_compl hUpi
      (Subgroup.isPiSubgroup_of_isPGroup_of_mem D.S.isPGroup' (by simp))
  have hUinfS0 : D.U ⊓ D.S0 = ⊥ := by
    have hle : D.U ⊓ D.S0 ≤ D.U ⊓ (D.S : Subgroup G) := inf_le_inf_left _ D.S0_le
    rw [hUinfS] at hle
    exact le_bot_iff.mp hle
  have hcardS : Nat.card ↥(D.S : Subgroup G) = 2 * Nat.card ↥D.S0 := by
    have h := Subgroup.relIndex_mul_card D.S0 (D.S : Subgroup G)
    rw [inf_eq_left.mpr D.S0_le, D.S0_index] at h
    exact h.symm
  have hcardUS : Nat.card ↥(D.U ⊔ (D.S : Subgroup G)) =
      Nat.card ↥D.U * Nat.card ↥(D.S : Subgroup G) := by
    have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left D.U (D.S : Subgroup G) hSnormU
    have h := Subgroup.card_HK_mul_card_inf_eq_card_mul_card D.U (D.S : Subgroup G)
    rw [hUinfS, Subgroup.card_bot, mul_one] at h
    rw [← hcoe] at h
    exact h
  have hcardUS0 : Nat.card ↥(D.U ⊔ D.S0) = Nat.card ↥D.U * Nat.card ↥D.S0 := by
    have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left D.U D.S0 (D.S0_le.trans hSnormU)
    have h := Subgroup.card_HK_mul_card_inf_eq_card_mul_card D.U D.S0
    rw [hUinfS0, Subgroup.card_bot, mul_one] at h
    rw [← hcoe] at h
    exact h
  have hHcard : Nat.card ↥D.H = 2 * (Nat.card ↥D.U * Nat.card ↥D.S0) := by
    rw [← hUS, hcardUS, hcardS]; ring
  have hrel := Subgroup.relIndex_mul_card (Work.BG.H1 D) D.H
  rw [inf_eq_left.mpr hH0_le_H, show Work.BG.H1 D = D.U ⊔ D.S0 from rfl, hcardUS0, hHcard] at hrel
  exact Nat.mul_right_cancel (Nat.mul_pos Nat.card_pos Nat.card_pos) hrel

theorem hyp12OfBGData {G : Type} [Group G] [Finite G]
    (hSplit : Work.GW2.CentralizerSplitProp) (D : Work.GW2.BGData G) :
    ∃ P : Work.BG.Hyp12 G, P.H = D.H ∧ P.U = D.U ∧ P.H0 = Work.BG.H1 D := by
  -- `S ≤ H = C_G(t)` and `H = U S` (centralizer splitting).
  have hcentr : ∀ x ∈ (D.S : Subgroup G), x * D.t = D.t * x := by
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (BGData_S_le_centralizer_t D hx) D.t
      (Set.mem_singleton D.t)).symm
  have hUS : D.U ⊔ (D.S : Subgroup G) = D.H :=
    hSplit G D.S D.n D.two_le D.dih D.t (D.S0_le D.t_mem) D.t_order hcentr
  have hS_le_H : (D.S : Subgroup G) ≤ D.H := by rw [← hUS]; exact le_sup_right
  have hS0_le_H : D.S0 ≤ D.H := D.S0_le.trans hS_le_H
  have hH0_le_H : Work.BG.H1 D ≤ D.H := sup_le (Subgroup.map_subtype_le _) hS0_le_H
  have hrel : (Work.BG.H1 D).relIndex D.H = 2 := relIndex_H1_H D hUS
  have hH0norm : ((Work.BG.H1 D).subgroupOf D.H).Normal :=
    Subgroup.normal_of_index_eq_two hrel
  -- `H` normalizes `U`.
  have hUnorm : D.U = Work.GW2.oddCoreIn D.H := rfl
  have hH_le_normU : D.H ≤ Subgroup.normalizer (D.U : Set G) := by
    rw [hUnorm, Work.GW2.oddCoreIn_eq_opiCoreInG]
    exact OddOrder.GroupTheory.le_normalizer_opiCoreInG _ _
  have hUpi : Subgroup.IsPiSubgroup ({q : ℕ | q ≠ 2}) D.U := by
    rw [hUnorm, Work.GW2.oddCoreIn_eq_opiCoreInG]
    exact OddOrder.GroupTheory.isPiSubgroup_opiCoreInG _ _
  have hOddU : Odd (Nat.card ↥D.U) :=
    (Work.GW2.odd_card_iff_isPiSubgroup_ne_two D.U).mpr hUpi
  have ht2 : D.t ^ 2 = 1 := ((orderOf_eq_prime_iff (p:=2)).mp D.t_order).1
  have ht1 : D.t ≠ 1 := ((orderOf_eq_prime_iff (p:=2)).mp D.t_order).2
  have ht_mem_H0 : D.t ∈ Work.BG.H1 D := (le_sup_right (a := D.U) (b := D.S0)) D.t_mem
  have ht_notU : D.t ∉ D.U := by
    intro hmem
    have hle : Subgroup.zpowers D.t ≤ D.U := Subgroup.zpowers_le.mpr hmem
    have hdvd : Nat.card ↥(Subgroup.zpowers D.t) ∣ Nat.card ↥D.U := Subgroup.card_dvd_of_le hle
    rw [Nat.card_zpowers, D.t_order] at hdvd
    have h1 : Nat.card ↥D.U % 2 = 1 := Nat.odd_iff.mp hOddU
    have h2 : Nat.card ↥D.U % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
    omega
  have hT_nonempty : (Work.BG.Tset (Work.BG.H1 D) D.U).Nonempty := ⟨D.t, ht_mem_H0, ht_notU⟩
  -- `H` normalizes `T`.
  have hH_normT : ∀ l ∈ D.H, ∀ a ∈ Work.BG.Tset (Work.BG.H1 D) D.U,
      l * a * l⁻¹ ∈ Work.BG.Tset (Work.BG.H1 D) D.U := by
    intro l hl a ha
    refine ⟨?_, ?_⟩
    · have hmem : (⟨l, hl⟩ * ⟨a, hH0_le_H ha.1⟩ * ⟨l, hl⟩⁻¹ : ↥D.H) ∈ (Work.BG.H1 D).subgroupOf D.H :=
        hH0norm.conj_mem ⟨a, hH0_le_H ha.1⟩ (by rw [Subgroup.mem_subgroupOf]; exact ha.1) ⟨l, hl⟩
      rw [Subgroup.mem_subgroupOf] at hmem
      simpa using hmem
    · intro hmem
      exact ha.2 ((Subgroup.mem_normalizer_iff.mp (hH_le_normU hl) a).mpr hmem)
  -- `T` is a TI-subset with normalizer bound `H`.
  have hTI : OddOrder.GroupTheory.IsTISubset (Work.BG.Tset (Work.BG.H1 D) D.U) D.H := by
    intro g ⟨a, ha, hga⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨p, hp⟩ := Subgroup.mem_zpowers_iff.mp (t_mem_zpowers_of_mem_T D ha)
    have hy : D.t ∈ Subgroup.zpowers (g * a * g⁻¹) := t_mem_zpowers_of_mem_T D hga
    have hgp : (g * a * g⁻¹) ^ p = g * D.t * g⁻¹ := by
      have h1 : (g * a * g⁻¹) = MulAut.conj g a := (MulAut.conj_apply g a).symm
      rw [h1, ← map_zpow, hp, MulAut.conj_apply]
    have hz2 : ((g * a * g⁻¹) ^ p) ^ 2 = 1 := by
      have hh : (g * D.t * g⁻¹) ^ 2 = g * D.t ^ 2 * g⁻¹ := by rw [pow_two, pow_two]; group
      rw [hgp, hh, ht2]; group
    have hz1 : (g * a * g⁻¹) ^ p ≠ 1 := by
      rw [hgp]
      intro h
      apply ht1
      have h2 : g⁻¹ * (g * D.t * g⁻¹) * g = D.t := by group
      rw [h, mul_one] at h2
      simpa using h2.symm
    have heq := eqOfMemZpowersOfSqEqOne (y := g * a * g⁻¹)
      (Subgroup.mem_zpowers_iff.mpr ⟨p, rfl⟩) hy hz2 ht2 hz1 ht1
    have hfix : g * D.t * g⁻¹ = D.t := hgp.symm.trans heq
    calc g * D.t = g * D.t * g⁻¹ * g := by group
      _ = D.t * g := by rw [hfix]
  have hnormT : Subgroup.normalizer (Work.BG.Tset (Work.BG.H1 D) D.U) = D.H :=
    OddOrder.GroupTheory.IsTISubset.set_normalizer_eq_of_nonempty_of_normalizes
      hTI hT_nonempty hH_normT
  exact ⟨{ H0 := Work.BG.H1 D, H := D.H, U := D.U,
           U_le_H0 := le_sup_left,
           H0_le_H := hH0_le_H,
           H0_normal := hH0norm,
           H0_relIndex := hrel,
           TI := hTI,
           normalizer_T := hnormT }, rfl, rfl, rfl⟩

end Work.BG
