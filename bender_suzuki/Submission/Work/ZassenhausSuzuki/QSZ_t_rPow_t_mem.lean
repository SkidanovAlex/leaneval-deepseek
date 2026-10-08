import Mathlib
import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ZassenhausSuzuki.twoPoint_inverted
import Submission.Work.ZassenhausSuzuki.exists_conjAction
import Submission.Work.ZassenhausSuzuki.QSZ_invH_le_centerQ
import Submission.Work.ZassenhausSuzuki.QSZ_abelian_fpf_isCyclic
import Submission.Work.ZassenhausSuzuki.cyclic_pow_involution
import Submission.Work.ZassenhausSuzuki.mem_H_centralizer_st
import Submission.Work.ZassenhausPSL2.Feit.centralizer_eq_Q
import Submission.Work.ThmF.Bender.DTransitiveInv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Submission.Blueprint

namespace Work.ZassenhausSuzuki

open LeanEval.GroupTheory.Defs

private theorem QSZ_aux {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (H Q : Subgroup G) (t : G) (h : Submission.Blueprint.IsSplitRankOne H Q t)
    (hZ : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {s r : G} (hsQ : s ∈ Q) (hs2 : orderOf s = 2) (hrQ : r ∈ Q)
    (hsr : t * s * t⁻¹ = r⁻¹ * t * r)
    (a : ℕ) (ha : orderOf r = 2 ^ a) (ha1 : 1 ≤ a) :
    s = r ^ 2 ^ (a - 1) := by
  have ht2 : t * t = 1 := by
    have hh := pow_orderOf_eq_one t
    rw [h.invol] at hh
    simpa [pow_two] using hh
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hss : s * s = 1 := by
    have hh := pow_orderOf_eq_one s
    rw [hs2] at hh
    simpa [pow_two] using hh
  have hs_inv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hsr' : t * s * t = r⁻¹ * t * r := by simpa [htinv] using hsr
  have hs_ne : s ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at hs2; exact absurd hs2 (by norm_num)
  have hsc : ∀ y ∈ Q, s * y = y * s := by
    have hu : s ∈ involutions (H : Set G) := ⟨h.le hsQ, hs2⟩
    have hc := QSZ_invH_le_centerQ h h2 s hu
    rw [Work.ThmF.mem_centerOf] at hc
    exact hc.2
  have hsus : s * (s * t) * s⁻¹ = (s * t)⁻¹ := by
    rw [mul_inv_rev, hs_inv, htinv]
    rw [show s * (s * t) * s = (s * s) * (t * s) from by group, hss, one_mul]
  have hrus : r⁻¹ * (s * t) * r = (s * t) ^ 2 := by
    have h1 : r⁻¹ * (s * t) * r = s * (r⁻¹ * t * r) := by
      calc r⁻¹ * (s * t) * r = (r⁻¹ * s) * (t * r) := by group
        _ = (s * r⁻¹) * (t * r) := by rw [← hsc r⁻¹ (Q.inv_mem hrQ)]
        _ = s * (r⁻¹ * t * r) := by group
    rw [h1, ← hsr', pow_two]; group
  have hst_ne : s * t ≠ 1 := by
    intro h1
    exact h.not_mem (by
      rw [show t = s⁻¹ * (s * t) from by group, h1, mul_one, hs_inv]
      exact h.le hsQ)
  set U : Subgroup G := Subgroup.zpowers (s * t) with hU
  set B : Subgroup G := Subgroup.closure ({r, s} : Set G) with hB
  have hrB : r ∈ B := Subgroup.subset_closure (by simp)
  have hsB : s ∈ B := Subgroup.subset_closure (by simp)
  have hs_conj : ∀ k ∈ U, s * k * s⁻¹ ∈ U := by
    intro k hk
    rw [hU] at hk ⊢
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hk
    rw [← hm]
    have h1 : s * (s * t) ^ m * s⁻¹ = ((s * t)⁻¹) ^ m := by
      rw [show s * (s * t) ^ m * s⁻¹ = (MulAut.conj s) ((s * t) ^ m) from by
        rw [MulAut.conj_apply]]
      rw [map_zpow, MulAut.conj_apply, hsus]
    refine Subgroup.mem_zpowers_iff.mpr ⟨-m, ?_⟩
    show (s * t) ^ (-m) = s * (s * t) ^ m * s⁻¹
    rw [h1, inv_zpow, zpow_neg]
  have hr_conj_inv : ∀ k ∈ U, r⁻¹ * k * r ∈ U := by
    intro k hk
    rw [hU] at hk ⊢
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hk
    rw [← hm]
    have h1 : r⁻¹ * (s * t) ^ m * r = ((s * t) ^ 2) ^ m := by
      rw [show r⁻¹ * (s * t) ^ m * r = (MulAut.conj r⁻¹) ((s * t) ^ m) from by
        rw [MulAut.conj_apply, inv_inv]]
      rw [map_zpow, MulAut.conj_apply, inv_inv, hrus]
    refine Subgroup.mem_zpowers_iff.mpr ⟨2 * m, ?_⟩
    show (s * t) ^ (2 * m) = r⁻¹ * (s * t) ^ m * r
    rw [h1, show ((s * t) ^ 2 : G) ^ m = (s * t) ^ (2 * m) from by
      rw [show ((s * t) ^ 2 : G) = (s * t) ^ (2 : ℤ) from by rw [zpow_ofNat]]
      rw [zpow_mul]]
  have hr_conj : ∀ k ∈ U, r * k * r⁻¹ ∈ U := by
    have hgen : r * (s * t) * r⁻¹ ∈ U := by
      have hsq : (r * (s * t) * r⁻¹) ^ 2 = s * t := by
        have h1 : (r * (s * t) * r⁻¹) ^ 2 = r * (s * t) ^ 2 * r⁻¹ := by
          simp only [pow_two]; group
        rw [h1, show (s * t) ^ 2 = r⁻¹ * (s * t) * r from hrus.symm]
        group
      have hle : U ≤ Subgroup.zpowers (r * (s * t) * r⁻¹) := by
        rw [hU, Subgroup.zpowers_le]
        exact Subgroup.mem_zpowers_iff.mpr ⟨(2 : ℤ), by rw [zpow_ofNat]; exact hsq⟩
      have hcard : Nat.card ↥(Subgroup.zpowers (r * (s * t) * r⁻¹)) ≤ Nat.card ↥U := by
        rw [Nat.card_zpowers, hU, Nat.card_zpowers]
        have heq : orderOf (r * (s * t) * r⁻¹) = orderOf (s * t) := by
          have hh : r * (s * t) * r⁻¹ = (MulAut.conj r) (s * t) := by rw [MulAut.conj_apply]
          rw [hh]
          exact orderOf_injective (MulAut.conj r).toMonoidHom (MulAut.conj r).injective (s * t)
        rw [heq]
      rw [Subgroup.eq_of_le_of_card_ge hle hcard]
      exact Subgroup.mem_zpowers _
    intro k hk
    rw [hU] at hk ⊢
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hk
    obtain ⟨mm, hmm⟩ := Subgroup.mem_zpowers_iff.mp hgen
    rw [← hm]
    have h1 : r * (s * t) ^ m * r⁻¹ = ((s * t) ^ mm) ^ m := by
      rw [show r * (s * t) ^ m * r⁻¹ = (MulAut.conj r) ((s * t) ^ m) from by
        rw [MulAut.conj_apply]]
      rw [map_zpow, MulAut.conj_apply, hmm]
    refine Subgroup.mem_zpowers_iff.mpr ⟨mm * m, ?_⟩
    show (s * t) ^ (mm * m) = r * (s * t) ^ m * r⁻¹
    rw [h1, zpow_mul]
  have hsN : s ∈ Subgroup.normalizer (U : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hs_conj y hy, fun hy => ?_⟩
    have h := hs_conj (s * y * s⁻¹) hy
    rwa [show s * (s * y * s⁻¹) * s⁻¹ = y from by
      rw [hs_inv]
      calc s * (s * y * s) * s = (s * s) * y * (s * s) := by group
        _ = 1 * y * 1 := by rw [hss]
        _ = y := by group] at h
  have hrN : r ∈ Subgroup.normalizer (U : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hr_conj y hy, fun hy => ?_⟩
    have h := hr_conj_inv (r * y * r⁻¹) hy
    rwa [show r⁻¹ * (r * y * r⁻¹) * r = y from by group] at h
  have hBle : B ≤ Subgroup.normalizer (U : Set G) := by
    rw [hB, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hrN
    · exact hsN
  let ρ : ↥B →* MulAut ↥U :=
    (Subgroup.normalizerMonoidHom U).comp (Subgroup.inclusion hBle)
  have hρ : ∀ (b : ↥B) (v : ↥U), ((ρ b v : ↥U) : G) = (b : G) * (v : G) * (b : G)⁻¹ := by
    intro b v
    show (((Subgroup.normalizerMonoidHom U) (Subgroup.inclusion hBle b)) v : G) = _
    rw [normalizerMonoidHom_apply_coe, Subgroup.coe_inclusion]
  have hBQ : B ≤ Q := by
    rw [hB, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hrQ
    · exact hsQ
  have hfpf : ∀ b : ↥B, b ≠ 1 → ∀ v : ↥U, ρ b v = v → v = 1 := by
    intro b hb v hv
    have hconj : (b : G) * (v : G) * (b : G)⁻¹ = (v : G) := by rw [← hρ b v, hv]
    have h3 : (b : G)⁻¹ * (v : G) * (b : G) = (v : G) := by
      have hg : (b : G)⁻¹ * ((b : G) * (v : G) * (b : G)⁻¹) * (b : G) = (v : G) := by group
      rwa [hconj] at hg
    have hbv : (v : G) * (b : G) = (b : G) * (v : G) := by
      calc (v : G) * (b : G) = (b : G) * ((b : G)⁻¹ * (v : G) * (b : G)) := by group
        _ = (b : G) * (v : G) := by rw [h3]
    have hb_ne : (b : G) ≠ 1 := fun h1 => hb (Subtype.ext h1)
    have hvH : (v : G) ∈ H :=
      Work.ZassenhausPSL2.Feit.mem_H_of_commute (x := (b : G)) h (hBQ b.2) hb_ne hbv
    have hvst : (v : G) * (s * t) = (s * t) * (v : G) := by
      have hvm : (v : G) ∈ Subgroup.zpowers (s * t) := by rw [← hU]; exact v.2
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hvm
      rw [← hk]
      have hcomm : (s * t) ^ k * (s * t) = (s * t) * (s * t) ^ k := by
        rw [show (s * t) ^ k * (s * t) = (s * t) ^ (k + 1) from by rw [zpow_add_one],
            show (s * t) * (s * t) ^ k = (s * t) ^ (1 + k) from by rw [zpow_add, zpow_one],
            show k + 1 = (1 : ℤ) + k from by ring]
      exact hcomm
    exact Subtype.ext (mem_H_centralizer_st h hZ h2 hsQ hs2 hvH hvst)
  have hrC : r ∈ Subgroup.centralizer (B : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y ∈ Subgroup.closure ({r, s} : Set G) := by rwa [← hB]
    exact Subgroup.closure_induction (p := fun z _ => z * r = r * z)
      (fun w hw => by
        rcases hw with hw | hw
        · rw [hw]
        · rw [hw, hsc r hrQ])
      (by rw [one_mul, mul_one])
      (fun u w _ _ ihu ihw => by
        calc (u * w) * r = u * (w * r) := by group
          _ = u * (r * w) := by rw [ihw]
          _ = (u * r) * w := by group
          _ = (r * u) * w := by rw [ihu]
          _ = r * (u * w) := by group)
      (fun u _ ihu => by
        calc u⁻¹ * r = u⁻¹ * (r * u) * u⁻¹ := by group
          _ = u⁻¹ * (u * r) * u⁻¹ := by rw [ihu]
          _ = r * u⁻¹ := by group)
      hy'
  have hsC : s ∈ Subgroup.centralizer (B : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y ∈ Subgroup.closure ({r, s} : Set G) := by rwa [← hB]
    exact Subgroup.closure_induction (p := fun z _ => z * s = s * z)
      (fun w hw => by
        rcases hw with hw | hw
        · rw [hw, hsc r hrQ]
        · rw [hw])
      (by rw [one_mul, mul_one])
      (fun u w _ _ ihu ihw => by
        calc (u * w) * s = u * (w * s) := by group
          _ = u * (s * w) := by rw [ihw]
          _ = (u * s) * w := by group
          _ = (s * u) * w := by rw [ihu]
          _ = s * (u * w) := by group)
      (fun u _ ihu => by
        calc u⁻¹ * s = u⁻¹ * (s * u) * u⁻¹ := by group
          _ = u⁻¹ * (u * s) * u⁻¹ := by rw [ihu]
          _ = s * u⁻¹ := by group)
      hy'
  have hBC : B ≤ Subgroup.centralizer (B : Set G) := by
    rw [hB, Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | rfl
    · exact hrC
    · exact hsC
  have hBc_comm : ∀ x y : ↥B, x * y = y * x := by
    intro x y
    apply Subtype.ext
    have hx := hBC x.2
    rw [Subgroup.mem_centralizer_iff] at hx
    exact (hx (y : G) y.2).symm
  haveI : IsMulCommutative ↥B := isMulCommutative_iff.mpr hBc_comm
  haveI : Nontrivial ↥U := (Subgroup.nontrivial_iff_ne_bot U).mpr (fun hbot => by
    have : s * t ∈ (⊥ : Subgroup G) := hbot ▸ (by rw [hU]; exact Subgroup.mem_zpowers _)
    exact hst_ne (Subgroup.mem_bot.mp this))
  have hcyc : IsCyclic ↥B := QSZ_abelian_fpf_isCyclic ρ hfpf
  have hs2' : (⟨s, hsB⟩ : ↥B) ^ 2 = 1 := by
    apply Subtype.ext
    simpa [Subgroup.coe_pow, pow_two] using hss
  have hs1' : (⟨s, hsB⟩ : ↥B) ≠ 1 := fun h1 => hs_ne (Subtype.ext_iff.mp h1)
  have hr' : orderOf (⟨r, hrB⟩ : ↥B) = 2 ^ a := by
    rw [← Subgroup.orderOf_coe (⟨r, hrB⟩ : ↥B)]; exact ha
  have heq := cyclic_pow_involution hs2' hs1' hr' ha1
  have hseq : s = r ^ 2 ^ (a - 1) := by
    have := congrArg (Subtype.val) heq
    simpa only [Subgroup.coe_pow, Subgroup.coe_mk] using this
  exact hseq

theorem QSZ_t_rPow_t_mem {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (H Q : Subgroup G) (t : G) (h : Submission.Blueprint.IsSplitRankOne H Q t)
    (hZ : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {s r : G} (hsQ : s ∈ Q) (hs2 : orderOf s = 2) (hrQ : r ∈ Q)
    (hsr : t * s * t⁻¹ = r⁻¹ * t * r)
    (a : ℕ) (ha : orderOf r = 2 ^ a) (ha1 : 1 ≤ a) :
    ∃ q1 ∈ Q, ∃ q2 ∈ Q, t * r ^ 2 ^ (a - 1) * t = q1 * t * q2 := by
  have htinv : t⁻¹ = t := by
    have ht2 : t * t = 1 := by
      have hh := pow_orderOf_eq_one t
      rw [h.invol] at hh
      simpa [pow_two] using hh
    exact inv_eq_of_mul_eq_one_right ht2
  have hsr' : t * s * t = r⁻¹ * t * r := by simpa [htinv] using hsr
  have hseq : s = r ^ 2 ^ (a - 1) := QSZ_aux hs H Q t h hZ h2 hsQ hs2 hrQ hsr a ha ha1
  exact ⟨r⁻¹, Q.inv_mem hrQ, r, hrQ, by rw [← hseq, hsr']⟩

end Work.ZassenhausSuzuki
