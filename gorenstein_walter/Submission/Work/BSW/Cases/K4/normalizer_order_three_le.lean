import Mathlib
import Submission.Work.BSW.Cases.K4.K4Hyp
import Submission.Work.BSW.Cases.K4.fourGroupNormalizer
import Submission.Work.BSW.Cases.K4.Setup
import Submission.Work.BSW.Cases.K4.benderCase2Aux
import Submission.Work.BSW.Cases.K4.card_conj_mul_card_normalizer
import Submission.Work.BSW.Cases.K4.card_normalizer_le_two_mul_card_centralizer

namespace Work.BSW.Cases.K4

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

/-! ## Auxiliary lemmas (helpers for `normalizer_order_three_le`) -/

lemma aux_conj_coe (K : Subgroup G) (n x : ↥K) :
    (((MulAut.conj n) x : ↥K) : G) = (n : G) * (x : G) * (n : G)⁻¹ := by
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]

lemma aux_map_conj_subgroupOf (K A : Subgroup G) (hA : A ≤ K) (n : ↥K) :
    (A.subgroupOf K).map (MulAut.conj n).toMonoidHom
      = (A.map (MulAut.conj (n : G)).toMonoidHom).subgroupOf K := by
  ext z
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxz⟩
    refine ⟨(x : G), Subgroup.mem_subgroupOf.mp hx, ?_⟩
    have key : (z : G) = (n : G) * (x : G) * (n : G)⁻¹ := by
      have h : (((MulAut.conj n) x : ↥K) : G) = (z : G) := congrArg (fun w : ↥K => (w : G)) hxz
      rw [← h]
      exact aux_conj_coe K n x
    change (MulAut.conj (n : G)) (x : G) = (z : G)
    rw [MulAut.conj_apply, key]
  · rintro ⟨x, hx, hxz⟩
    refine ⟨⟨x, hA hx⟩, Subgroup.mem_subgroupOf.mpr hx, ?_⟩
    apply Subtype.ext
    change (MulAut.conj (n : G)) (x : G) = (z : G)
    rw [MulAut.conj_apply]
    exact hxz

theorem aux_exists_conj (h : K4Hyp G) {V X Y : Subgroup G} (hV : IsV4 V)
    (hXle : X ≤ Subgroup.normalizer (V : Set G)) (hX3 : Nat.card ↥X = 3)
    (hYle : Y ≤ Subgroup.normalizer (V : Set G)) (hY3 : Nat.card ↥Y = 3) :
    ∃ n ∈ Subgroup.normalizer (V : Set G), Y = X.map (MulAut.conj n).toMonoidHom := by
  set NV : Subgroup G := Subgroup.normalizer (V : Set G) with hNV
  have hNVcard : Nat.card ↥NV = 24 := card_normalizer_eq h hV
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hX3' : Nat.card ↥(X.subgroupOf NV) = 3 := by
    rw [← hX3]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXle).toEquiv
  have hY3' : Nat.card ↥(Y.subgroupOf NV) = 3 := by
    rw [← hY3]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYle).toEquiv
  have hfac : (Nat.card ↥NV).factorization 3 = 1 := by rw [hNVcard]; norm_num [Nat.factorization]
  have hXP : Nat.card ↥(X.subgroupOf NV) = 3 ^ (Nat.card ↥NV).factorization 3 := by
    rw [hfac, pow_one]; exact hX3'
  have hYP : Nat.card ↥(Y.subgroupOf NV) = 3 ^ (Nat.card ↥NV).factorization 3 := by
    rw [hfac, pow_one]; exact hY3'
  let P : Sylow 3 ↥NV := Sylow.ofCard (X.subgroupOf NV) hXP
  let Q : Sylow 3 ↥NV := Sylow.ofCard (Y.subgroupOf NV) hYP
  have hP : (P : Subgroup ↥NV) = X.subgroupOf NV := Sylow.coe_ofCard _ _
  have hQ : (Q : Subgroup ↥NV) = Y.subgroupOf NV := Sylow.coe_ofCard _ _
  obtain ⟨n, hn⟩ := MulAction.IsPretransitive.exists_smul_eq (M := ↥NV) P Q
  refine ⟨(n : G), n.2, ?_⟩
  have hstep : (X.subgroupOf NV).map (MulAut.conj n).toMonoidHom = Y.subgroupOf NV := by
    have h1 := congrArg (fun P : Sylow 3 ↥NV => (P : Subgroup ↥NV)) hn
    rw [Sylow.coe_subgroup_smul] at h1
    rw [Subgroup.pointwise_smul_def] at h1
    rw [hP, hQ] at h1
    exact h1
  have hYeq : (X.map (MulAut.conj (n : G)).toMonoidHom).subgroupOf NV = Y.subgroupOf NV := by
    rw [← aux_map_conj_subgroupOf NV X hXle n]
    exact hstep
  have hXmap_le_NV : X.map (MulAut.conj (n : G)).toMonoidHom ≤ NV := by
    rintro z ⟨x, hx, rfl⟩
    change (MulAut.conj (n : G)) x ∈ NV
    rw [MulAut.conj_apply]
    exact NV.mul_mem (NV.mul_mem n.2 (hXle hx)) (NV.inv_mem n.2)
  have hXeq : X.map (MulAut.conj (n : G)).toMonoidHom = Y := by
    have hh := Subgroup.subgroupOf_inj.mp hYeq
    rwa [inf_eq_left.mpr hXmap_le_NV, inf_eq_left.mpr hYle] at hh
  exact hXeq.symm

lemma aux_normalizer_subgroupOf_eq {K Y : Subgroup G} (hY : Y ≤ K) :
    Subgroup.normalizer ((Y.subgroupOf K) : Set ↥K)
      = (Subgroup.normalizer (Y : Set G)).subgroupOf K := by
  ext g
  constructor
  · intro hg
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hhK : h ∈ K := hY hh
      have hmem : (⟨h, hhK⟩ : ↥K) ∈ Y.subgroupOf K := Subgroup.mem_subgroupOf.mpr hh
      have h2 : g * ⟨h, hhK⟩ * g⁻¹ ∈ Y.subgroupOf K :=
        (Subgroup.mem_normalizer_iff.mp hg ⟨h, hhK⟩).mp hmem
      have h3 : ((g * ⟨h, hhK⟩ * g⁻¹ : ↥K) : G) = (g : G) * h * (g : G)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← h3]
      exact Subgroup.mem_subgroupOf.mp h2
    · intro hh
      have hginv : (g⁻¹ : ↥K) ∈ Subgroup.normalizer ((Y.subgroupOf K) : Set ↥K) :=
        Subgroup.inv_mem _ hg
      have hzK : (g : G) * h * (g : G)⁻¹ ∈ K := hY hh
      have hzmem : (⟨(g : G) * h * (g : G)⁻¹, hzK⟩ : ↥K) ∈ Y.subgroupOf K :=
        Subgroup.mem_subgroupOf.mpr hh
      have h2 := (Subgroup.mem_normalizer_iff.mp hginv
        ⟨(g : G) * h * (g : G)⁻¹, hzK⟩).mp hzmem
      have h3 : (((g⁻¹ * ⟨(g : G) * h * (g : G)⁻¹, hzK⟩ * (g⁻¹)⁻¹ : ↥K)) : G) = h := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
        group
      have h4 : (((g⁻¹ * ⟨(g : G) * h * (g : G)⁻¹, hzK⟩ * (g⁻¹)⁻¹ : ↥K)) : G) ∈ Y :=
        Subgroup.mem_subgroupOf.mp h2
      rwa [h3] at h4
  · intro hg
    rw [Subgroup.mem_subgroupOf] at hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have h2 := Subgroup.mem_normalizer_iff.mp hg (h : G)
    have h3 : ((g * h * g⁻¹ : ↥K) : G) = (g : G) * (h : G) * (g : G)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · intro hh
      rw [h3]
      exact h2.mp hh
    · intro hh
      rw [h3] at hh
      exact h2.mpr hh

/-- In a finite group `H` of order `24`, the normalizer of a non-normal subgroup `X` of order `3`
has order `6`. -/
theorem aux_card_normalizer_eq_six {H : Type} [Group H] [Finite H]
    (X : Subgroup H) (hH : Nat.card H = 24) (hX : Nat.card ↥X = 3) (hnot : ¬ X.Normal) :
    Nat.card ↥(Subgroup.normalizer (X : Set H)) = 6 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Finite (Sylow 3 H) := inferInstance
  have hfac : (Nat.card H).factorization 3 = 1 := by rw [hH]; norm_num [Nat.factorization]
  have hXcard : Nat.card ↥X = 3 ^ (Nat.card H).factorization 3 := by rw [hfac, pow_one, hX]
  let P : Sylow 3 H := Sylow.ofCard X hXcard
  have hP : (P : Subgroup H) = X := Sylow.coe_ofCard X hXcard
  have hmod : Nat.card (Sylow 3 H) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 H
  let N : Subgroup H := Subgroup.normalizer (X : Set H)
  change Nat.card ↥N = 6
  have hidx : Nat.card (Sylow 3 H) = N.index := by
    change Nat.card (Sylow 3 H) = (Subgroup.normalizer (X : Set H)).index
    rw [← hP]; exact Sylow.card_eq_index_normalizer P
  have hmul : Nat.card ↥N * N.index = 24 := by
    have := Subgroup.card_mul_index N; rw [hH] at this; exact this
  have hndvd : N.index ∣ 24 := ⟨Nat.card ↥N, by rw [← hmul, mul_comm]⟩
  have hmodn : N.index ≡ 1 [MOD 3] := by rw [← hidx]; exact hmod
  have hnpos : 0 < N.index := Nat.pos_of_dvd_of_pos hndvd (by norm_num)
  have hnle : N.index ≤ 24 := Nat.le_of_dvd (by norm_num) hndvd
  have hne1 : N.index ≠ 1 := by
    intro h1
    have htop : N = ⊤ := Subgroup.index_eq_one.mp h1
    exact hnot (Subgroup.normalizer_eq_top_iff.mp htop)
  have hn14 : N.index = 1 ∨ N.index = 4 := by
    interval_cases N.index <;> simp_all [Nat.ModEq]
  rcases hn14 with h1 | h1
  · exact absurd h1 hne1
  · have : Nat.card ↥N = 6 := by rw [h1] at hmul; omega
    exact this

theorem aux_card_normalizer_inf (h : K4Hyp G) {V Y : Subgroup G} (hV : IsV4 V)
    (hYle : Y ≤ Subgroup.normalizer (V : Set G)) (hY3 : Nat.card ↥Y = 3) :
    Nat.card ↥(Subgroup.normalizer (Y : Set G) ⊓ Subgroup.normalizer (V : Set G)) = 6 := by
  set NV : Subgroup G := Subgroup.normalizer (V : Set G) with hNV
  have hNVcard : Nat.card ↥NV = 24 := card_normalizer_eq h hV
  have hY3' : Nat.card ↥(Y.subgroupOf NV) = 3 := by
    rw [← hY3]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYle).toEquiv
  have hnotnormal : ¬ (Y.subgroupOf NV).Normal := by
    intro hnorm
    have hVnorm : (V.subgroupOf NV).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (le_rfl : NV ≤ Subgroup.normalizer (V : Set G))
    have hYVbot : Y ⊓ V = ⊥ := by
      have hcard : Nat.card ↥(Y ⊓ V) = 1 := by
        have h1 : Nat.card ↥(Y ⊓ V) ∣ 3 := by
          have := Subgroup.card_dvd_of_le (inf_le_left : Y ⊓ V ≤ Y); rwa [hY3] at this
        have h2 : Nat.card ↥(Y ⊓ V) ∣ 4 := by
          have := Subgroup.card_dvd_of_le (inf_le_right : Y ⊓ V ≤ V); rwa [hV.1] at this
        have h3 := Nat.dvd_gcd h1 h2
        have hg : Nat.gcd 3 4 = 1 := by norm_num
        rw [hg] at h3
        exact Nat.le_antisymm (Nat.le_of_dvd (by norm_num) h3) Nat.card_pos
      exact Subgroup.card_eq_one.mp hcard
    have hinfbot : Y.subgroupOf NV ⊓ V.subgroupOf NV = ⊥ := by
      rw [show Y.subgroupOf NV ⊓ V.subgroupOf NV = (Y ⊓ V).subgroupOf NV from by
        ext x
        rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
          Subgroup.mem_subgroupOf, Subgroup.mem_inf], hYVbot]
      simp
    obtain ⟨y, hyY', hy1⟩ : ∃ y : ↥NV, y ∈ Y.subgroupOf NV ∧ y ≠ 1 := by
      haveI : Nontrivial ↥(Y.subgroupOf NV) := by
        haveI := Fintype.ofFinite ↥(Y.subgroupOf NV)
        rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card, hY3']
        norm_num
      obtain ⟨y, hy⟩ := exists_ne (1 : ↥(Y.subgroupOf NV))
      exact ⟨y.1, y.2, fun hc => hy (Subtype.ext hc)⟩
    obtain ⟨u, huV', hu1⟩ : ∃ u : ↥NV, u ∈ V.subgroupOf NV ∧ u ≠ 1 := by
      haveI : Nontrivial ↥(V.subgroupOf NV) := by
        haveI := Fintype.ofFinite ↥(V.subgroupOf NV)
        rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer : V ≤ NV)).toEquiv,
          hV.1]
        norm_num
      obtain ⟨u, hu⟩ := exists_ne (1 : ↥(V.subgroupOf NV))
      exact ⟨u.1, u.2, fun hc => hu (Subtype.ext hc)⟩
    have hyY : (y : G) ∈ Y := Subgroup.mem_subgroupOf.mp hyY'
    have huV : (u : G) ∈ V := Subgroup.mem_subgroupOf.mp huV'
    have hyord : orderOf (y : G) = 3 := by
      have hd : orderOf (y : G) ∣ 3 := by
        have := orderOf_dvd_natCard_of_mem hyY; rwa [hY3] at this
      rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hd with h1 | h3
      · exfalso; exact hy1 (Subtype.ext (orderOf_eq_one_iff.mp h1))
      · exact h3
    have huord : orderOf (u : G) = 2 :=
      hV.orderOf_eq_two huV (fun hc => hu1 (Subtype.ext hc))
    -- show y and u commute in ↥NV
    have huNY : u ∈ Subgroup.normalizer ((Y.subgroupOf NV) : Set ↥NV) := by
      rw [(Subgroup.normalizer_eq_top_iff).mpr hnorm]; exact Subgroup.mem_top u
    have hyNV : y ∈ Subgroup.normalizer ((V.subgroupOf NV) : Set ↥NV) := by
      rw [(Subgroup.normalizer_eq_top_iff).mpr hVnorm]; exact Subgroup.mem_top y
    have hcY : y * u * y⁻¹ * u⁻¹ ∈ Y.subgroupOf NV := by
      have h1 : u * y⁻¹ * u⁻¹ ∈ Y.subgroupOf NV :=
        (Subgroup.mem_normalizer_iff.mp huNY y⁻¹).mp ((Y.subgroupOf NV).inv_mem hyY')
      have h2 : y * (u * y⁻¹ * u⁻¹) ∈ Y.subgroupOf NV := (Y.subgroupOf NV).mul_mem hyY' h1
      rwa [show y * (u * y⁻¹ * u⁻¹) = y * u * y⁻¹ * u⁻¹ from by group] at h2
    have hcV : y * u * y⁻¹ * u⁻¹ ∈ V.subgroupOf NV := by
      have h1 : y * u * y⁻¹ ∈ V.subgroupOf NV :=
        (Subgroup.mem_normalizer_iff.mp hyNV u).mp huV'
      have h2 : (y * u * y⁻¹) * u⁻¹ ∈ V.subgroupOf NV :=
        (V.subgroupOf NV).mul_mem h1 ((V.subgroupOf NV).inv_mem huV')
      rwa [show (y * u * y⁻¹) * u⁻¹ = y * u * y⁻¹ * u⁻¹ from rfl] at h2
    have hc : y * u * y⁻¹ * u⁻¹ = 1 := by
      have hmem : y * u * y⁻¹ * u⁻¹ ∈ Y.subgroupOf NV ⊓ V.subgroupOf NV := ⟨hcY, hcV⟩
      rw [hinfbot, Subgroup.mem_bot] at hmem
      exact hmem
    have h3 : y * u = u * y := by
      have h4 : y * u * y⁻¹ = u := by
        calc y * u * y⁻¹ = (y * u * y⁻¹ * u⁻¹) * u := by group
          _ = 1 * u := by rw [hc]
          _ = u := one_mul u
      calc y * u = (y * u * y⁻¹) * y := by group
        _ = u * y := by rw [h4]
    exact not_commute_of_orderOf_eq_three h huord hyord (congrArg Subtype.val h3).symm
  have hN6 : Nat.card ↥(Subgroup.normalizer ((Y.subgroupOf NV) : Set ↥NV)) = 6 :=
    aux_card_normalizer_eq_six (Y.subgroupOf NV) hNVcard hY3' hnotnormal
  rw [aux_normalizer_subgroupOf_eq hYle] at hN6
  have hcard_conv : Nat.card ↥((Subgroup.normalizer (Y : Set G)).subgroupOf NV)
      = Nat.card ↥(Subgroup.normalizer (Y : Set G) ⊓ NV) := by
    have heq : (Subgroup.normalizer (Y : Set G)).subgroupOf NV
        = (Subgroup.normalizer (Y : Set G) ⊓ NV).subgroupOf NV := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => ⟨h, x.2⟩, fun h => h.1⟩
    rw [heq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : Subgroup.normalizer (Y : Set G) ⊓ NV ≤ NV)).toEquiv
  rw [hcard_conv] at hN6
  simpa [hNV] using hN6

/-- `C_G(X) = X` for an order-`3` subgroup `X ≤ N_G(V)` with `C_G(X) ≤ N_G(V)`. -/
theorem aux_centralizer_order_three_eq_self (h : K4Hyp G) {V X : Subgroup G} (hV : IsV4 V)
    (hXle : X ≤ Subgroup.normalizer (V : Set G)) (hX3 : Nat.card ↥X = 3)
    (hCX : Subgroup.centralizer (X : Set G) ≤ Subgroup.normalizer (V : Set G)) :
    Subgroup.centralizer (X : Set G) = X := by
  classical
  have hXab : X ≤ Subgroup.centralizer (X : Set G) := by
    haveI : IsCyclic ↥X := isCyclic_of_card_dvd_prime (p := 3) (by rw [hX3])
    exact Subgroup.le_centralizer X
  set n : ℕ := Nat.card ↥(Subgroup.centralizer (X : Set G)) with hn
  have hn24 : n ∣ 24 := by
    rw [hn, ← card_normalizer_eq h hV]
    exact Subgroup.card_dvd_of_le hCX
  have hn3 : 3 ∣ n := by
    rw [hn]
    have h' := Subgroup.card_dvd_of_le hXab
    rwa [hX3] at h'
  have h2n : ¬ 2 ∣ n := by
    intro h2
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(Subgroup.centralizer (X : Set G))) 2 (by rwa [← hn])
    have hz2 : (z : G) ∈ Subgroup.centralizer (X : Set G) := z.2
    have hzG : orderOf (z : G) = 2 := by
      rw [Subgroup.orderOf_coe]; exact hz
    have hle : X ≤ cent G (z : G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hz2 x hx
    have hdvd : 3 ∣ Nat.card ↥(cent G (z : G)) := by
      have h' := Subgroup.card_dvd_of_le hle
      rwa [hX3] at h'
    rw [h.2.1 (z : G) hzG] at hdvd
    obtain ⟨k, hk⟩ := hdvd
    omega
  have hn_eq : n = 3 := by
    obtain ⟨a, ha⟩ := hn24
    obtain ⟨b, hb⟩ := hn3
    have hba : b * a = 8 := by
      have : 3 * (b * a) = 24 := by rw [ha, hb]; ring
      omega
    have hb1 : b = 1 := by
      have hbdvd : b ∣ 8 := ⟨a, hba.symm⟩
      obtain ⟨i, hi, hbi⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 3)).mp (by simpa using hbdvd)
      interval_cases i
      · simpa using hbi
      · exfalso; apply h2n; rw [hb, hbi]; norm_num
      · exfalso; apply h2n; rw [hb, hbi]; norm_num
      · exfalso; apply h2n; rw [hb, hbi]; norm_num
    rw [hb, hb1, mul_one]
  have hnc : Nat.card ↥(Subgroup.centralizer (X : Set G)) = 3 := by rw [← hn]; exact hn_eq
  exact (Subgroup.eq_of_le_of_card_ge hXab (by rw [hX3, hnc])).symm

/-- `C_G(Y) = Y` for any order-`3` subgroup `Y ≤ N_G(V)`, given an order-`3` subgroup
`X ≤ N_G(V)` with `C_G(X) ≤ N_G(V)` (all order-`3` subgroups of `N_G(V)` are conjugate there). -/
theorem aux_centralizer_eq_self (h : K4Hyp G) {V X Y : Subgroup G} (hV : IsV4 V)
    (hXle : X ≤ Subgroup.normalizer (V : Set G)) (hX3 : Nat.card ↥X = 3)
    (hCX : Subgroup.centralizer (X : Set G) ≤ Subgroup.normalizer (V : Set G))
    (hYle : Y ≤ Subgroup.normalizer (V : Set G)) (hY3 : Nat.card ↥Y = 3) :
    Subgroup.centralizer (Y : Set G) = Y := by
  have hCXeq : Subgroup.centralizer (X : Set G) = X :=
    aux_centralizer_order_three_eq_self h hV hXle hX3 hCX
  obtain ⟨n, _hnNV, hconj⟩ := aux_exists_conj h hV hXle hX3 hYle hY3
  apply le_antisymm
  · intro z hz
    rw [hconj, Subgroup.mem_map]
    refine ⟨n⁻¹ * z * n, ?_, ?_⟩
    · rw [← hCXeq, Subgroup.mem_centralizer_iff]
      intro x hx
      have hnx : n * x * n⁻¹ ∈ Y := by
        rw [hconj, Subgroup.mem_map]
        exact ⟨x, hx, by change (MulAut.conj n) x = n * x * n⁻¹; rw [MulAut.conj_apply]⟩
      have hzx := Subgroup.mem_centralizer_iff.mp hz (n * x * n⁻¹) hnx
      calc x * (n⁻¹ * z * n) = n⁻¹ * ((n * x * n⁻¹) * z) * n := by group
        _ = n⁻¹ * (z * (n * x * n⁻¹)) * n := by rw [hzx]
        _ = (n⁻¹ * z * n) * x := by group
    · change (MulAut.conj n) (n⁻¹ * z * n) = z
      rw [MulAut.conj_apply]; group
  · haveI : IsCyclic ↥Y := isCyclic_of_card_dvd_prime (p := 3) (by rw [hY3])
    exact Subgroup.le_centralizer Y

/-- **The Bender §3, Case 2 key point**: for every subgroup `Y ≤ N_G(V)` of order `3`, the
normalizer `N_G(Y)` is contained in `N_G(V)`. -/
theorem normalizer_order_three_le {G : Type} [Group G] [Finite G]
    (h : Work.BSW.Cases.K4.K4Hyp G) {V X : Subgroup G} (hV : Work.BSW.Cases.K4.IsV4 V)
    (hXle : X ≤ Subgroup.normalizer (V : Set G)) (hX3 : Nat.card ↥X = 3)
    (hCX : Subgroup.centralizer (X : Set G) ≤ Subgroup.normalizer (V : Set G)) {Y : Subgroup G}
    (hYle : Y ≤ Subgroup.normalizer (V : Set G)) (hY3 : Nat.card ↥Y = 3) :
    Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  have hCY : Subgroup.centralizer (Y : Set G) = Y :=
    aux_centralizer_eq_self h hV hXle hX3 hCX hYle hY3
  have h3 := aux_card_normalizer_inf h hV hYle hY3
  have hle6 : Nat.card ↥(Subgroup.normalizer (Y : Set G)) ≤ 6 := by
    have h1 := card_normalizer_le_two_mul_card_centralizer Y hY3
    rw [hCY, hY3] at h1
    omega
  have hge6 : 6 ≤ Nat.card ↥(Subgroup.normalizer (Y : Set G)) := by
    have h4 := Nat.card_le_card_of_injective
      (Subgroup.inclusion (inf_le_left :
        Subgroup.normalizer (Y : Set G) ⊓ Subgroup.normalizer (V : Set G) ≤
          Subgroup.normalizer (Y : Set G)))
      (Subgroup.inclusion_injective _)
    omega
  have hcard : Nat.card ↥(Subgroup.normalizer (Y : Set G))
      = Nat.card ↥(Subgroup.normalizer (Y : Set G) ⊓ Subgroup.normalizer (V : Set G)) := by
    omega
  have heq : Subgroup.normalizer (Y : Set G)
      = Subgroup.normalizer (Y : Set G) ⊓ Subgroup.normalizer (V : Set G) :=
    (Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard])).symm
  rw [heq]
  exact inf_le_right

end Work.BSW.Cases.K4
