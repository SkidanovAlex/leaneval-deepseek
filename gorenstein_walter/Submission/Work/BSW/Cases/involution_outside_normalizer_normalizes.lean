import Mathlib
import Submission.Work.BSW.Concl
import Submission.Work.BSW.Api.card_centralizer_of_card_K_two
import Submission.Work.BSW.Api.ncard_involutions_eq_index
import Submission.Work.BSW.Api.mem_centralizer_iff
import Submission.Work.BSW.Api.card_sup_zpowers

namespace Work.BSW.Cases

open Subgroup Work.GW2

variable {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}

/-- `K = ⟨t⟩` in the `|K| = 2` case. -/
theorem iwn_K_eq_zpowers_t (h : BSWHyps2 G t s K) (hk : Nat.card ↥K = 2) :
    K = Subgroup.zpowers t := by
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · exact Subgroup.zpowers_le.mpr (Work.BSW.t_mem_K h)
  · rw [Nat.card_zpowers, Work.BSW.orderOf_t h, hk]

/-- The four elements of `H = C_G(t)`. -/
theorem iwn_mem_centralizer_H_iff (h : BSWHyps2 G t s K) (hk : Nat.card ↥K = 2) (x : G) :
    x ∈ Subgroup.centralizer ({t} : Set G) ↔ x = 1 ∨ x = t ∨ x = s ∨ x = t * s := by
  have hK : K = Subgroup.zpowers t := iwn_K_eq_zpowers_t h hk
  rw [Work.BSW.Api.mem_centralizer_iff h x, hK]
  refine ⟨?_, ?_⟩
  · rintro (hx | ⟨k, hkK, hkx⟩)
    · rcases Work.BSW.mem_zpowers_t h hx with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
    · rcases Work.BSW.mem_zpowers_t h hkK with hk1 | hk1
      · right; right; left; rw [hkx, hk1, one_mul]
      · right; right; right; rw [hkx, hk1]
  · intro hx
    rcases hx with h1 | h2 | h3 | h4
    · rw [h1]; exact Or.inl (Subgroup.one_mem _)
    · rw [h2]; exact Or.inl (Subgroup.mem_zpowers t)
    · rw [h3]; exact Or.inr ⟨1, Subgroup.one_mem _, (one_mul s).symm⟩
    · rw [h4]; exact Or.inr ⟨t, Subgroup.mem_zpowers t, rfl⟩

/-- `C_G(t)` has exponent `2`. -/
theorem iwn_H_two (h : BSWHyps2 G t s K) (hk : Nat.card ↥K = 2) :
    ∀ x ∈ Subgroup.centralizer ({t} : Set G), x * x = 1 := by
  intro x hx
  rw [iwn_mem_centralizer_H_iff h hk] at hx
  rcases hx with h1 | h1 | h1 | h1
  · rw [h1, one_mul]
  · rw [h1, Work.BSW.t_mul_self h]
  · rw [h1, Work.BSW.s_mul_self h]
  · rw [h1, mul_assoc, ← mul_assoc s t s, Work.BSW.s_mul_t_eq_t_mul_s h, mul_assoc,
      ← mul_assoc t t (s * s), Work.BSW.t_mul_self h, one_mul, Work.BSW.s_mul_self h]

/-- `C_G(t)` is abelian. -/
theorem iwn_H_comm (h : BSWHyps2 G t s K) (hk : Nat.card ↥K = 2) :
    ∀ x ∈ Subgroup.centralizer ({t} : Set G), ∀ y ∈ Subgroup.centralizer ({t} : Set G),
      x * y = y * x := by
  have hst : s * t = t * s := Work.BSW.s_mul_t_eq_t_mul_s h
  intro x hx y hy
  rw [iwn_mem_centralizer_H_iff h hk] at hx hy
  rcases hx with h1 | h1 | h1 | h1 <;> rcases hy with h2 | h2 | h2 | h2
  all_goals rw [h1, h2]
  all_goals
    solve
    | rfl
    | simp only [one_mul, mul_one]
    | rw [hst]
    | rw [← mul_assoc t t s, Work.BSW.t_mul_self h, one_mul, mul_assoc t s t, hst,
        ← mul_assoc t t s, Work.BSW.t_mul_self h, one_mul]
    | rw [← mul_assoc s t s, hst]
    | rw [mul_assoc t s t, hst]
    | rw [mul_assoc t s s, Work.BSW.s_mul_self h, mul_one, ← mul_assoc s t s, hst,
        mul_assoc t s s, Work.BSW.s_mul_self h, mul_one]

/-- Conjugation carries centralizers to centralizers. -/
theorem iwn_map_conj_centralizer (c x : G) :
    (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj c).toMonoidHom =
      Subgroup.centralizer ({c * x * c⁻¹} : Set G) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨w, hw, rfl⟩
    calc (c * w * c⁻¹) * (c * x * c⁻¹) = c * (w * x) * c⁻¹ := by group
      _ = c * (x * w) * c⁻¹ := by rw [hw]
      _ = (c * x * c⁻¹) * (c * w * c⁻¹) := by group
  · intro hy
    refine ⟨c⁻¹ * y * c, ?_, ?_⟩
    · calc (c⁻¹ * y * c) * x = c⁻¹ * (y * (c * x * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * x * c⁻¹) * y) * c := by rw [hy]
        _ = x * (c⁻¹ * y * c) := by group
    · group

/-- The centralizer of an involution has order `4`. -/
theorem iwn_involution_centralizer_card (h : BSWHyps2 G t s K) (hk : Nat.card ↥K = 2)
    {x : G} (hx : orderOf x = 2) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set G)) = 4 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (Work.BSW.involutions_conj h x hx)
  have h1 : Nat.card ↥((Subgroup.centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom)
      = Nat.card ↥(Subgroup.centralizer ({x} : Set G)) :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  rw [← h1, iwn_map_conj_centralizer g x, hg, Work.BSW.Api.card_centralizer_of_card_K_two h hk]

/-- `C_G(z) = C_G(t)` for `z ∈ C_G(t)`, `z ≠ 1`. -/
theorem iwn_centralizer_eq_H_of_mem (h : BSWHyps2 G t s K) (hk : Nat.card ↥K = 2)
    {z : G} (hzH : z ∈ Subgroup.centralizer ({t} : Set G)) (hz1 : z ≠ 1) :
    Subgroup.centralizer ({t} : Set G) = Subgroup.centralizer ({z} : Set G) := by
  have hzz : z * z = 1 := iwn_H_two h hk z hzH
  have hz2 : orderOf z = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two]; exact hzz
    · exact hz1
  apply Subgroup.eq_of_le_of_card_ge
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (iwn_H_comm h hk z hzH x hx).symm
  · rw [iwn_involution_centralizer_card h hk hz2, Work.BSW.Api.card_centralizer_of_card_K_two h hk]

/-- Every `2`-subgroup of `G` has order at most `4`. -/
theorem iwn_two_subgroup_le_four (h : BSWHyps2 G t s K) (hk : Nat.card ↥K = 2)
    (P : Subgroup G) (hP : IsPGroup 2 P) : Nat.card ↥P ≤ 4 := by
  by_contra hlt
  rw [not_le] at hlt
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Nontrivial ↥P := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hcn : Nontrivial ↥(Subgroup.center ↥P) := hP.center_nontrivial
  have hcP : IsPGroup 2 ↥(Subgroup.center ↥P) := hP.to_subgroup (Subgroup.center ↥P)
  have hdvd : 2 ∣ Nat.card ↥(Subgroup.center ↥P) := by
    rcases IsPGroup.card_eq_or_dvd hcP with h1 | h1
    · exfalso
      haveI : Subsingleton ↥(Subgroup.center ↥P) := (Nat.card_eq_one_iff_unique.mp h1).1
      exact (not_subsingleton_iff_nontrivial.mpr hcn) inferInstance
    · exact h1
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hzG : orderOf (((z : ↥(Subgroup.center ↥P)) : ↥P) : G) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have hPle : P ≤ Subgroup.centralizer ({(((z : ↥(Subgroup.center ↥P)) : ↥P) : G)} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hzcent : (z : ↥P) ∈ Subgroup.center ↥P := z.2
    have hcomm : (⟨x, hx⟩ : ↥P) * (z : ↥P) = (z : ↥P) * ⟨x, hx⟩ :=
      Subgroup.mem_center_iff.mp hzcent ⟨x, hx⟩
    exact congrArg Subtype.val hcomm
  have hdiv : Nat.card ↥P ∣
      Nat.card ↥(Subgroup.centralizer ({(((z : ↥(Subgroup.center ↥P)) : ↥P) : G)} : Set G)) :=
    Subgroup.card_dvd_of_le hPle
  rw [iwn_involution_centralizer_card h hk hzG] at hdiv
  exact absurd (Nat.le_of_dvd (by norm_num) hdiv) (not_le.mpr hlt)

theorem iwn_t_ne_s (h : BSWHyps2 G t s K) : t ≠ s := fun hts =>
  Work.BSW.s_notMem_K h (by rw [← hts]; exact Work.BSW.t_mem_K h)

theorem iwn_s_ne_t (h : BSWHyps2 G t s K) : s ≠ t := (iwn_t_ne_s h).symm

theorem iwn_t_ne_ts (h : BSWHyps2 G t s K) : t ≠ t * s := by
  intro hts
  refine Work.BSW.s_ne_one h ?_
  have h2 := congrArg (fun z => t⁻¹ * z) hts
  simpa [mul_assoc] using h2.symm

theorem iwn_s_ne_ts (h : BSWHyps2 G t s K) : s ≠ t * s := by
  intro hts
  refine Work.BSW.t_ne_one h ?_
  have h2 := congrArg (fun z => z * s⁻¹) hts
  simpa [mul_assoc] using h2.symm

theorem iwn_ts_ne_t (h : BSWHyps2 G t s K) : t * s ≠ t := (iwn_t_ne_ts h).symm

theorem iwn_ts_ne_s (h : BSWHyps2 G t s K) : t * s ≠ s := (iwn_s_ne_ts h).symm

/-- The three involutions of `C_G(t)` are distinct. -/
theorem iwn_ncard_three (h : BSWHyps2 G t s K) : ({t, s, t * s} : Set G).ncard = 3 := by
  rw [Set.ncard_insert_of_notMem (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨iwn_t_ne_s h, iwn_t_ne_ts h⟩),
      Set.ncard_insert_of_notMem (by
        simp only [Set.mem_singleton_iff]; exact iwn_s_ne_ts h),
      Set.ncard_singleton]

/-- Burnside's fusion lemma in the abelian-Sylow situation. -/
theorem iwn_conj_mem_normalizer (h : BSWHyps2 G t s K) (hk : Nat.card ↥K = 2)
    {x y : G} (hxH : x ∈ Subgroup.centralizer ({t} : Set G)) (hx1 : x ≠ 1)
    (hyH : y ∈ Subgroup.centralizer ({t} : Set G)) (hy1 : y ≠ 1) (hconj : IsConj x y) :
    ∃ n ∈ Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G), n * x * n⁻¹ = y := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  refine ⟨c, ?_, hc⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change (Subgroup.centralizer ({t} : Set G)).map (MulAut.conj c).toMonoidHom
      = Subgroup.centralizer ({t} : Set G)
  have hxcen : Subgroup.centralizer ({x} : Set G) = Subgroup.centralizer ({t} : Set G) :=
    (iwn_centralizer_eq_H_of_mem h hk hxH hx1).symm
  have hycen : Subgroup.centralizer ({y} : Set G) = Subgroup.centralizer ({t} : Set G) :=
    (iwn_centralizer_eq_H_of_mem h hk hyH hy1).symm
  conv_lhs => rw [← hxcen]
  rw [iwn_map_conj_centralizer c x, hc, hycen]

theorem iwn_ts_ne_one (h : BSWHyps2 G t s K) : t * s ≠ 1 := by
  intro hc
  exact iwn_t_ne_s h (by
    have h2 := congrArg (fun z => z * s) hc
    simpa [mul_assoc, Work.BSW.s_mul_self h] using h2)

theorem iwn_orderOf_ts (h : BSWHyps2 G t s K) (hk : Nat.card ↥K = 2) :
    orderOf (t * s) = 2 := by
  apply orderOf_eq_prime
  · rw [pow_two]
    exact iwn_H_two h hk (t * s)
      (Subgroup.mul_mem _ (Work.BSW.t_mem_centralizer_t h) (Work.BSW.s_mem_centralizer_t h))
  · exact iwn_ts_ne_one h

/-- `N_G(C_G(t))` has order `12`. -/
theorem iwn_card_normalizer (h : BSWHyps2 G t s K) (hk : Nat.card ↥K = 2) :
    Nat.card ↥(Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G)) = 12 := by
  let H : Subgroup G := Subgroup.centralizer ({t} : Set G)
  let N : Subgroup G := Subgroup.normalizer (H : Set G)
  change Nat.card ↥N = 12
  have hHN : H ≤ N := Subgroup.le_normalizer
  have htH : t ∈ H := Work.BSW.t_mem_centralizer_t h
  have htN : t ∈ N := hHN htH
  have hsH : s ∈ H := Work.BSW.s_mem_centralizer_t h
  have htsH : t * s ∈ H := Subgroup.mul_mem _ htH hsH
  have hthree : ({t, s, t * s} : Set G).ncard = 3 := iwn_ncard_three h
  have hmemS : ∀ x ∈ ({t, s, t * s} : Set G), x ∈ H := by
    intro x hx
    have hh : x = t ∨ x = s ∨ x = t * s := by simpa using hx
    rcases hh with hh | hh | hh
    · rwa [hh]
    · rwa [hh]
    · rwa [hh]
  have hpre : (Subtype.val ⁻¹' ({t, s, t * s} : Set G) : Set ↥N).ncard = 3 := by
    rw [← Set.ncard_image_of_injective
      (Subtype.val ⁻¹' ({t, s, t * s} : Set G) : Set ↥N) (fun _ _ h => Subtype.ext h)]
    have himg : (Subtype.val '' (Subtype.val ⁻¹' ({t, s, t * s} : Set G) : Set ↥N))
        = ({t, s, t * s} : Set G) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx
        exact ⟨⟨x, hHN (hmemS x hx)⟩, hx, rfl⟩
    rw [himg, hthree]
  have hset : (conjugatesOf (⟨t, htN⟩ : ↥N)) = Subtype.val ⁻¹' ({t, s, t * s} : Set G) := by
    ext y
    constructor
    · intro hy
      obtain ⟨n, hn⟩ := isConj_iff.mp hy
      have hnN : (n : G) ∈ N := n.2
      have hval : (y : G) = (n : G) * t * (n : G)⁻¹ := by
        have hh := congrArg (Subtype.val) hn
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hh.symm
      rw [Set.mem_preimage]
      have hyH : (y : G) ∈ H := by
        rw [hval]
        exact (Subgroup.mem_normalizer_iff.mp hnN t).mp htH
      have hy1 : (y : G) ≠ 1 := by
        rw [hval]; intro hh
        refine Work.BSW.t_ne_one h ?_
        calc t = (n : G)⁻¹ * ((n : G) * t * (n : G)⁻¹) * (n : G) := by group
          _ = 1 := by rw [hh]; group
      have hmemv := (iwn_mem_centralizer_H_iff h hk (y : G)).mp hyH
      rcases hmemv with h1 | h1 | h1 | h1
      · exact absurd h1 hy1
      · show (y : G) ∈ ({t, s, t * s} : Set G); rw [h1]; simp
      · show (y : G) ∈ ({t, s, t * s} : Set G); rw [h1]; simp
      · show (y : G) ∈ ({t, s, t * s} : Set G); rw [h1]; simp
    · intro hy
      rw [Set.mem_preimage] at hy
      have hy' : (y : G) = t ∨ (y : G) = s ∨ (y : G) = t * s := by simpa using hy
      rcases hy' with h1 | h1 | h1
      · rw [show y = ⟨t, htN⟩ from Subtype.ext h1]
        exact IsConj.refl _
      · obtain ⟨n, hnN, hn⟩ := iwn_conj_mem_normalizer h hk hsH (Work.BSW.s_ne_one h)
            htH (Work.BSW.t_ne_one h) (Work.BSW.involutions_conj h s (Work.BSW.orderOf_s h))
        refine isConj_iff.mpr ⟨⟨n⁻¹, N.inv_mem hnN⟩, ?_⟩
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
        rw [h1]
        calc (n : G)⁻¹ * t * (n : G)
            = (n : G)⁻¹ * (n * s * (n : G)⁻¹) * (n : G) := by rw [hn]
          _ = s := by group
      · obtain ⟨n, hnN, hn⟩ := iwn_conj_mem_normalizer h hk htsH (iwn_ts_ne_one h)
            htH (Work.BSW.t_ne_one h)
            (Work.BSW.involutions_conj h (t * s) (iwn_orderOf_ts h hk))
        refine isConj_iff.mpr ⟨⟨n⁻¹, N.inv_mem hnN⟩, ?_⟩
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
        rw [h1]
        calc (n : G)⁻¹ * t * (n : G)
            = (n : G)⁻¹ * (n * (t * s) * (n : G)⁻¹) * (n : G) := by rw [hn]
          _ = t * s := by group
  have hidx : (H.subgroupOf N).index = 3 := by
    have hcent : Subgroup.centralizer ({⟨t, htN⟩} : Set ↥N) = H.subgroupOf N := by
      ext y
      rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
        Subgroup.mem_centralizer_singleton_iff]
      exact ⟨fun hh => congrArg Subtype.val hh, fun hh => Subtype.ext hh⟩
    rw [← hcent, Subgroup.index_centralizer_eq_ncard, hset, hpre]
  rw [← Subgroup.card_mul_index (H.subgroupOf N), hidx]
  have hcardH : Nat.card ↥(H.subgroupOf N) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHN).toEquiv,
      Work.BSW.Api.card_centralizer_of_card_K_two h hk]
  rw [hcardH]

/-- Every involution of `N_G(C_G(t))` lies in `C_G(t)`. -/
theorem iwn_mem_of_mem_normalizer_of_orderOf_two (h : BSWHyps2 G t s K) (hk : Nat.card ↥K = 2)
    {w : G} (hwN : w ∈ Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G))
    (hw2 : orderOf w = 2) : w ∈ Subgroup.centralizer ({t} : Set G) := by
  let H : Subgroup G := Subgroup.centralizer ({t} : Set G)
  let N : Subgroup G := Subgroup.normalizer (H : Set G)
  change w ∈ H
  have hHN : H ≤ N := Subgroup.le_normalizer
  have hwN' : w ∈ N := hwN
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hHnorm : (H.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHN).mpr le_rfl
  have hHcard : Nat.card ↥(H.subgroupOf N) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHN).toEquiv,
      Work.BSW.Api.card_centralizer_of_card_K_two h hk]
  have hHp : IsPGroup 2 ↥(H.subgroupOf N) := IsPGroup.of_card (n := 2) (by rw [hHcard]; norm_num)
  have hwG2 : orderOf (⟨w, hwN'⟩ : ↥N) = 2 := by rw [← Subgroup.orderOf_coe]; exact hw2
  have hwp : IsPGroup 2 ↥(Subgroup.zpowers (⟨w, hwN'⟩ : ↥N)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hwG2]; norm_num)
  obtain ⟨Q, hQle⟩ := IsPGroup.exists_le_sylow hwp
  haveI := hHnorm
  have hHleQ : H.subgroupOf N ≤ (Q : Subgroup ↥N) := IsPGroup.le_sylow_of_normal hHp Q
  have hQcard : Nat.card ↥(Q : Subgroup ↥N) ≤ 4 := by
    have hm := iwn_two_subgroup_le_four h hk ((Q : Subgroup ↥N).map N.subtype)
      (Q.isPGroup'.map N.subtype)
    rwa [Subgroup.card_map_of_injective (f := N.subtype) (fun _ _ hh => Subtype.ext hh)] at hm
  have hQeq : (Q : Subgroup ↥N) = H.subgroupOf N :=
    (Subgroup.eq_of_le_of_card_ge hHleQ (by rw [hHcard]; exact hQcard)).symm
  have : (⟨w, hwN'⟩ : ↥N) ∈ H.subgroupOf N := by
    rw [← hQeq]; exact hQle (Subgroup.mem_zpowers _)
  rwa [Subgroup.mem_subgroupOf] at this

/-- The involutions lying in `N_G(C_G(t))` are exactly `t`, `s`, `t*s`. -/
theorem iwn_involutions_mem_normalizer_ncard (h : BSWHyps2 G t s K) (hk : Nat.card ↥K = 2) :
    {x : G | orderOf x = 2 ∧
      x ∈ Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G)}.ncard = 3 := by
  have hset : {x : G | orderOf x = 2 ∧
        x ∈ Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G)}
      = ({t, s, t * s} : Set G) := by
    ext x
    constructor
    · rintro ⟨hx2, hxN⟩
      have hxH := iwn_mem_of_mem_normalizer_of_orderOf_two h hk hxN hx2
      have hmem := (iwn_mem_centralizer_H_iff h hk x).mp hxH
      rcases hmem with h1 | h1 | h1 | h1
      · rw [h1, orderOf_one] at hx2; exact absurd hx2 (by norm_num)
      · show x ∈ ({t, s, t * s} : Set G); rw [h1]; simp
      · show x ∈ ({t, s, t * s} : Set G); rw [h1]; simp
      · show x ∈ ({t, s, t * s} : Set G); rw [h1]; simp
    · intro hx
      have hx' : x = t ∨ x = s ∨ x = t * s := by simpa using hx
      rcases hx' with rfl | rfl | rfl
      · exact ⟨Work.BSW.orderOf_t h, Subgroup.le_normalizer (Work.BSW.t_mem_centralizer_t h)⟩
      · exact ⟨Work.BSW.orderOf_s h, Subgroup.le_normalizer (Work.BSW.s_mem_centralizer_t h)⟩
      · exact ⟨iwn_orderOf_ts h hk,
          Subgroup.le_normalizer (Subgroup.mul_mem _ (Work.BSW.t_mem_centralizer_t h)
            (Work.BSW.s_mem_centralizer_t h))⟩
  rw [hset, iwn_ncard_three h]

theorem iwn_ncard_image_mk' (h : BSWHyps2 G t s K) (hk : Nat.card ↥K = 2) :
    ((fun x : G => (QuotientGroup.mk x : G ⧸ Subgroup.centralizer ({t} : Set G))) ''
      (Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G) : Set G)).ncard = 3 := by
  let H : Subgroup G := Subgroup.centralizer ({t} : Set G)
  let N : Subgroup G := Subgroup.normalizer (H : Set G)
  change ((fun x : G => (QuotientGroup.mk x : G ⧸ H)) '' (N : Set G)).ncard = 3
  have hHN : H ≤ N := Subgroup.le_normalizer
  have hQcard : Nat.card (↥N ⧸ (H.subgroupOf N)) = 3 := by
    rw [← Subgroup.index_eq_card (H.subgroupOf N)]
    have hc := Subgroup.card_mul_index (H.subgroupOf N)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHN).toEquiv,
      Work.BSW.Api.card_centralizer_of_card_K_two h hk, iwn_card_normalizer h hk] at hc
    omega
  have hb : (Set.univ : Set (↥N ⧸ (H.subgroupOf N))).ncard =
      ((fun x : G => (QuotientGroup.mk x : G ⧸ H)) '' (N : Set G)).ncard :=
    Set.ncard_congr
    (s := (Set.univ : Set (↥N ⧸ (H.subgroupOf N))))
    (t := ((fun x : G => (QuotientGroup.mk x : G ⧸ H)) '' (N : Set G)))
    (fun (q : ↥N ⧸ (H.subgroupOf N)) (_ : q ∈ Set.univ) =>
      (QuotientGroup.mk ((Quotient.out q : ↥N) : G) : G ⧸ H))
    (fun (q : ↥N ⧸ (H.subgroupOf N)) _ =>
      ⟨((Quotient.out q : ↥N) : G), (Quotient.out q).2, rfl⟩)
    (fun q1 q2 _ _ hq => by
      have h1 : ((Quotient.out q1 : ↥N) : G)⁻¹ * ((Quotient.out q2 : ↥N) : G) ∈ H :=
        QuotientGroup.eq.mp hq
      have h2 : (Quotient.out q1)⁻¹ * (Quotient.out q2) ∈ H.subgroupOf N := by
        rwa [Subgroup.mem_subgroupOf]
      rw [← QuotientGroup.out_eq' q1, ← QuotientGroup.out_eq' q2, QuotientGroup.eq]
      exact h2)
    (fun c hc => by
      rw [Set.mem_image] at hc
      obtain ⟨n, hnN, hnc⟩ := hc
      refine ⟨QuotientGroup.mk (s := H.subgroupOf N) (⟨n, hnN⟩ : ↥N), Set.mem_univ _, ?_⟩
      show (QuotientGroup.mk (s := H)
        ((Quotient.out (QuotientGroup.mk (s := H.subgroupOf N) (⟨n, hnN⟩ : ↥N)) : ↥N) : G) :
        G ⧸ H) = c
      rw [← hnc]
      apply Quotient.sound
      have hq : ((Quotient.out (QuotientGroup.mk (s := H.subgroupOf N) (⟨n, hnN⟩ : ↥N)) : ↥N)⁻¹ *
          (⟨n, hnN⟩ : ↥N)) ∈ H.subgroupOf N :=
        (QuotientGroup.eq (s := H.subgroupOf N)).mp
          (QuotientGroup.out_eq' (s := H.subgroupOf N)
            (QuotientGroup.mk (s := H.subgroupOf N) (⟨n, hnN⟩ : ↥N)))
      have hq2 : (((Quotient.out (QuotientGroup.mk (s := H.subgroupOf N)
          (⟨n, hnN⟩ : ↥N)) : ↥N) : G))⁻¹ * n ∈ H := by
        have := Subgroup.mem_subgroupOf.mp hq
        simpa using this
      exact (QuotientGroup.leftRel_apply (s := H)).mpr hq2)
  rw [Set.ncard_univ] at hb
  rw [hQcard] at hb
  exact hb.symm

/-- Two involutions in the same coset of `C_G(t)` (a coset different from `C_G(t)`) coincide. -/
theorem iwn_eq_of_coset (h : BSWHyps2 G t s K) (hk : Nat.card ↥K = 2) {b : G}
    (hbH : b ∉ Subgroup.centralizer ({t} : Set G)) {x y : G}
    (hx : x ∈ (fun h => b * h) '' (Subgroup.centralizer ({t} : Set G) : Set G))
    (hx2 : orderOf x = 2)
    (hy : y ∈ (fun h => b * h) '' (Subgroup.centralizer ({t} : Set G) : Set G))
    (hy2 : orderOf y = 2) : x = y := by
  obtain ⟨h1, hh1, hx1⟩ := hx
  obtain ⟨h2, hh2, hy1⟩ := hy
  change b * h1 = x at hx1
  change b * h2 = y at hy1
  have hx2pow : x * x = 1 := by
    have := pow_orderOf_eq_one x; rw [hx2] at this; simpa [pow_two] using this
  have hy2pow : y * y = 1 := by
    have := pow_orderOf_eq_one y; rw [hy2] at this; simpa [pow_two] using this
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_left hx2pow
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_left hy2pow
  have hA : x⁻¹ * y ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [← hx1, ← hy1, mul_inv_rev, mul_assoc h1⁻¹ b⁻¹ (b * h2),
      ← mul_assoc b⁻¹ b h2, inv_mul_cancel, one_mul]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hh1) hh2
  rw [hxinv] at hA
  have hz2 : (x * y) * (x * y) = 1 := iwn_H_two h hk _ hA
  by_cases hz1 : x * y = 1
  · have : y = x * (x * y) := by rw [← mul_assoc, hx2pow, one_mul]
    rw [this, hz1, mul_one]
  · exfalso
    have hcomm : x * y = y * x := by
      have h5 : x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_left hz2).symm
      rw [h5, mul_inv_rev, hxinv, hyinv]
    have hxmem : x ∈ Subgroup.centralizer ({x * y} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x * (x * y) = (x * x) * y := (mul_assoc x x y).symm
        _ = y := by rw [hx2pow, one_mul]
        _ = (x * y) * x := by rw [mul_assoc, ← hcomm, ← mul_assoc, hx2pow, one_mul]
    have hxH : x ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [iwn_centralizer_eq_H_of_mem h hk hA hz1]; exact hxmem
    exact hbH (by
      have h3 : x * h1⁻¹ ∈ Subgroup.centralizer ({t} : Set G) :=
        Subgroup.mul_mem _ hxH (Subgroup.inv_mem _ hh1)
      rw [← hx1] at h3
      simpa [mul_assoc] using h3)

/-- Each coset of `C_G(t)` outside `N_G(C_G(t))` contains exactly one involution. -/
theorem iwn_coset_count (h : BSWHyps2 G t s K) (hk : Nat.card ↥K = 2)
    {a : G} (ha : a ∉ Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G)) :
    ∃! x : G, x ∈ (fun h => a * h) '' (Subgroup.centralizer ({t} : Set G) : Set G) ∧
      orderOf x = 2 := by
  let H : Subgroup G := Subgroup.centralizer ({t} : Set G)
  let N : Subgroup G := Subgroup.normalizer (H : Set G)
  have hHN : H ≤ N := Subgroup.le_normalizer
  have haN : a ∉ N := ha
  have haH : a ∉ H := fun hh => haN (Subgroup.le_normalizer hh)
  have hJ : {x : G | orderOf x = 2}.ncard = H.index := by
    rw [Work.BSW.Api.ncard_involutions_eq_index h]
  have hJN : {x : G | orderOf x = 2 ∧ x ∈ N}.ncard = 3 := by
    change {x : G | orderOf x = 2 ∧
      x ∈ Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G)}.ncard = 3
    exact iwn_involutions_mem_normalizer_ncard h hk
  have hJout : {x : G | orderOf x = 2 ∧ x ∉ N}.ncard = H.index - 3 := by
    have hset : {x : G | orderOf x = 2 ∧ x ∉ N}
        = {x : G | orderOf x = 2} \ {x : G | orderOf x = 2 ∧ x ∈ N} := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_sdiff]; tauto
    rw [hset, Set.ncard_sdiff (by intro x hx; exact hx.1), hJ, hJN]
  have hSN : ((fun x : G => (QuotientGroup.mk x : G ⧸ H)) '' (N : Set G)).ncard = 3 := by
    change ((fun x : G => (QuotientGroup.mk x : G ⧸ H)) ''
      (Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G) : Set G)).ncard = 3
    exact iwn_ncard_image_mk' h hk
  have hout : {c : G ⧸ H | c ∉ (fun x : G => (QuotientGroup.mk x : G ⧸ H)) '' (N : Set G)}.ncard
      = H.index - 3 := by
    have hset : {c : G ⧸ H | c ∉ (fun x : G => (QuotientGroup.mk x : G ⧸ H)) '' (N : Set G)}
        = (Set.univ \ ((fun x : G => (QuotientGroup.mk x : G ⧸ H)) '' (N : Set G))) := by
      ext c; simp
    rw [hset, Set.ncard_sdiff (Set.subset_univ _), Set.ncard_univ, ← Subgroup.index_eq_card H, hSN]
  have himg : ((fun x : G => (QuotientGroup.mk x : G ⧸ H)) '' {x : G | orderOf x = 2 ∧ x ∉ N})
      ⊆ {c : G ⧸ H | c ∉ (fun x : G => (QuotientGroup.mk x : G ⧸ H)) '' (N : Set G)} := by
    rw [Set.image_subset_iff]
    intro x hx
    rw [Set.mem_preimage]
    rintro ⟨n, hnN, hnm⟩
    have h1 : n⁻¹ * x ∈ H := QuotientGroup.eq.mp hnm
    have h2 : x ∈ N := by
      have h3 : x = n * (n⁻¹ * x) := by rw [← mul_assoc, mul_inv_cancel, one_mul]
      rw [h3]; exact N.mul_mem hnN (hHN h1)
    exact hx.2 h2
  have hcardimg : ((fun x : G => (QuotientGroup.mk x : G ⧸ H)) '' {x : G | orderOf x = 2 ∧ x ∉ N}).ncard
      = H.index - 3 := by
    have hcongr := Set.ncard_congr
      (s := {x : G | orderOf x = 2 ∧ x ∉ N})
      (t := ((fun x : G => (QuotientGroup.mk x : G ⧸ H)) '' {x : G | orderOf x = 2 ∧ x ∉ N}))
      (fun (x : G) (_ : x ∈ {x : G | orderOf x = 2 ∧ x ∉ N}) => (QuotientGroup.mk x : G ⧸ H))
      (fun x hx => ⟨x, hx, rfl⟩)
      (fun x y hx hy hxy => by
        have hxH : x ∉ H := fun hh => hx.2 (Subgroup.le_normalizer hh)
        have h1 : x⁻¹ * y ∈ H := QuotientGroup.eq.mp hxy
        exact iwn_eq_of_coset (b := x) h hk hxH
          (x := x) ⟨1, Subgroup.one_mem _, by show x * 1 = x; rw [mul_one]⟩ hx.1
          (y := y) ⟨x⁻¹ * y, h1, by show x * (x⁻¹ * y) = y; rw [← mul_assoc, mul_inv_cancel, one_mul]⟩ hy.1)
      (fun c hc => by
        obtain ⟨a, ha, hfa⟩ := hc
        exact ⟨a, ha, hfa⟩)
    exact hcongr.symm.trans hJout
  have heq : ((fun x : G => (QuotientGroup.mk x : G ⧸ H)) '' {x : G | orderOf x = 2 ∧ x ∉ N})
      = {c : G ⧸ H | c ∉ (fun x : G => (QuotientGroup.mk x : G ⧸ H)) '' (N : Set G)} :=
    Set.eq_of_subset_of_ncard_le himg (by rw [hout, hcardimg])
  have hca : (QuotientGroup.mk a : G ⧸ H) ∉
      (fun x : G => (QuotientGroup.mk x : G ⧸ H)) '' (N : Set G) := by
    rintro ⟨n, hnN, hnm⟩
    refine haN ?_
    have h1 : n⁻¹ * a ∈ H := QuotientGroup.eq.mp hnm
    have h2 : a = n * (n⁻¹ * a) := by rw [← mul_assoc, mul_inv_cancel, one_mul]
    rw [h2]; exact N.mul_mem hnN (hHN h1)
  have hca2 : (QuotientGroup.mk a : G ⧸ H) ∈
      ((fun x : G => (QuotientGroup.mk x : G ⧸ H)) '' {x : G | orderOf x = 2 ∧ x ∉ N}) := by
    rw [heq]; exact hca
  obtain ⟨x, hx, hxa⟩ := hca2
  have hxa' : x⁻¹ * a ∈ H := QuotientGroup.eq.mp hxa
  have hxcoset : x ∈ (fun h => a * h) '' (Subgroup.centralizer ({t} : Set G) : Set G) :=
    ⟨a⁻¹ * x, by simpa [mul_inv_rev] using Subgroup.inv_mem _ hxa', by
      show a * (a⁻¹ * x) = x; rw [← mul_assoc, mul_inv_cancel, one_mul]⟩
  refine ⟨x, ⟨hxcoset, hx.1⟩, ?_⟩
  intro y hy
  exact iwn_eq_of_coset (b := a) h hk haH (x := y) hy.1 hy.2 (y := x) ⟨a⁻¹ * x,
    by simpa [mul_inv_rev] using Subgroup.inv_mem _ hxa', by
      show a * (a⁻¹ * x) = x; rw [← mul_assoc, mul_inv_cancel, one_mul]⟩ hx.1

/-- If `u` is an involution outside `N_G(C_G(t))`, then `u` normalizes some subgroup of order `3`
contained in `N_G(C_G(t))`. -/
theorem involution_outside_normalizer_normalizes {G : Type} [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (t s : G) (K : Subgroup G)
    (h : Work.GW2.BSWHyps2 G t s K) (hk : Nat.card ↥K = 2) (u : G) (hu : orderOf u = 2)
    (huN : u ∉ Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G)) :
    ∃ T : Subgroup G, Nat.card T = 3 ∧
      T ≤ Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G) ∧
      u ∈ Subgroup.normalizer (T : Set G) := by
  let H : Subgroup G := Subgroup.centralizer ({t} : Set G)
  let N : Subgroup G := Subgroup.normalizer (H : Set G)
  have hHN : H ≤ N := Subgroup.le_normalizer
  have hu2 : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rw [hu] at this
    simpa [pow_two] using this
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_left hu2
  have huN' : u ∉ N := huN
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hdvd3 : 3 ∣ Nat.card ↥N := by
    rw [show Nat.card ↥N = 12 from iwn_card_normalizer h hk]
    norm_num
  obtain ⟨xN, hxN3⟩ := exists_prime_orderOf_dvd_card' 3 hdvd3
  let xG : G := (xN : G)
  have hxG3 : orderOf xG = 3 := by
    show orderOf (xN : G) = 3
    rw [Subgroup.orderOf_coe, hxN3]
  have hxGN : xG ∈ N := by show (xN : G) ∈ N; exact xN.2
  have hxnotH : xG ∉ H := by
    intro hh
    have h2 : xG * xG = 1 := iwn_H_two h hk xG hh
    have hd : orderOf xG ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rwa [pow_two])
    rw [hxG3] at hd
    exact absurd (Nat.le_of_dvd (by norm_num) hd) (by norm_num)
  have ha : u * xG ∉ N := by
    intro hc
    refine huN' ?_
    have h2 : (u * xG) * xG⁻¹ ∈ N := N.mul_mem hc (N.inv_mem hxGN)
    rwa [mul_assoc, mul_inv_cancel, mul_one] at h2
  obtain ⟨v, ⟨hv, hv2⟩, _⟩ := iwn_coset_count (a := u * xG) h hk ha
  obtain ⟨h0, hh0H, hh0⟩ := hv
  let w : G := xG * h0
  have hwN : w ∈ N := by show xG * h0 ∈ N; exact N.mul_mem hxGN (hHN hh0H)
  have hvw : v = u * w := by
    have hh0' : (u * xG) * h0 = v := hh0
    rw [← hh0', mul_assoc]
  have hv2pow : v * v = 1 := by
    have := pow_orderOf_eq_one v
    rw [hv2] at this
    simpa [pow_two] using this
  have huwu : u * w * u = w⁻¹ := by
    have hs : (u * w) * (u * w) = 1 := by rw [← hvw]; exact hv2pow
    have hsw : u * w = w⁻¹ * u := by
      rw [← inv_eq_of_mul_eq_one_left hs, mul_inv_rev, huinv]
    rw [hsw, mul_assoc, hu2, mul_one]
  have hHnorm : (H.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHN).mpr le_rfl
  haveI := hHnorm
  let xn : ↥N := ⟨xG, hxGN⟩
  let h0n : ↥N := ⟨h0, hHN hh0H⟩
  let wn : ↥N := ⟨w, hwN⟩
  have hxn3 : orderOf xn = 3 := (Subgroup.orderOf_coe xn).symm.trans hxG3
  have hwn_eq : wn = xn * h0n := by
    apply Subtype.ext
    show w = xG * h0
    rfl
  have hquot0 : QuotientGroup.mk' (H.subgroupOf N) h0n = 1 := by
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff h0n).mpr (by rw [Subgroup.mem_subgroupOf]; exact hh0H)
  have hquotx : QuotientGroup.mk' (H.subgroupOf N) wn =
      QuotientGroup.mk' (H.subgroupOf N) xn := by
    rw [hwn_eq, map_mul, hquot0, mul_one]
  have hquotx_ne : QuotientGroup.mk' (H.subgroupOf N) xn ≠ 1 := by
    intro hc
    rw [QuotientGroup.mk'_apply] at hc
    have hmem : xn ∈ H.subgroupOf N := (QuotientGroup.eq_one_iff xn).mp hc
    rw [Subgroup.mem_subgroupOf] at hmem
    exact hxnotH (by simpa using hmem)
  have hquotx3 : orderOf (QuotientGroup.mk' (H.subgroupOf N) xn) = 3 := by
    have hd : orderOf (QuotientGroup.mk' (H.subgroupOf N) xn) ∣ 3 := by
      have hk' := orderOf_map_dvd (QuotientGroup.mk' (H.subgroupOf N)) xn
      rwa [hxn3] at hk'
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hquotx_ne
    · exact h3
  have hdvdw : 3 ∣ orderOf w := by
    have h1 : 3 ∣ orderOf wn := by
      rw [← hquotx3, ← hquotx]
      exact orderOf_map_dvd (QuotientGroup.mk' (H.subgroupOf N)) wn
    have h2 : orderOf wn = orderOf w := (Subgroup.orderOf_coe wn).symm
    rwa [h2] at h1
  haveI : Fintype ↥N := Fintype.ofFinite _
  have hdvd12 : orderOf w ∣ 12 := by
    have h1 : orderOf wn ∣ Fintype.card ↥N := orderOf_dvd_card (x := wn)
    rw [Fintype.card_eq_nat_card, show Nat.card ↥N = 12 from iwn_card_normalizer h hk] at h1
    have h2 : orderOf wn = orderOf w := (Subgroup.orderOf_coe wn).symm
    rwa [h2] at h1
  have hdpos : 0 < orderOf w := Nat.pos_of_dvd_of_pos hdvd12 (by norm_num)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, orderOf w = 3 * m :=
    ⟨orderOf w / 3, (Nat.mul_div_cancel' hdvdw).symm⟩
  have hmpos : 0 < m := by omega
  have hwmpow3 : (w ^ m) ^ 3 = 1 := by
    rw [← pow_mul]
    have : m * 3 = orderOf w := by rw [hm]; ring
    rw [this, pow_orderOf_eq_one]
  have hwmpow_ne : w ^ m ≠ 1 := by
    intro hc
    have hdm : orderOf w ∣ m := orderOf_dvd_iff_pow_eq_one.mpr hc
    have hle : orderOf w ≤ m := Nat.le_of_dvd hmpos hdm
    omega
  have hdvd3z : orderOf (w ^ m) ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hwmpow3
  have hz3' : orderOf (w ^ m) = 3 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd3z with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hwmpow_ne
    · exact h3
  have hconj_z : (MulAut.conj u) (w ^ m) = (w ^ m)⁻¹ := by
    rw [MulAut.conj_apply]
    calc u * w ^ m * u⁻¹ = (MulAut.conj u) (w ^ m) := by rw [MulAut.conj_apply]
      _ = ((MulAut.conj u) w) ^ m := by rw [map_pow]
      _ = (u * w * u⁻¹) ^ m := by rw [MulAut.conj_apply]
      _ = (u * w * u) ^ m := by rw [huinv]
      _ = (w⁻¹) ^ m := by rw [huwu]
      _ = (w ^ m)⁻¹ := by rw [inv_pow]
  refine ⟨Subgroup.zpowers (w ^ m), ?_, ?_, ?_⟩
  · rw [Nat.card_zpowers, hz3']
  · rw [Subgroup.zpowers_le]; exact N.pow_mem hwN m
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (Subgroup.zpowers (w ^ m)).map (MulAut.conj u).toMonoidHom
      = Subgroup.zpowers (w ^ m)
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers ((MulAut.conj u) (w ^ m)) = Subgroup.zpowers (w ^ m)
    rw [hconj_z, Subgroup.zpowers_inv]

end Work.BSW.Cases
