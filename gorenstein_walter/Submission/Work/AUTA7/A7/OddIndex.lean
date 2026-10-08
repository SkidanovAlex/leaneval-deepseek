import Mathlib
import Submission.Work.AUTA7.Defs
import Submission.Work.AUTA7.A7.OddIndexDefs
import Submission.Work.A7F.normal_K_in_centralizer
import Submission.Work.A7F.card_centralizer_a7Invol
import Submission.Work.A7F.Facts

namespace Work.AUTA7.A7

open Subgroup

set_option maxRecDepth 400000
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

/-!  ## Part 1: general group theory -/

/-- Conjugation commutes with integer powers. -/
private theorem conj_zpow {G : Type*} [Group G] (t x : G) (n : ℤ) :
    t * x ^ n * t⁻¹ = (t * x * t⁻¹) ^ n := by
  have h1 : t * x ^ n * t⁻¹ = (MulAut.conj t) (x ^ n) := (MulAut.conj_apply t (x ^ n)).symm
  have h2 : (MulAut.conj t) (x ^ n) = ((MulAut.conj t) x) ^ n := map_zpow (MulAut.conj t) x n
  have h3 : ((MulAut.conj t) x) ^ n = (t * x * t⁻¹) ^ n := by rw [MulAut.conj_apply t x]
  rw [h1, h2, h3]

/-- **A normal subgroup of order `3` of a group of order `24` is the only subgroup of order
`3`.** -/
theorem eq_of_card_three_of_normal {G : Type*} [Group G] [Finite G]
    {Z K L : Subgroup G} (hKZ : K ≤ Z) (hLZ : L ≤ Z) (hKn : (K.subgroupOf Z).Normal)
    (hK3 : Nat.card K = 3) (hL3 : Nat.card L = 3) (hZ : Nat.card Z = 24) : K = L := by
  haveI : (K.subgroupOf Z).Normal := hKn
  set K' : Subgroup ↥Z := K.subgroupOf Z
  set L' : Subgroup ↥Z := L.subgroupOf Z
  haveI : K'.Normal := hKn
  have hK'3 : Nat.card ↥K' = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKZ).toEquiv, hK3]
  have hL'3 : Nat.card ↥L' = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLZ).toEquiv, hL3]
  have hquot : Nat.card (↥Z ⧸ K') = 8 := by
    rw [← Subgroup.index_eq_card]
    have h := Subgroup.index_mul_card K'
    rw [hK'3, hZ] at h
    omega
  set f : ↥L' →* (↥Z ⧸ K') := (QuotientGroup.mk' K').comp L'.subtype with hf
  have hcard := Subgroup.card_ker_mul_card_range f
  rw [hL'3] at hcard
  have hrange_dvd : Nat.card ↥(MonoidHom.range f) ∣ Nat.card (↥Z ⧸ K') :=
    Subgroup.card_subgroup_dvd_card _
  rw [hquot] at hrange_dvd
  have hrange_dvd3 : Nat.card ↥(MonoidHom.range f) ∣ 3 :=
    ⟨Nat.card ↥(f.ker), by rw [mul_comm]; exact hcard.symm⟩
  have hrange1 : Nat.card ↥(MonoidHom.range f) = 1 := by
    have h : Nat.card ↥(MonoidHom.range f) ∣ Nat.gcd 3 8 := Nat.dvd_gcd hrange_dvd3 hrange_dvd
    rw [show Nat.gcd 3 8 = 1 from by norm_num] at h
    exact Nat.eq_one_of_dvd_one h
  have hker3 : Nat.card ↥(f.ker) = 3 := by
    have h := hcard
    rw [hrange1] at h
    omega
  have hker_top : f.ker = ⊤ := Subgroup.eq_top_of_card_eq f.ker (by rw [hker3, hL'3])
  have hL'le : L' ≤ K' := by
    intro x hx
    have hxker : (⟨x, hx⟩ : ↥L') ∈ f.ker := by rw [hker_top]; trivial
    have hfx : (QuotientGroup.mk' K') x = 1 := by
      have := (MonoidHom.mem_ker).mp hxker
      simpa [hf, MonoidHom.comp_apply] using this
    rw [← QuotientGroup.ker_mk' K']
    exact (MonoidHom.mem_ker).mpr hfx
  have hLK : L ≤ K := by
    intro x hx
    have hx' : (⟨x, hLZ hx⟩ : ↥Z) ∈ L' := hx
    exact Subgroup.mem_subgroupOf.mp (hL'le hx')
  exact (Subgroup.eq_of_le_of_card_ge hLK (by rw [hK3, hL3])).symm

/-- **Conjugation preserves the normality of a cyclic subgroup of order `3` in a centralizer.** -/
theorem conj_normal_zpowers {G : Type*} [Group G] {a b g : G}
    (hb : b ∈ Subgroup.centralizer ({a} : Set G))
    (hn : ((Subgroup.zpowers b).subgroupOf (Subgroup.centralizer ({a} : Set G))).Normal) :
    ((Subgroup.zpowers (g * b * g⁻¹)).subgroupOf
      (Subgroup.centralizer ({g * a * g⁻¹} : Set G))).Normal := by
  have hle : Subgroup.zpowers b ≤ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.zpowers_le.mpr hb
  have hn' : ∀ h k : G, h ∈ Subgroup.zpowers b →
      k ∈ Subgroup.centralizer ({a} : Set G) → k * h * k⁻¹ ∈ Subgroup.zpowers b :=
    (Subgroup.normal_subgroupOf_iff hle).mp hn
  rw [Subgroup.normal_subgroupOf_iff]
  · intro h k hh hk
    rw [Subgroup.mem_zpowers_iff] at hh ⊢
    obtain ⟨n, rfl⟩ := hh
    have hk' : g⁻¹ * k * g ∈ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hk ⊢
      calc (g⁻¹ * k * g) * a = g⁻¹ * (k * (g * a * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * a * g⁻¹) * k) * g := by rw [hk]
        _ = a * (g⁻¹ * k * g) := by group
    obtain ⟨m, hm⟩ :=
      Subgroup.mem_zpowers_iff.mp (hn' b (g⁻¹ * k * g) (Subgroup.mem_zpowers b) hk')
    refine ⟨m * n, ?_⟩
    rw [zpow_mul]
    have hconj : k * (g * b * g⁻¹) * k⁻¹ = (g * b * g⁻¹) ^ m := by
      have h1 : k * (g * b * g⁻¹) * k⁻¹ =
          g * ((g⁻¹ * k * g) * b * (g⁻¹ * k * g)⁻¹) * g⁻¹ := by group
      rw [h1, ← hm, conj_zpow g b m]
    have hpow : k * (g * b * g⁻¹) ^ n * k⁻¹ = (k * (g * b * g⁻¹) * k⁻¹) ^ n :=
      conj_zpow k (g * b * g⁻¹) n
    rw [hpow, hconj]
  · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    calc (g * b * g⁻¹) * (g * a * g⁻¹) = g * (b * a) * g⁻¹ := by group
      _ = g * (a * b) * g⁻¹ := by rw [Subgroup.mem_centralizer_singleton_iff.mp hb]
      _ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group

/-- The image of `⟨x⟩` under an isomorphism is `⟨ψ x⟩`. -/
theorem map_zpowers {G H : Type*} [Group G] [Group H] (ψ : G ≃* H) (x : G) :
    (Subgroup.zpowers x).map ψ.toMonoidHom = Subgroup.zpowers (ψ x) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ⟨k, (map_zpow ψ.toMonoidHom x k).symm⟩
  · intro h
    rw [Subgroup.mem_zpowers_iff] at h
    obtain ⟨k, hk⟩ := h
    refine ⟨ψ.symm y, Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩, by simp⟩
    rw [← hk, map_zpow, ψ.symm_apply_apply]

/-- The image of `⟨x⟩` under the inclusion of a subgroup is `⟨x⟩`. -/
theorem map_zpowers_subtype {Q : Type*} [Group Q] (L : Subgroup Q) (x : ↥L) :
    (Subgroup.zpowers x).map L.subtype = Subgroup.zpowers (L.subtype x) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ⟨k, by rw [map_zpow]⟩
  · intro hy
    rw [Subgroup.mem_zpowers_iff] at hy
    obtain ⟨k, hk⟩ := hy
    exact ⟨x ^ k, Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩, by rw [map_zpow, hk]⟩

/-- Centralizers of singletons transport along an isomorphism. -/
theorem map_centralizer_singleton {G H : Type*} [Group G] [Group H] (ψ : G ≃* H) (z : G) :
    (Subgroup.centralizer ({z} : Set G)).map ψ.toMonoidHom =
      Subgroup.centralizer ({ψ z} : Set H) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    simpa using congrArg ψ.toMonoidHom hy
  · intro hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    refine Subgroup.mem_map.mpr ⟨ψ.symm x, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply ψ.injective
    simpa using hx

/-- The order of the centralizer of a point transports along an isomorphism. -/
theorem nat_card_centralizer_singleton {G H : Type*} [Group G] [Group H] (ψ : G ≃* H) (z : G) :
    Nat.card (Subgroup.centralizer ({z} : Set G)) =
      Nat.card (Subgroup.centralizer ({ψ z} : Set H)) := by
  rw [← map_centralizer_singleton ψ z]
  exact (Subgroup.card_map_of_injective ψ.injective).symm

/-- Normality of `⟨x⟩` in the centralizer transports along an isomorphism. -/
theorem normal_zpowers_centralizer_of_map {G H : Type*} [Group G] [Group H]
    (ψ : G ≃* H) {z : G} {x : G}
    (hxz : x ∈ Subgroup.centralizer ({z} : Set G))
    (hn : ((Subgroup.zpowers (ψ x)).subgroupOf
      (Subgroup.centralizer ({ψ z} : Set H))).Normal) :
    ((Subgroup.zpowers x).subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal := by
  have hle : Subgroup.zpowers x ≤ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.zpowers_le.mpr hxz
  have hmaple : Subgroup.zpowers (ψ x) ≤ Subgroup.centralizer ({ψ z} : Set H) := by
    rw [← map_zpowers ψ x, ← map_centralizer_singleton ψ z]
    exact Subgroup.map_mono hle
  have hn' : ∀ a b : H, a ∈ Subgroup.zpowers (ψ x) →
      b ∈ Subgroup.centralizer ({ψ z} : Set H) → b * a * b⁻¹ ∈ Subgroup.zpowers (ψ x) :=
    (Subgroup.normal_subgroupOf_iff hmaple).mp hn
  rw [Subgroup.normal_subgroupOf_iff hle]
  intro a b ha hb
  have hba : ψ b ∈ Subgroup.centralizer ({ψ z} : Set H) := by
    rw [← map_centralizer_singleton ψ z, Subgroup.mem_map]
    exact ⟨b, hb, rfl⟩
  have hxa : ψ a ∈ Subgroup.zpowers (ψ x) := by
    rw [← map_zpowers ψ x, Subgroup.mem_map]
    exact ⟨a, ha, rfl⟩
  have := hn' (ψ a) (ψ b) hxa hba
  rw [← map_zpowers ψ x, Subgroup.mem_map] at this
  obtain ⟨c, hc, hca⟩ := this
  have hcab : c = b * a * b⁻¹ := by
    apply ψ.injective
    simpa using hca
  rwa [hcab] at hc

/-- **Every element has `2`-power order if the only elements of odd order are trivial.** -/
theorem exists_eq_two_pow_of_odd_eq_one {G : Type*} [Group G] [Finite G]
    (h : ∀ x : G, Odd (orderOf x) → x = 1) (x : G) : ∃ k, orderOf x = 2 ^ k := by
  have key : ∀ m : ℕ, ∀ y : G, orderOf y = m → ∃ k, m = 2 ^ k := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro y hm
      rcases Nat.even_or_odd m with hev | hoddm
      · obtain ⟨j, hj⟩ := hev
        have hm2 : orderOf y = 2 * j := by rw [hm, hj, two_mul]
        have hx0 : orderOf y ≠ 0 := (orderOf_pos y).ne'
        have hj0 : j ≠ 0 := by
          rintro rfl
          rw [mul_zero] at hm2
          exact hx0 hm2
        have hm_eq : m = 2 * j := by rw [← hm]; exact hm2
        have hlt : j < m := by rw [hm_eq]; omega
        have h2 : orderOf (y ^ 2) = j := by
          rw [orderOf_pow, hm2]
          have hg : Nat.gcd (2 * j) 2 = 2 := by
            rw [Nat.gcd_eq_right_iff_dvd]
            exact ⟨j, rfl⟩
          rw [hg, Nat.mul_div_cancel_left j (by norm_num)]
        obtain ⟨k, hk⟩ := ih j hlt (y ^ 2) h2
        exact ⟨k + 1, by rw [hm_eq, hk]; ring⟩
      · have hy1 : y = 1 := h y (by rw [hm]; exact hoddm)
        refine ⟨0, ?_⟩
        rw [← hm, hy1, orderOf_one]
        norm_num
  exact key (orderOf x) x rfl

/-- **If an automorphism of odd order sends an element of order `3` into its own cyclic
subgroup, it fixes it.** -/
theorem mulAut_apply_eq_of_mem_zpowers {G : Type*} [Group G] (α : MulAut G)
    (hodd : Odd (orderOf α)) {x : G} (hx : orderOf x = 3)
    (h : α x ∈ Subgroup.zpowers x) : α x = x := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  have hx3 : x ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, ← hx]
    exact pow_orderOf_eq_one x
  have h2order : orderOf (α x) = 3 := by
    have hh := orderOf_injective α.toMonoidHom α.injective x
    rw [hx] at hh
    simpa using hh
  have hne : x ^ k ≠ 1 := by
    intro h1
    have h3 : orderOf (x ^ k) = orderOf (α x) := by rw [hk]
    rw [h1, orderOf_one, h2order] at h3
    omega
  have hdvd : ¬ (3 : ℤ) ∣ k := by
    rintro ⟨j, hj⟩
    refine hne ?_
    rw [hj, zpow_mul]
    simp [hx3]
  have hmod : k % 3 = 1 ∨ k % 3 = 2 := by omega
  have hdec : k = k % 3 + 3 * (k / 3) := by omega
  have hxk_eq : x ^ k = x ^ (k % 3) := by
    rw [hdec, zpow_add, zpow_mul]
    simp [hx3]
  have hfix : α (α x) = x := by
    rcases hmod with h1 | h2
    · have hxα : α x = x := by rw [← hk, hxk_eq, h1, zpow_one]
      rw [hxα, hxα]
    · have hxα : α x = x ^ (2 : ℤ) := by rw [← hk, hxk_eq, h2]
      calc α (α x) = α (x ^ (2 : ℤ)) := by rw [hxα]
        _ = (α x) ^ (2 : ℤ) := map_zpow α x 2
        _ = (x ^ (2 : ℤ)) ^ (2 : ℤ) := by rw [hxα]
        _ = x ^ ((2 : ℤ) * 2) := (zpow_mul x 2 2).symm
        _ = x ^ (4 : ℤ) := by norm_num
        _ = x ^ ((1 : ℤ) + 3) := by norm_num
        _ = x ^ (1 : ℤ) * x ^ (3 : ℤ) := by rw [zpow_add]
        _ = x := by rw [hx3, zpow_one, mul_one]
  have hpow2 : ∀ j : ℕ, ((α ^ 2) ^ j) x = x := by
    intro j
    induction j with
    | zero => rw [pow_zero]; rfl
    | succ j ih =>
      rw [pow_succ]
      show ((α ^ 2) ^ j) ((α ^ 2) x) = x
      have hquad : (α ^ 2) x = x := by
        rw [pow_two]
        show (α * α) x = x
        rw [show (α * α) x = α (α x) from rfl, hfix]
      rw [hquad, ih]
  obtain ⟨t, ht⟩ : ∃ t : ℕ, orderOf α = 2 * t + 1 := by
    have := Nat.odd_iff.mp hodd
    exact ⟨orderOf α / 2, by omega⟩
  have hkey : α = (α ^ 2) ^ (t + 1) := by
    rw [← pow_mul, show 2 * (t + 1) = orderOf α + 1 by rw [ht]; ring, pow_succ,
      pow_orderOf_eq_one, one_mul]
  calc α x = ((α ^ 2) ^ (t + 1)) x := congrArg (fun f : MulAut G => f x) hkey
    _ = x := hpow2 (t + 1)

/-!  ## Part 2: odd-order automorphisms of `D₈` -/

private theorem zmod4_four_sum : ∀ d i : ZMod 4, d + (d + (d + (d + i))) = i := by decide

private theorem zmod4_three_mul_three : ∀ i : ZMod 4, (3 : ZMod 4) * (3 * i) = i := by decide

private theorem zmod4_three_sum : ∀ d i : ZMod 4, d + 3 * (d + 3 * i) = i := by decide

/-- Any automorphism of the dihedral group of order `8` has `4`-th power `1`. -/
theorem mulAut_dihedralGroup_four_pow_four (σ : MulAut (DihedralGroup 4)) : σ ^ 4 = 1 := by
  have h2sq : ((σ (DihedralGroup.r 1)) : DihedralGroup 4) ^ 2 ≠ 1 := by
    intro hcon
    have h1 : σ (DihedralGroup.r (2 : ZMod 4)) = 1 := by
      have hr2 : (DihedralGroup.r (2 : ZMod 4) : DihedralGroup 4) =
          (DihedralGroup.r 1) ^ 2 := by
        rw [DihedralGroup.r_one_pow]; simp
      rw [hr2, map_pow, hcon]
    have h2 : (DihedralGroup.r (2 : ZMod 4) : DihedralGroup 4) = 1 :=
      σ.injective (by rw [h1, map_one])
    exact absurd h2 (by decide)
  obtain ⟨c, hc, hc13⟩ : ∃ c : ZMod 4, σ (DihedralGroup.r 1) = DihedralGroup.r c ∧
      (c = 1 ∨ c = 3) := by
    cases' hval : σ (DihedralGroup.r 1) with i i
    · refine ⟨i, rfl, ?_⟩
      exact (by decide : ∀ i : ZMod 4, ((DihedralGroup.r i : DihedralGroup 4)) ^ 2 ≠ 1 →
        i = 1 ∨ i = 3) i (by rw [← hval]; exact h2sq)
    · exfalso
      have hsq : ((DihedralGroup.sr i : DihedralGroup 4)) ^ 2 = 1 := by
        rw [pow_two, DihedralGroup.sr_mul_self]
      exact h2sq (by rw [hval]; exact hsq)
  have hrotσ : ∀ i : ZMod 4, σ (DihedralGroup.r i) = DihedralGroup.r (c * i) := by
    intro i
    have hi : (DihedralGroup.r i : DihedralGroup 4) = (DihedralGroup.r 1) ^ i.val := by
      rw [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
    calc σ (DihedralGroup.r i) = σ ((DihedralGroup.r 1) ^ i.val) := by rw [hi]
      _ = (σ (DihedralGroup.r 1)) ^ i.val := map_pow σ _ _
      _ = (DihedralGroup.r c) ^ i.val := by rw [hc]
      _ = DihedralGroup.r (c * (i.val : ZMod 4)) := by
        rw [show (DihedralGroup.r c : DihedralGroup 4) = (DihedralGroup.r 1) ^ c.val by
          rw [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]]
        rw [← pow_mul, DihedralGroup.r_one_pow, Nat.cast_mul, ZMod.natCast_zmod_val,
          ZMod.natCast_zmod_val, mul_comm]
      _ = DihedralGroup.r (c * i) := by rw [ZMod.natCast_zmod_val]
  obtain ⟨d, hd⟩ : ∃ d : ZMod 4, σ (DihedralGroup.sr 0) = DihedralGroup.sr d := by
    cases' hval : σ (DihedralGroup.sr 0) with i i
    · exfalso
      rcases hc13 with hc1 | hc3
      · have hσi : σ (DihedralGroup.r i) = DihedralGroup.r i := by
          rw [hrotσ i, hc1, one_mul]
        have heq : (DihedralGroup.sr 0 : DihedralGroup 4) = DihedralGroup.r i :=
          σ.injective (by rw [hval]; exact hσi.symm)
        cases heq
      · have hσ3i : σ (DihedralGroup.r (3 * i)) = DihedralGroup.r i := by
          rw [hrotσ (3 * i), hc3, zmod4_three_mul_three]
        have heq : (DihedralGroup.sr 0 : DihedralGroup 4) = DihedralGroup.r (3 * i) :=
          σ.injective (by rw [hval]; exact hσ3i.symm)
        cases heq
    · exact ⟨i, rfl⟩
  have hpt : ∀ x : DihedralGroup 4, σ (σ (σ (σ x))) = x := by
    rcases hc13 with hc1 | hc3
    · have hσr : ∀ i : ZMod 4, σ (DihedralGroup.r i) = DihedralGroup.r i :=
        fun i => by rw [hrotσ i, hc1, one_mul]
      have href : ∀ j : ZMod 4, σ (DihedralGroup.sr j) = DihedralGroup.sr (d + j) := by
        intro j
        have h1 : (DihedralGroup.sr j : DihedralGroup 4) =
            DihedralGroup.r (-j) * DihedralGroup.sr 0 := by simp
        calc σ (DihedralGroup.sr j) = σ (DihedralGroup.r (-j) * DihedralGroup.sr 0) := by rw [h1]
          _ = σ (DihedralGroup.r (-j)) * σ (DihedralGroup.sr 0) := map_mul σ _ _
          _ = DihedralGroup.r (-j) * DihedralGroup.sr d := by rw [hσr (-j), hd]
          _ = DihedralGroup.sr (d + j) := by rw [DihedralGroup.r_mul_sr, sub_neg_eq_add]
      intro x
      cases x with
      | r i =>
        calc σ (σ (σ (σ (DihedralGroup.r i)))) = σ (σ (σ (DihedralGroup.r i))) :=
              congrArg σ (congrArg σ (congrArg σ (hσr i)))
          _ = σ (σ (DihedralGroup.r i)) := congrArg σ (congrArg σ (hσr i))
          _ = σ (DihedralGroup.r i) := congrArg σ (hσr i)
          _ = DihedralGroup.r i := hσr i
      | sr i =>
        calc σ (σ (σ (σ (DihedralGroup.sr i)))) = σ (σ (σ (DihedralGroup.sr (d + i)))) :=
              congrArg σ (congrArg σ (congrArg σ (href i)))
          _ = σ (σ (DihedralGroup.sr (d + (d + i)))) := congrArg σ (congrArg σ (href (d + i)))
          _ = σ (DihedralGroup.sr (d + (d + (d + i)))) := congrArg σ (href (d + (d + i)))
          _ = DihedralGroup.sr (d + (d + (d + (d + i)))) := href (d + (d + (d + i)))
          _ = DihedralGroup.sr i := by rw [zmod4_four_sum]
    · have hσr : ∀ i : ZMod 4, σ (DihedralGroup.r i) = DihedralGroup.r (3 * i) :=
        fun i => by rw [hrotσ i, hc3]
      have hσ2r : ∀ i : ZMod 4, σ (σ (DihedralGroup.r i)) = DihedralGroup.r i := by
        intro i
        calc σ (σ (DihedralGroup.r i)) = σ (DihedralGroup.r (3 * i)) := congrArg σ (hσr i)
          _ = DihedralGroup.r (3 * (3 * i)) := hσr (3 * i)
          _ = DihedralGroup.r i := by rw [zmod4_three_mul_three]
      have href : ∀ j : ZMod 4, σ (DihedralGroup.sr j) = DihedralGroup.sr (d + 3 * j) := by
        intro j
        have h1 : (DihedralGroup.sr j : DihedralGroup 4) =
            DihedralGroup.r (-j) * DihedralGroup.sr 0 := by simp
        calc σ (DihedralGroup.sr j) = σ (DihedralGroup.r (-j) * DihedralGroup.sr 0) := by rw [h1]
          _ = σ (DihedralGroup.r (-j)) * σ (DihedralGroup.sr 0) := map_mul σ _ _
          _ = DihedralGroup.r (3 * (-j)) * DihedralGroup.sr d := by rw [hσr (-j), hd]
          _ = DihedralGroup.sr (d + 3 * j) := by
            rw [DihedralGroup.r_mul_sr]
            congr 1
            ring
      have hσ2s : ∀ j : ZMod 4, σ (σ (DihedralGroup.sr j)) = DihedralGroup.sr j := by
        intro j
        calc σ (σ (DihedralGroup.sr j)) = σ (DihedralGroup.sr (d + 3 * j)) := congrArg σ (href j)
          _ = DihedralGroup.sr (d + 3 * (d + 3 * j)) := href (d + 3 * j)
          _ = DihedralGroup.sr j := by rw [zmod4_three_sum]
      intro x
      cases x with
      | r i =>
        calc σ (σ (σ (σ (DihedralGroup.r i)))) = σ (σ (DihedralGroup.r i)) :=
              congrArg σ (congrArg σ (hσ2r i))
          _ = DihedralGroup.r i := hσ2r i
      | sr i =>
        calc σ (σ (σ (σ (DihedralGroup.sr i)))) = σ (σ (DihedralGroup.sr i)) :=
              congrArg σ (congrArg σ (hσ2s i))
          _ = DihedralGroup.sr i := hσ2s i
  have hmul : ∀ x : DihedralGroup 4, (σ * (σ * (σ * σ))) x = x := fun x => hpt x
  have hpow : (σ : MulAut (DihedralGroup 4)) ^ 4 = σ * (σ * (σ * σ)) := by
    have h1 : (σ : MulAut (DihedralGroup 4)) ^ 4 = ((σ * σ) * σ) * σ := by
      rw [pow_succ, pow_succ, pow_two]
    calc (σ : MulAut (DihedralGroup 4)) ^ 4 = ((σ * σ) * σ) * σ := h1
      _ = (σ * σ) * (σ * σ) := mul_assoc (σ * σ) σ σ
      _ = σ * (σ * (σ * σ)) := mul_assoc σ σ (σ * σ)
  rw [hpow]
  exact MulEquiv.ext hmul

/-- **An automorphism of the dihedral group of order `8` has `2`-power order.** -/
theorem odd_order_mulAut_dihedralGroup_four (σ : MulAut (DihedralGroup 4))
    (hodd : Odd (orderOf σ)) : σ = 1 := by
  have hfour := mulAut_dihedralGroup_four_pow_four σ
  have hdvd : orderOf σ ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr hfour
  obtain ⟨k, hk⟩ := hdvd
  have hle : orderOf σ ≤ 4 := Nat.le_of_dvd (by norm_num) ⟨k, hk⟩
  have hpos : 0 < orderOf σ := orderOf_pos σ
  have hmem : orderOf σ = 1 ∨ orderOf σ = 2 ∨ orderOf σ = 3 ∨ orderOf σ = 4 := by omega
  rcases hmem with h | h | h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hodd; exact absurd hodd (by decide)
  · rw [h] at hk; omega
  · rw [h] at hodd; exact absurd hodd (by decide)

/-- **An element of odd order in the normalizer of a subgroup isomorphic to `D₈` centralizes
it.** -/
theorem OddOrderNormalizerCentralizes {G : Type*} [Group G] {D : Subgroup G}
    (e : ↥D ≃* DihedralGroup 4) {g : G} (hg : g ∈ Subgroup.normalizer (D : Set G))
    (hodd : Odd (orderOf g)) : ∀ d : G, d ∈ D → g * d * g⁻¹ = d := by
  classical
  set N : Subgroup G := Subgroup.normalizer (D : Set G) with hN
  have hgN : g ∈ N := hg
  have hDN : D ≤ N := Subgroup.le_normalizer
  haveI : (D.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDN).mpr (le_refl _)
  let φ : ↥N →* MulAut ↥(D.subgroupOf N) := MulAut.conjNormal
  let F : MulAut ↥(D.subgroupOf N) ≃* MulAut (DihedralGroup 4) :=
    (MulAut.congr (Subgroup.subgroupOfEquivOfLe hDN)).trans (MulAut.congr e)
  have hoddF : Odd (orderOf (F (φ ⟨g, hgN⟩))) := by
    have hdiv : orderOf (φ ⟨g, hgN⟩) ∣ orderOf g := by
      have h1 : orderOf (φ ⟨g, hgN⟩) ∣ orderOf (⟨g, hgN⟩ : ↥N) := orderOf_map_dvd φ ⟨g, hgN⟩
      have h2 : orderOf (⟨g, hgN⟩ : ↥N) = orderOf g :=
        (orderOf_injective N.subtype Subtype.coe_injective ⟨g, hgN⟩).symm
      rwa [h2] at h1
    obtain ⟨k, hk⟩ := hdiv
    have hk' : Odd (orderOf (φ ⟨g, hgN⟩) * k) := by rw [← hk]; exact hodd
    have hoddφ : Odd (orderOf (φ ⟨g, hgN⟩)) := (Nat.odd_mul.mp hk').1
    have h3 : orderOf (F (φ ⟨g, hgN⟩)) = orderOf (φ ⟨g, hgN⟩) :=
      orderOf_injective F.toMonoidHom F.injective (φ ⟨g, hgN⟩)
    rw [h3]
    exact hoddφ
  have hF1 : F (φ ⟨g, hgN⟩) = 1 := odd_order_mulAut_dihedralGroup_four _ hoddF
  have hφ1 : φ ⟨g, hgN⟩ = 1 := F.injective (by rw [hF1, map_one])
  intro d hd
  have hdN : d ∈ N := hDN hd
  set x : ↥(D.subgroupOf N) := ⟨⟨d, hdN⟩, hd⟩ with hx
  have happ : (MulAut.conjNormal (H := D.subgroupOf N) ⟨g, hgN⟩) x = x := by
    have h := congrArg (fun f : MulAut ↥(D.subgroupOf N) => f x) hφ1
    simpa [φ] using h
  have hconj := MulAut.conjNormal_apply (G := ↥N) (H := D.subgroupOf N) ⟨g, hgN⟩ x
  rw [happ] at hconj
  have h1 : (x : ↥N) = (⟨g, hgN⟩ : ↥N) * (x : ↥N) * (⟨g, hgN⟩ : ↥N)⁻¹ := hconj
  have h3 : d = g * d * g⁻¹ := by
    have := congrArg (fun z : ↥N => (z : G)) h1
    simpa [x] using this
  exact h3.symm

/-!  ## Part 3: `A₇` -/

/-- `A₇` has no subgroup of index `≤ 6` besides the whole group. -/
theorem A7IndexLeSix (H : Subgroup (alternatingGroup (Fin 7))) (h : H.index ≤ 6) : H = ⊤ := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 7)) := Work.A7.isSimpleGroup_alternatingGroup_seven
  haveI : H.normalCore.Normal := Subgroup.normalCore_normal H
  have hfact : H.normalCore.index ≤ H.index.factorial :=
    Subgroup.index_normalCore_le_factorial_index H
  have h720 : H.index.factorial ≤ 720 := by
    calc H.index.factorial ≤ (6).factorial := Nat.factorial_le h
      _ = 720 := by norm_num
  have hle : H.normalCore.index ≤ 720 := le_trans hfact h720
  have hne : H.normalCore ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.index_bot, Work.A7.card_alternatingGroup_seven] at hle
    omega
  have htop : H.normalCore = ⊤ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top H.normalCore with h1 | h1
    · exact absurd h1 hne
    · exact h1
  exact top_le_iff.mp (htop ▸ Subgroup.normalCore_le H)

/-- The join of the model Sylow `2`-subgroup with the fixed-point `3`-cycles of three of its
involutions is all of `A₇`. -/
theorem a7SylowJoinTop :
    Subgroup.closure ({a7R, a7S, Work.A7.a7ThreeCycle, c026, c136} :
      Set (alternatingGroup (Fin 7))) = ⊤ := by
  set J : Subgroup (alternatingGroup (Fin 7)) :=
    Subgroup.closure ({a7R, a7S, Work.A7.a7ThreeCycle, c026, c136} :
      Set (alternatingGroup (Fin 7))) with hJ
  have ha7R : a7R ∈ J := Subgroup.subset_closure (by simp)
  have hc1 : Work.A7.a7ThreeCycle ∈ J := Subgroup.subset_closure (by simp)
  have hc2 : c026 ∈ J := Subgroup.subset_closure (by simp)
  have hc3 : c136 ∈ J := Subgroup.subset_closure (by simp)
  have hdiv : ∀ x ∈ J, orderOf x ∣ Nat.card ↥J := by
    intro x hx
    have hle : Subgroup.zpowers x ≤ J := Subgroup.zpowers_le.mpr hx
    have hdvd : Nat.card ↥((Subgroup.zpowers x).subgroupOf J) ∣ Nat.card ↥J :=
      Subgroup.card_subgroup_dvd_card _
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers] at hdvd
  have h4 : 4 ∣ Nat.card ↥J := by
    have := hdiv a7R ha7R
    rwa [orderOf_a7R] at this
  have h3 : 3 ∣ Nat.card ↥J := by
    have := hdiv _ hc1
    rwa [Work.A7.orderOf_a7ThreeCycle] at this
  have h5 : 5 ∣ Nat.card ↥J := by
    have := hdiv _ (mul_mem hc1 hc2)
    rwa [orderOf_a7ThreeCycle_mul_c026] at this
  have h7 : 7 ∣ Nat.card ↥J := by
    have := hdiv _ (mul_mem (mul_mem hc1 hc2) hc3)
    rwa [orderOf_a7ThreeCycle_mul_c026_mul_c136] at this
  have h420 : 420 ∣ Nat.card ↥J := by
    have h12 : 12 ∣ Nat.card ↥J :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 4 3) h4 h3
    have h60 : 60 ∣ Nat.card ↥J :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 12 5) h12 h5
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 60 7) h60 h7
  have hmul : J.index * Nat.card ↥J = 2520 := by
    rw [Subgroup.index_mul_card, Work.A7.card_alternatingGroup_seven]
  have hpos : 0 < Nat.card ↥J := Nat.card_pos
  have hle : 420 ≤ Nat.card ↥J := Nat.le_of_dvd hpos h420
  have hidx : J.index ≤ 6 := by
    have h2 : 420 * J.index ≤ 2520 := by
      rw [mul_comm]
      calc J.index * 420 ≤ J.index * Nat.card ↥J := Nat.mul_le_mul_left _ hle
        _ = 2520 := hmul
    have h3 : 420 * J.index ≤ 420 * 6 := by norm_num at h2 ⊢; omega
    exact Nat.le_of_mul_le_mul_left h3 (by norm_num)
  exact A7IndexLeSix J hidx

/-!  ## Part 4: the three model pairs -/

/-- `⟨(4 5 6)⟩` is normal in the centralizer of `(0 1)(2 3)`. -/
theorem normal_c3_a7Invol :
    ((Subgroup.zpowers (Work.A7.a7ThreeCycle)).subgroupOf
      (Subgroup.centralizer ({Work.A7.a7Invol} : Set (alternatingGroup (Fin 7))))).Normal :=
  Work.A7F.normal_K_in_centralizer

/-- `⟨(0 2 6)⟩` is normal in the centralizer of `(1 3)(4 5)`. -/
theorem normal_c3_zB :
    ((Subgroup.zpowers c026).subgroupOf
      (Subgroup.centralizer ({zB} : Set (alternatingGroup (Fin 7))))).Normal := by
  have hb : Work.A7.a7ThreeCycle ∈ Subgroup.centralizer
      ({Work.A7.a7Invol} : Set (alternatingGroup (Fin 7))) :=
    Subgroup.mem_centralizer_singleton_iff.mpr a7Invol_mul_a7ThreeCycle.symm
  have h := conj_normal_zpowers (a := Work.A7.a7Invol) (b := Work.A7.a7ThreeCycle)
    (g := gB) hb normal_c3_a7Invol
  rwa [gB_conj_invol, gB_conj_threeCycle] at h

/-- `⟨(1 3 6)⟩` is normal in the centralizer of `(0 2)(4 5)`. -/
theorem normal_c3_a7S :
    ((Subgroup.zpowers c136).subgroupOf
      (Subgroup.centralizer ({a7S} : Set (alternatingGroup (Fin 7))))).Normal := by
  have hb : Work.A7.a7ThreeCycle ∈ Subgroup.centralizer
      ({Work.A7.a7Invol} : Set (alternatingGroup (Fin 7))) :=
    Subgroup.mem_centralizer_singleton_iff.mpr a7Invol_mul_a7ThreeCycle.symm
  have h := conj_normal_zpowers (a := Work.A7.a7Invol) (b := Work.A7.a7ThreeCycle)
    (g := gC) hb normal_c3_a7Invol
  rwa [gC_conj_invol, gC_conj_threeCycle] at h

/-!  ## Part 5: the key step -/

/-- **An element of odd order centralizing an involution `z ∈ L` centralizes the `3`-element
generating the unique subgroup of order `3` of `C_L(z)`.** -/
theorem centralizes_of_normal_zpowers {Q : Type*} [Group Q] (L : Subgroup Q) [L.Normal]
    [Finite ↥L] {h : Q} (hodd : Odd (orderOf h)) {z x : ↥L}
    (hz : h * (z : Q) * h⁻¹ = (z : Q))
    (hxz : x ∈ Subgroup.centralizer ({z} : Set ↥L))
    (hxord : orderOf x = 3)
    (hcard : Nat.card ↥(Subgroup.centralizer ({z} : Set ↥L)) = 24)
    (hnorm : ((Subgroup.zpowers x).subgroupOf
      (Subgroup.centralizer ({z} : Set ↥L))).Normal) :
    h * (x : Q) * h⁻¹ = (x : Q) := by
  have hyL : h * (x : Q) * h⁻¹ ∈ L :=
    Subgroup.Normal.conj_mem ‹L.Normal› (x : Q) x.2 h
  let y : ↥L := ⟨h * (x : Q) * h⁻¹, hyL⟩
  have hxy : y ∈ Subgroup.centralizer ({z} : Set ↥L) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    show h * (x : Q) * h⁻¹ * (z : Q) = (z : Q) * (h * (x : Q) * h⁻¹)
    have hxzc : (x : Q) * (z : Q) = (z : Q) * (x : Q) :=
      congrArg (fun w : ↥L => (w : Q)) (Subgroup.mem_centralizer_singleton_iff.mp hxz)
    rw [← hz]
    rw [show h * (x : Q) * h⁻¹ * (h * (z : Q) * h⁻¹) = h * ((x : Q) * (z : Q)) * h⁻¹ from
        by group,
      show h * (z : Q) * h⁻¹ * (h * (x : Q) * h⁻¹) = h * ((z : Q) * (x : Q)) * h⁻¹ from
        by group,
      hxzc]
  have hyord : orderOf y = 3 := by
    have h1 : orderOf y = orderOf (h * (x : Q) * h⁻¹) :=
      (orderOf_injective L.subtype Subtype.coe_injective y).symm
    have h2 : orderOf (h * (x : Q) * h⁻¹) = orderOf (x : Q) := by
      have hh := orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective (x : Q)
      simpa [MulAut.conj_apply] using hh
    have h3 : orderOf (x : Q) = orderOf x :=
      orderOf_injective L.subtype Subtype.coe_injective x
    rw [h1, h2, h3, hxord]
  have hzeq : Subgroup.zpowers x = Subgroup.zpowers y :=
    eq_of_card_three_of_normal (Subgroup.zpowers_le.mpr hxz) (Subgroup.zpowers_le.mpr hxy)
      hnorm (by rw [Nat.card_zpowers, hxord]) (by rw [Nat.card_zpowers, hyord]) hcard
  have hymem : y ∈ Subgroup.zpowers x := by rw [hzeq]; exact Subgroup.mem_zpowers y
  have hmemQ : (MulAut.conj h) (x : Q) ∈ Subgroup.zpowers (x : Q) := by
    have h1 : (MulAut.conj h) (x : Q) = (y : Q) := by rw [MulAut.conj_apply]
    rw [h1]
    have h2 : (y : Q) ∈ (Subgroup.zpowers x).map L.subtype :=
      Subgroup.mem_map.mpr ⟨y, hymem, rfl⟩
    rwa [map_zpowers_subtype L x] at h2
  have hconjpow : ∀ n : ℕ, (MulAut.conj h) ^ n = MulAut.conj (h ^ n) := by
    intro n
    induction n with
    | zero =>
      ext w
      simp
    | succ n ih =>
      rw [pow_succ, ih, pow_succ]
      ext w
      show MulAut.conj (h ^ n) (MulAut.conj h w) = MulAut.conj (h ^ n * h) w
      simp only [MulAut.conj_apply]
      group
  have hdiv : orderOf (MulAut.conj h) ∣ orderOf h := by
    rw [orderOf_dvd_iff_pow_eq_one, hconjpow, pow_orderOf_eq_one]
    ext w
    simp
  obtain ⟨k, hk⟩ := hdiv
  have hk' : Odd (orderOf (MulAut.conj h) * k) := by rw [← hk]; exact hodd
  have hoddα : Odd (orderOf (MulAut.conj h)) := (Nat.odd_mul.mp hk').1
  have hxq : orderOf (x : Q) = 3 := by
    have hh := orderOf_injective L.subtype Subtype.coe_injective x
    rw [hxord] at hh
    simpa using hh
  have hfix := mulAut_apply_eq_of_mem_zpowers (MulAut.conj h) hoddα hxq hmemQ
  rwa [MulAut.conj_apply] at hfix

/-!  ## Part 6: the assembly -/

/-- **AUTA7, odd index case: a group `Q` with a normal subgroup `L ≅ A₇`, trivial centralizer
and cyclic-or-dihedral Sylow `2`-subgroups has `L` of odd index only if `L = ⊤`.** -/
theorem OddIndex : Work.GW2.AutA7OddIndexProp := by
  intro Q _ _ L hLnorm hψ hC hdih hoddIndex
  classical
  obtain ⟨ψ⟩ := hψ
  haveI : L.Normal := hLnorm
  haveI : Finite ↥L := Finite.of_injective L.subtype Subtype.coe_injective
  -- ### the model Sylow `2`-subgroup of `A₇` and its preimage in `L`
  have hKcard : Nat.card ↥(dihToA7.range : Subgroup (alternatingGroup (Fin 7))) = 8 := by
    have h := Nat.card_congr (MonoidHom.ofInjective dihToA7_injective).toEquiv
    rw [DihedralGroup.nat_card] at h
    omega
  have hKp : IsPGroup 2 ↥(dihToA7.range : Subgroup (alternatingGroup (Fin 7))) :=
    IsPGroup.of_card (n := 3) (by rw [hKcard]; norm_num)
  have hKidx : (dihToA7.range : Subgroup (alternatingGroup (Fin 7))).index = 315 := by
    have h := Subgroup.index_mul_card (dihToA7.range : Subgroup (alternatingGroup (Fin 7)))
    rw [hKcard, Work.A7.card_alternatingGroup_seven] at h
    omega
  have hKndvd : ¬ 2 ∣ (dihToA7.range : Subgroup (alternatingGroup (Fin 7))).index := by
    rw [hKidx]; norm_num
  let P₀ : Sylow 2 (alternatingGroup (Fin 7)) := hKp.toSylow hKndvd
  have hP₀le : (P₀ : Subgroup (alternatingGroup (Fin 7))) ≤ ψ.toMonoidHom.range := by
    have hrange : ψ.toMonoidHom.range = ⊤ :=
      MonoidHom.range_eq_top.mpr (fun y => ⟨ψ.symm y, by simp⟩)
    rw [hrange]
    exact le_top
  let P : Sylow 2 ↥L := P₀.comapOfInjective ψ.toMonoidHom ψ.injective hP₀le
  let DL : Subgroup ↥L := (P : Subgroup ↥L)
  let DQ : Subgroup Q := DL.map L.subtype
  let N : Subgroup Q := Subgroup.normalizer (DQ : Set Q)
  have hfratt : N ⊔ L = ⊤ := Sylow.normalizer_sup_eq_top P
  -- ### `DQ ≅ D₈`
  have hDLeq : DL = (dihToA7.range : Subgroup (alternatingGroup (Fin 7))).comap ψ.toMonoidHom :=
    Sylow.coe_comapOfInjective P₀ ψ.toMonoidHom ψ.injective _
  have eDL : ↥DL ≃* ↥(dihToA7.range : Subgroup (alternatingGroup (Fin 7))) := by
    refine MulEquiv.ofBijective
      (MonoidHom.mk' (fun x : ↥DL => ⟨ψ x, by
        have hx : (x : ↥L) ∈ (dihToA7.range : Subgroup (alternatingGroup (Fin 7))).comap
            ψ.toMonoidHom := by rw [← hDLeq]; exact x.2
        exact Subgroup.mem_comap.mp hx⟩) ?_)
      ⟨?_, ?_⟩
    · intro a b
      ext
      simp
    · intro a b hab
      exact Subtype.ext (ψ.injective (congrArg Subtype.val hab))
    · intro y
      refine ⟨⟨ψ.symm y, ?_⟩, Subtype.ext (by simp)⟩
      rw [hDLeq, Subgroup.mem_comap]
      simpa using y.2
  have eDQ : ↥DQ ≃* DihedralGroup 4 :=
    (Subgroup.equivMapOfInjective DL L.subtype Subtype.coe_injective).symm.trans
      (eDL.trans (MonoidHom.ofInjective dihToA7_injective).symm)
  -- ### the elements
  set z1 : ↥L := ψ.symm Work.A7.a7Invol with hz1
  set z2 : ↥L := ψ.symm zB with hz2
  set z3 : ↥L := ψ.symm a7S with hz3
  set x1 : ↥L := ψ.symm Work.A7.a7ThreeCycle with hx1
  set x2 : ↥L := ψ.symm c026 with hx2
  set x3 : ↥L := ψ.symm c136 with hx3
  have hψz1 : ψ z1 = Work.A7.a7Invol := by
    simp [hz1]
  have hψz2 : ψ z2 = zB := by
    simp [hz2]
  have hψz3 : ψ z3 = a7S := by
    simp [hz3]
  have hψx1 : ψ x1 = Work.A7.a7ThreeCycle := by
    simp [hx1]
  have hψx2 : ψ x2 = c026 := by
    simp [hx2]
  have hψx3 : ψ x3 = c136 := by
    simp [hx3]
  have hψx1' : ψ.toMonoidHom x1 = Work.A7.a7ThreeCycle := by simpa using hψx1
  have hψx2' : ψ.toMonoidHom x2 = c026 := by simpa using hψx2
  have hψx3' : ψ.toMonoidHom x3 = c136 := by simpa using hψx3
  have hz1DL : z1 ∈ DL := by
    rw [hDLeq, Subgroup.mem_comap]
    simpa [hψz1] using a7Invol_mem_range
  have hz2DL : z2 ∈ DL := by
    rw [hDLeq, Subgroup.mem_comap]
    simpa [hψz2] using zB_mem_range
  have hz3DL : z3 ∈ DL := by
    rw [hDLeq, Subgroup.mem_comap]
    simpa [hψz3] using a7S_mem_range
  have hz1DQ : ((z1 : ↥L) : Q) ∈ DQ := Subgroup.mem_map.mpr ⟨z1, hz1DL, rfl⟩
  have hz2DQ : ((z2 : ↥L) : Q) ∈ DQ := Subgroup.mem_map.mpr ⟨z2, hz2DL, rfl⟩
  have hz3DQ : ((z3 : ↥L) : Q) ∈ DQ := Subgroup.mem_map.mpr ⟨z3, hz3DL, rfl⟩
  -- ### the transported facts
  have hord1 : orderOf x1 = 3 := by
    have h := orderOf_injective ψ.symm.toMonoidHom ψ.symm.injective
      (Work.A7.a7ThreeCycle)
    rw [Work.A7.orderOf_a7ThreeCycle] at h
    simpa [hx1] using h
  have hord2 : orderOf x2 = 3 := by
    have h := orderOf_injective ψ.symm.toMonoidHom ψ.symm.injective
      (c026)
    rw [orderOf_c026] at h
    simpa [hx2] using h
  have hord3 : orderOf x3 = 3 := by
    have h := orderOf_injective ψ.symm.toMonoidHom ψ.symm.injective
      (c136)
    rw [orderOf_c136] at h
    simpa [hx3] using h
  have hcen1 : x1 ∈ Subgroup.centralizer ({z1} : Set ↥L) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply ψ.injective
    simpa [hψx1, hψz1] using a7Invol_mul_a7ThreeCycle.symm
  have hcen2 : x2 ∈ Subgroup.centralizer ({z2} : Set ↥L) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply ψ.injective
    simpa [hψx2, hψz2] using zB_mul_c026.symm
  have hcen3 : x3 ∈ Subgroup.centralizer ({z3} : Set ↥L) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply ψ.injective
    simpa [hψx3, hψz3] using a7S_mul_c136.symm
  have hcard1 : Nat.card ↥(Subgroup.centralizer ({z1} : Set ↥L)) = 24 := by
    have hz1ord : orderOf (ψ z1) = 2 := by simpa [hψz1] using Work.A7.orderOf_a7Invol
    rw [nat_card_centralizer_singleton ψ z1]
    exact Work.A7F.card_centralizer_of_involution _ hz1ord
  have hcard2 : Nat.card ↥(Subgroup.centralizer ({z2} : Set ↥L)) = 24 := by
    rw [nat_card_centralizer_singleton ψ z2, hψz2]
    exact Work.A7F.card_centralizer_of_involution _ (by
      rw [show zB = Work.A7.a7Dswap 1 3 4 5 (by decide) (by decide) from rfl]
      exact orderOf_eq_prime (by decide) (by decide))
  have hcard3 : Nat.card ↥(Subgroup.centralizer ({z3} : Set ↥L)) = 24 := by
    rw [nat_card_centralizer_singleton ψ z3, hψz3]
    exact Work.A7F.card_centralizer_of_involution _ (by
      rw [show a7S = (⟨sylowS, by rw [Equiv.Perm.mem_alternatingGroup, sign_sylowS]⟩ :
        alternatingGroup (Fin 7)) from rfl]
      exact orderOf_eq_prime (by decide) (by decide))
  have hnorm1 : ((Subgroup.zpowers x1).subgroupOf
      (Subgroup.centralizer ({z1} : Set ↥L))).Normal := by
    have := normal_zpowers_centralizer_of_map ψ hcen1
      (show ((Subgroup.zpowers (ψ x1)).subgroupOf
        (Subgroup.centralizer ({ψ z1} : Set (alternatingGroup (Fin 7))))).Normal by
        rw [hψx1, hψz1]; exact normal_c3_a7Invol)
    exact this
  have hnorm2 : ((Subgroup.zpowers x2).subgroupOf
      (Subgroup.centralizer ({z2} : Set ↥L))).Normal := by
    have := normal_zpowers_centralizer_of_map ψ hcen2
      (show ((Subgroup.zpowers (ψ x2)).subgroupOf
        (Subgroup.centralizer ({ψ z2} : Set (alternatingGroup (Fin 7))))).Normal by
        rw [hψx2, hψz2]; exact normal_c3_zB)
    exact this
  have hnorm3 : ((Subgroup.zpowers x3).subgroupOf
      (Subgroup.centralizer ({z3} : Set ↥L))).Normal := by
    have := normal_zpowers_centralizer_of_map ψ hcen3
      (show ((Subgroup.zpowers (ψ x3)).subgroupOf
        (Subgroup.centralizer ({ψ z3} : Set (alternatingGroup (Fin 7))))).Normal by
        rw [hψx3, hψz3]; exact normal_c3_a7S)
    exact this
  -- ### the main claim
  have hmain : ∀ h : Q, h ∈ N → Odd (orderOf h) → h = 1 := by
    intro h hh hodd
    have hcent : ∀ d : Q, d ∈ DQ → h * d * h⁻¹ = d :=
      OddOrderNormalizerCentralizes eDQ hh hodd
    have hx1c := centralizes_of_normal_zpowers L hodd (hcent _ hz1DQ) hcen1 hord1 hcard1 hnorm1
    have hx2c := centralizes_of_normal_zpowers L hodd (hcent _ hz2DQ) hcen2 hord2 hcard2 hnorm2
    have hx3c := centralizes_of_normal_zpowers L hodd (hcent _ hz3DQ) hcen3 hord3 hcard3 hnorm3
    -- the subgroup generated by `DL` and the `xᵢ` is all of `L`
    have hjoin : Subgroup.closure ((DL : Set ↥L) ∪ ({x1, x2, x3} : Set ↥L)) = ⊤ := by
      apply Subgroup.map_injective (f := ψ.toMonoidHom)
      exact fun a b h => ψ.injective h
      rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective ψ.toMonoidHom ψ.surjective]
      have himg : ψ.toMonoidHom '' ((DL : Set ↥L) ∪ ({x1, x2, x3} : Set ↥L)) =
          (dihToA7.range : Set (alternatingGroup (Fin 7))) ∪
            ({Work.A7.a7ThreeCycle, c026, c136} : Set (alternatingGroup (Fin 7))) := by
        ext y
        constructor
        · rintro ⟨w, hw, rfl⟩
          rcases hw with hw | hw | hw | hw
          · left
            rw [hDLeq] at hw
            exact Subgroup.mem_comap.mp hw
          · rw [hw]
            exact Or.inr (Or.inl (by simpa using hψx1'))
          · rw [hw]
            exact Or.inr (Or.inr (Or.inl (by simpa using hψx2')))
          · rw [hw]
            exact Or.inr (Or.inr (Or.inr (by simpa using hψx3')))
        · intro hy
          rcases hy with hy | hy
          · refine ⟨ψ.symm y, Or.inl ?_, by simp⟩
            rw [hDLeq]
            exact Subgroup.mem_comap.mpr (by simpa using hy)
          · rcases hy with hy | hy | hy
            · refine ⟨x1, Or.inr (Or.inl rfl), ?_⟩
              simpa [hψx1] using hy.symm
            · refine ⟨x2, Or.inr (Or.inr (Or.inl rfl)), ?_⟩
              simpa [hψx2] using hy.symm
            · refine ⟨x3, Or.inr (Or.inr (Or.inr rfl)), ?_⟩
              simpa [hψx3] using hy.symm
      rw [himg]
      refine le_antisymm le_top ?_
      rw [← a7SylowJoinTop]
      apply Subgroup.closure_mono
      intro y hy
      rcases hy with rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (MonoidHom.mem_range.mpr ⟨DihedralGroup.r 1, a7R_eq_dihToA7⟩)
      · exact Or.inl (MonoidHom.mem_range.mpr ⟨DihedralGroup.sr 0, a7S_eq_dihToA7⟩)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
    -- `h` centralizes `L`
    have hC' : (⊤ : Subgroup ↥L) ≤ (Subgroup.centralizer ({h} : Set Q)).comap L.subtype := by
      rw [← hjoin]
      refine (Subgroup.closure_le _).mpr ?_
      intro y hy
      change L.subtype y ∈ Subgroup.centralizer ({h} : Set Q)
      rw [Subgroup.mem_centralizer_singleton_iff]
      rcases hy with hy | rfl | rfl | rfl
      · have h2 : h * (y : Q) * h⁻¹ = (y : Q) :=
          hcent (y : Q) (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
        calc (y : Q) * h = (h * (y : Q) * h⁻¹) * h := by rw [h2]
          _ = h * (y : Q) := by group
      · have h2 : h * ((x1 : ↥L) : Q) * h⁻¹ = ((x1 : ↥L) : Q) := hx1c
        calc ((x1 : ↥L) : Q) * h = (h * ((x1 : ↥L) : Q) * h⁻¹) * h := by rw [h2]
          _ = h * ((x1 : ↥L) : Q) := by group
      · have h2 : h * ((x2 : ↥L) : Q) * h⁻¹ = ((x2 : ↥L) : Q) := hx2c
        calc ((x2 : ↥L) : Q) * h = (h * ((x2 : ↥L) : Q) * h⁻¹) * h := by rw [h2]
          _ = h * ((x2 : ↥L) : Q) := by group
      · have h2 : h * ((x3 : ↥L) : Q) * h⁻¹ = ((x3 : ↥L) : Q) := hx3c
        calc ((x3 : ↥L) : Q) * h = (h * ((x3 : ↥L) : Q) * h⁻¹) * h := by rw [h2]
          _ = h * ((x3 : ↥L) : Q) := by group
    have hmem : h ∈ Subgroup.centralizer (L : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hh := hC' (show (⟨l, hl⟩ : ↥L) ∈ ⊤ from trivial)
      change L.subtype ⟨l, hl⟩ ∈ Subgroup.centralizer ({h} : Set Q) at hh
      rw [Subgroup.mem_centralizer_singleton_iff] at hh
      exact hh
    rw [hC] at hmem
    simpa using hmem
  -- ### `N ≤ L`
  have hNL : N ≤ L := by
    intro n hn
    obtain ⟨k, hk⟩ := exists_eq_two_pow_of_odd_eq_one
      (fun y hy => Subtype.ext (hmain (y : Q) y.2 (by simpa using hy))) (⟨n, hn⟩ : ↥N)
    have h1 : orderOf ((QuotientGroup.mk' L) n) ∣ 2 ^ k := by
      rw [← hk]
      have hh : orderOf ((QuotientGroup.mk' L) n) ∣ orderOf (⟨n, hn⟩ : ↥N) :=
        orderOf_map_dvd ((QuotientGroup.mk' L).comp N.subtype) (⟨n, hn⟩ : ↥N)
      simpa using hh
    have h2 : orderOf ((QuotientGroup.mk' L) n) ∣ L.index := by
      rw [Subgroup.index_eq_card, ← Nat.card_zpowers ((QuotientGroup.mk' L) n)]
      exact Subgroup.card_subgroup_dvd_card (Subgroup.zpowers _)
    have hcop : Nat.Coprime (2 ^ k) L.index :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hoddIndex)
    have h3 : orderOf ((QuotientGroup.mk' L) n) ∣ 1 := by
      have hh := Nat.dvd_gcd h1 h2
      rwa [hcop] at hh
    have h4 : orderOf ((QuotientGroup.mk' L) n) = 1 := Nat.eq_one_of_dvd_one h3
    have h5 : (QuotientGroup.mk' L) n = 1 := orderOf_eq_one_iff.mp h4
    rw [← QuotientGroup.ker_mk' L]
    exact (MonoidHom.mem_ker).mpr h5
  -- ### conclusion
  have hfratt' : L ⊔ N = ⊤ := by rw [sup_comm]; exact hfratt
  exact top_le_iff.mp (hfratt' ▸ sup_le le_rfl hNL)

end Work.AUTA7.A7
