import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE3.CosetInvCountBasic
import Submission.Work.CORE3.NormalizerPcoreEqHhat
import Submission.Work.CORE3.SylowDihedral
import Submission.Work.CORE3.Case1bFive
import Submission.Work.CORE3.OutsideS0OrderTwo
import Submission.Work.ASM.CyclicSylow

set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Work.CORE3

open Work.GW2


/-- In a group of cardinality `2`, all elements commute (local copy, kept independent of the
other CORE3 leaf files). -/
theorem commute_of_card_two' {G : Type*} [Group G] (hcard : Nat.card G = 2) (a b : G) :
    a * b = b * a := by
  have h2 : ∀ c : G, c * c = 1 := by
    intro c
    have hdvd : orderOf c ∣ 2 := by
      simpa [hcard] using orderOf_dvd_natCard c
    have h3 : c ^ orderOf c = 1 := pow_orderOf_eq_one c
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · rw [h1, pow_one] at h3
      rw [h3, one_mul]
    · rw [h1] at h3
      simpa [pow_two] using h3
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right (h2 (a * b))).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by
          rw [inv_eq_of_mul_eq_one_right (h2 b), inv_eq_of_mul_eq_one_right (h2 a)]

/-- An element of odd order cannot invert a nontrivial element of odd order (local copy). -/
theorem eq_one_of_conj_eq_inv_of_odd' {G : Type*} [Group G] {g a : G}
    (hg : Odd (orderOf g)) (h : g * a * g⁻¹ = a⁻¹) (ha : Odd (orderOf a)) : a = 1 := by
  have hstep : ∀ i : ℕ, g ^ (2 * i + 1) * a * (g ^ (2 * i + 1))⁻¹ = a⁻¹ := by
    intro i
    induction i with
    | zero => simpa using h
    | succ j ih =>
      have h2 : g ^ 2 * a * (g ^ 2)⁻¹ = a := by
        have h1 : g ^ 2 * a * (g ^ 2)⁻¹ = g * (g * a * g⁻¹) * g⁻¹ := by
          rw [pow_two, mul_inv_rev]; group
        rw [h1, h]
        have h3 : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
        rw [h3, h, inv_inv]
      have h4 : 2 * (j + 1) + 1 = 2 * j + 1 + 2 := by ring
      rw [h4, pow_add]
      have h5 : g ^ (2 * j + 1) * g ^ 2 * a * (g ^ (2 * j + 1) * g ^ 2)⁻¹
          = g ^ (2 * j + 1) * (g ^ 2 * a * (g ^ 2)⁻¹) * (g ^ (2 * j + 1))⁻¹ := by
        rw [mul_inv_rev]; group
      rw [h5, h2, ih]
  obtain ⟨k, hk⟩ := hg
  have hgk : g ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one g
  have haeq : a = a⁻¹ := by
    have h1 := hstep k
    rw [hgk] at h1
    simpa using h1
  have ha2 : a ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [haeq]
    exact mul_inv_cancel a
  have hdvd : orderOf a ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr ha2
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · exact absurd (h1 ▸ ha) (by decide)

/-- Pure group identity: if `y` is an involution inverting `x` and `v` commutes with `x`,
then `x` centralizes `y * v * y⁻¹`. -/
lemma conj_inv_centralizes {G : Type*} [Group G] {x y v : G}
    (hy : y * y = 1) (hxy : y * x * y⁻¹ = x⁻¹) (hvx : x * v = v * x) :
    x * (y * v * y⁻¹) * x⁻¹ = y * v * y⁻¹ := by
  have hxy' : x * y = y * x⁻¹ := by
    have h1 : y * x = x⁻¹ * y := by
      have := congrArg (fun t => t * y) hxy
      simpa [mul_assoc, hy] using this
    have h2 : x * y * x = y := by
      have := congrArg (fun t => x * t) h1
      simpa [mul_assoc] using this
    calc x * y = x * y * x * x⁻¹ := by group
      _ = y * x⁻¹ := by rw [h2]
  have hxv : x⁻¹ * v * x = v := by
    rw [mul_assoc, ← hvx, ← mul_assoc, inv_mul_cancel, one_mul]
  calc x * (y * v * y⁻¹) * x⁻¹
      = (x * y) * v * (x * y)⁻¹ := by group
    _ = (y * x⁻¹) * v * (y * x⁻¹)⁻¹ := by rw [hxy']
    _ = y * (x⁻¹ * v * x) * y⁻¹ := by group
    _ = y * v * y⁻¹ := by rw [hxv]

/-- If `y` is an involution inverting `x`, then `y` normalizes `⟨x⟩`. -/
lemma mem_normalizer_zpowers_of_inverts {G : Type*} [Group G] {x y : G}
    (hy1 : y * y = 1) (hxy : y * x * y⁻¹ = x⁻¹) :
    y ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
  have hconjx : (MulAut.conj y) x = x⁻¹ := by rw [MulAut.conj_apply]; exact hxy
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy1
  have hconjy : (MulAut.conj y⁻¹) x = x⁻¹ := by
    rw [show y⁻¹ = y from hyinv]
    exact hconjx
  rw [Subgroup.mem_normalizer_iff]
  intro w
  rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨-j, ?_⟩
    have hh : y * x ^ j * y⁻¹ = (x ^ j)⁻¹ := by
      calc y * x ^ j * y⁻¹ = (MulAut.conj y) (x ^ j) := by rw [MulAut.conj_apply]
        _ = ((MulAut.conj y) x) ^ j := map_zpow _ _ _
        _ = (x⁻¹) ^ j := by rw [hconjx]
        _ = (x ^ j)⁻¹ := inv_zpow x j
    rw [hh]; exact zpow_neg x j
  · rintro ⟨j, hj⟩
    refine ⟨-j, ?_⟩
    have hw : w = y⁻¹ * x ^ j * y := by rw [hj]; group
    rw [hw]
    have hh : y⁻¹ * x ^ j * y = (x ^ j)⁻¹ := by
      calc y⁻¹ * x ^ j * y = (MulAut.conj y⁻¹) (x ^ j) := by rw [MulAut.conj_apply, inv_inv]
        _ = ((MulAut.conj y⁻¹) x) ^ j := map_zpow _ _ _
        _ = (x⁻¹) ^ j := by rw [hconjy]
        _ = (x ^ j)⁻¹ := inv_zpow x j
    rw [hh]; exact zpow_neg x j

/-- **Bender 1981 §3, p. 223 (Claim A):** `C_G(v) ≤ Ĥ` for every `1 ≠ v ∈ O₂(Ĥ)`.
(Reproduced here from `Work.CORE3`'s leaf file, where it sits under a deeper namespace.) -/
theorem claimA (G : Type) [Group G] [Finite G]
    (h : BenderCtx G) (B : BenderSetup G) (hfus : InvolutionFusionProp)
    (h26 : Thm26Concl B) (h4 : IsFourGroup (pCoreIn 2 B.Hhat)) {v : G}
    (hv : v ∈ pCoreIn 2 B.Hhat) (hv1 : v ≠ 1) :
    Subgroup.centralizer ({v} : Set G) ≤ B.Hhat := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup G := h.simple
  have htV : B.t ∈ pCoreIn 2 B.Hhat := by
    rw [← Work.CORE2A.thm26Concl_centralizer_eq h26, Subgroup.mem_inf]
    refine ⟨Work.CORE2A.bSetup_t_mem_S B, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr (fun u hu =>
      ((Subgroup.mem_centralizer_iff.mp (Work.CORE2A.bSetup_U_le_H B hu)) B.t
        (by simp)).symm)
  have hno2 : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
    intro N hN h2
    haveI := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hb | ht
    · have hcard : Nat.card G = 2 := by
        rw [← Subgroup.index_bot, ← hb]; exact h2
      obtain ⟨a, b, hab⟩ := h.nonab
      exact hab (commute_of_card_two' hcard a b)
    · rw [ht, Subgroup.index_top] at h2
      exact absurd h2 (by norm_num)
  obtain ⟨n, hn2, hdih⟩ := _root_.Work.CORE3.SylowDihedral G h B
  obtain ⟨g, hg, hgt⟩ := (hfus G B.S n hn2 hdih hno2).2 (pCoreIn 2 B.Hhat) h4 B.t htV v hv
    (Work.CORE2A.bSetup_t_ne_one B) hv1
  rw [_root_.Work.CORE3.NormalizerPcoreEqHhat G h B h4] at hg
  intro c hc
  have hvc : v * c = c * v := (Subgroup.mem_centralizer_iff.mp hc) v (by simp)
  have hd : g⁻¹ * c * g ∈ B.H := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have h1 : B.t * (g⁻¹ * c * g) = g⁻¹ * (v * c) * g := by rw [← hgt]; group
    have h2 : (g⁻¹ * c * g) * B.t = g⁻¹ * (c * v) * g := by rw [← hgt]; group
    rw [h1, h2, hvc]
  have hdH : g⁻¹ * c * g ∈ B.Hhat := B.H_le_Hhat hd
  have hce : c = g * (g⁻¹ * c * g) * g⁻¹ := by group
  rw [hce]
  exact B.Hhat.mul_mem (B.Hhat.mul_mem hg hdH) (B.Hhat.inv_mem hg)

lemma pow_factorization_dvd (n : ℕ) (hn0 : n ≠ 0) (f : ℕ) (hf : f = n.factorization 2) :
    (2:ℕ) ^ f ∣ n := by
  rw [← Nat.factorization_le_iff_dvd (by positivity : (2:ℕ)^f ≠ 0) hn0]
  intro p
  rw [Nat.factorization_pow, hf]
  rw [Finsupp.smul_apply, smul_eq_mul]
  by_cases hp : p = 2
  · subst hp
    rw [Nat.prime_two.factorization]
    rw [Finsupp.single_eq_same, mul_one]
  · rw [Nat.prime_two.factorization]
    rw [Finsupp.single_eq_of_ne (by omega : p ≠ 2), mul_zero]
    exact Nat.zero_le _

lemma odd_div_pow_factorization (n : ℕ) (hn0 : n ≠ 0) (f : ℕ) (hf : f = n.factorization 2)
    (m : ℕ) (hm : m = n / 2 ^ f) : Odd m := by
  have h2f : (2:ℕ) ^ f ∣ n := pow_factorization_dvd n hn0 f hf
  have hmpos : 0 < m := by
    rw [hm]
    exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) h2f) (by positivity)
  rw [← Nat.not_even_iff_odd]
  intro hev
  have hm2 : 2 ∣ m := by rwa [even_iff_two_dvd] at hev
  have hfac : n.factorization = ((2:ℕ)^f).factorization + m.factorization := by
    have h1 : n = 2^f * m := by rw [hm]; exact (Nat.mul_div_cancel' h2f).symm
    rw [h1]
    exact Nat.factorization_mul (by positivity) hmpos.ne'
  have h2 : n.factorization 2 = ((2:ℕ)^f).factorization 2 + m.factorization 2 := by
    rw [hfac]; rfl
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, Nat.prime_two.factorization,
    Finsupp.single_eq_same, mul_one] at h2
  have hm2fac : m.factorization 2 ≠ 0 := by
    intro h0
    rw [Nat.factorization_eq_zero_iff] at h0
    rcases h0 with h | h | h
    · exact h Nat.prime_two
    · exact h hm2
    · exact absurd h hmpos.ne'
  omega

lemma pow_conj_eq_inv_of_odd {G : Type*} [Group G] {x k : G} (hkx : k * x * k⁻¹ = x⁻¹)
    {m : ℕ} (hm : Odd m) : k ^ m * x * (k ^ m)⁻¹ = x⁻¹ := by
  obtain ⟨j, rfl⟩ := hm
  have hki2 : (k ^ 2)⁻¹ = k⁻¹ * k⁻¹ := by rw [pow_two, mul_inv_rev]
  have h2 : k ^ 2 * x * (k ^ 2)⁻¹ = x := by
    rw [hki2, pow_two]
    calc k * k * x * (k⁻¹ * k⁻¹) = k * (k * x * k⁻¹) * k⁻¹ := by group
      _ = k * x⁻¹ * k⁻¹ := by rw [hkx]
      _ = (k * x * k⁻¹)⁻¹ := by group
      _ = x := by rw [hkx, inv_inv]
  have h2' : k ^ 2 * x⁻¹ * (k ^ 2)⁻¹ = x⁻¹ := by
    have := congrArg Inv.inv h2
    simpa [mul_assoc, mul_inv_rev, inv_inv] using this
  induction j with
  | zero => simpa using hkx
  | succ j ih =>
      calc k ^ (2 * (j + 1) + 1) * x * (k ^ (2 * (j + 1) + 1))⁻¹
          = k ^ 2 * (k ^ (2 * j + 1) * x * (k ^ (2 * j + 1))⁻¹) * (k ^ 2)⁻¹ := by
            rw [show 2 * (j + 1) + 1 = 2 + (2 * j + 1) by ring, pow_add]; group
        _ = k ^ 2 * x⁻¹ * (k ^ 2)⁻¹ := by rw [ih]
        _ = x⁻¹ := h2'

lemma sq_mem_pCoreIn_of_mem_Hhat {G : Type} [Group G] [Finite G] (I : Case1Inputs)
    (h : BenderCtx G) (B : BenderSetup G) (h1 : Case1 B) (D : Case1bData B) {p : G}
    (hp : p ∈ B.Hhat) (hord : ∃ k, orderOf p = 2 ^ k) : p ^ 2 ∈ pCoreIn 2 B.Hhat := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVle : pCoreIn 2 B.Hhat ≤ B.Hhat := Work.CORE2A.thm26Concl_O2_le_Hhat (I.h26 G I.T.ft h B)
  have hVnorm : B.Hhat ≤ Subgroup.normalizer ((pCoreIn 2 B.Hhat : Subgroup G) : Set G) :=
    _root_.Work.CORE3.le_normalizer_map_subtype B.Hhat (Work.GW2.pCore 2 ↥B.Hhat)
  set VH : Subgroup ↥B.Hhat := (pCoreIn 2 B.Hhat).subgroupOf B.Hhat with hVHdef
  have hVHcard : Nat.card ↥VH = 4 := by
    rw [hVHdef]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVle).toEquiv]
    exact D.four.1
  have hVHpg : IsPGroup 2 ↥VH := by
    rw [IsPGroup.iff_card]; exact ⟨2, by rw [hVHcard]; norm_num⟩
  have hVHnormal : VH.Normal := by
    rw [hVHdef]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hVle).mpr hVnorm
  let pH : ↥B.Hhat := ⟨p, hp⟩
  have hpHpg : IsPGroup 2 ↥(Subgroup.zpowers pH) := by
    obtain ⟨c, hc⟩ := hord
    exact IsPGroup.of_card (p := 2) (n := c) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk]; exact hc)
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hpHpg
  have hVHQ : VH ≤ (Q : Subgroup ↥B.Hhat) := IsPGroup.le_sylow_of_normal hVHpg Q
  have hpHQ : pH ∈ (Q : Subgroup ↥B.Hhat) := hQ (Subgroup.mem_zpowers pH)
  have hSle : (B.S : Subgroup G) ≤ B.Hhat := Work.CORE2A.bSetup_S_le_Hhat B
  have hQcard : Nat.card ↥(Q : Subgroup ↥B.Hhat) = 8 := by
    rw [Sylow.card_eq_multiplicity Q, ← Sylow.card_eq_multiplicity ((B.S).subtype hSle),
      Sylow.coe_subtype]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSle).toEquiv, D.S8]
  have hidx : VH.relIndex (Q : Subgroup ↥B.Hhat) = 2 := by
    have h1 := Subgroup.relIndex_mul_card VH (Q : Subgroup ↥B.Hhat)
    rw [inf_eq_left.mpr hVHQ, hVHcard, hQcard] at h1
    omega
  have hpHsqVH : pH ^ 2 ∈ VH := by
    haveI : (VH.subgroupOf (Q : Subgroup ↥B.Hhat)).Normal := hVHnormal.subgroupOf _
    have hcard2 : Nat.card (↥(Q : Subgroup ↥B.Hhat) ⧸ VH.subgroupOf (Q : Subgroup ↥B.Hhat)) = 2 := by
      rw [← Subgroup.index_eq_card]
      exact hidx
    have hg2 : (QuotientGroup.mk' (VH.subgroupOf (Q : Subgroup ↥B.Hhat))
        (⟨pH, hpHQ⟩ : ↥(Q : Subgroup ↥B.Hhat))) ^ 2 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one]
      exact (orderOf_dvd_natCard _).trans (by rw [hcard2])
    have hmap : ((⟨pH, hpHQ⟩ : ↥(Q : Subgroup ↥B.Hhat)) ^ 2 : ↥(Q : Subgroup ↥B.Hhat)) ∈ VH.subgroupOf (Q : Subgroup ↥B.Hhat) := by
      rw [← QuotientGroup.eq_one_iff]
      change QuotientGroup.mk' (VH.subgroupOf (Q : Subgroup ↥B.Hhat))
        ((⟨pH, hpHQ⟩ : ↥(Q : Subgroup ↥B.Hhat)) ^ 2) = 1
      rw [map_pow]
      exact hg2
    rw [Subgroup.mem_subgroupOf] at hmap
    simpa using hmap
  have h1 : ((pH : ↥B.Hhat) ^ 2 : ↥B.Hhat) ∈ VH := hpHsqVH
  rw [hVHdef, Subgroup.mem_subgroupOf] at h1
  have h2 : ((↑((pH : ↥B.Hhat) ^ 2)) : G) = p ^ 2 := by
    rw [Subgroup.coe_pow]
  rwa [h2] at h1


lemma four_group_third {G : Type*} [Group G] [Finite G] {V : Subgroup G} (hV : Work.GW2.IsFourGroup V)
    {a b w : G}
    (ha : a ∈ V) (hb : b ∈ V) (hw : w ∈ V) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hw1 : w ≠ 1)
    (hab : a ≠ b) (hwa : w ≠ a) (hwb : w ≠ b) : w = a * b := by
  have ha2 : a * a = 1 := by rw [← pow_two]; exact hV.2 a ha
  have hb2 : b * b = 1 := by rw [← pow_two]; exact hV.2 b hb
  have hVc : (V : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]; exact hV.1
  have h4c : ({1, w, a, b} : Set G).ncard = 4 := by
    have h1 : (1 : G) ∉ ({w, a, b} : Set G) := by
      intro hmem
      rcases (Set.mem_insert_iff.mp hmem) with h | h
      · exact hw1 h.symm
      · rcases (Set.mem_insert_iff.mp h) with h | h
        · exact ha1 h.symm
        · exact hb1 (Set.mem_singleton_iff.mp h).symm
    have h2 : w ∉ ({a, b} : Set G) := by
      intro hmem
      rcases (Set.mem_insert_iff.mp hmem) with h | h
      · exact hwa h
      · exact hwb (Set.mem_singleton_iff.mp h)
    have h3 : a ∉ ({b} : Set G) := by
      intro hmem; exact hab (Set.mem_singleton_iff.mp hmem)
    rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
      Set.ncard_insert_of_notMem h3, Set.ncard_singleton]
  haveI : Finite (V : Set G) := inferInstanceAs (Finite ↥V)
  have hsub : ({1, w, a, b} : Set G) ⊆ V := by
    intro x hx
    rcases (Set.mem_insert_iff.mp hx) with h | h
    · rw [h]; exact V.one_mem
    · rcases (Set.mem_insert_iff.mp h) with h | h
      · rw [h]; exact hw
      · rcases (Set.mem_insert_iff.mp h) with h | h
        · rw [h]; exact ha
        · rw [Set.mem_singleton_iff.mp h]; exact hb
  have hVeq : V = ({1, w, a, b} : Set G) :=
    (Set.eq_of_subset_of_ncard_le (s := ({1, w, a, b} : Set G)) (t := (V : Set G)) hsub
      (by rw [hVc, h4c])).symm
  have hab1 : a * b ≠ 1 := by
    intro h
    exact hab (mul_left_cancel (show a * b = a * a from by rw [h, ha2])).symm
  have haba : a * b ≠ a := by
    intro h
    exact hb1 (mul_left_cancel (show a * b = a * 1 from by rw [h, mul_one]))
  have habb : a * b ≠ b := by
    intro h
    exact ha1 (mul_right_cancel (show a * b = 1 * b from by rw [h, one_mul]))
  have hmem : a * b ∈ ({1, w, a, b} : Set G) := by
    rw [← hVeq]
    exact V.mul_mem ha hb
  rcases (Set.mem_insert_iff.mp hmem) with h | h
  · exact absurd h hab1
  · rcases (Set.mem_insert_iff.mp h) with h | h
    · exact h.symm
    · rcases (Set.mem_insert_iff.mp h) with h | h
      · exact absurd h haba
      · exact absurd (Set.mem_singleton_iff.mp h) habb


/-- Crux: if `x ∈ U \ {1}` is inverted by an involution `y ∉ Ĥ`, then some element of `Ĥ`
also inverts `x`. -/
theorem exists_hhat_conj_inv (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (h : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) {x y : G} (hxU : x ∈ B.U) (hx1 : x ≠ 1)
    (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat) (hxy : y * x * y⁻¹ = x⁻¹) :
    ∃ z ∈ B.Hhat, z * x * z⁻¹ = x⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h26 : Thm26Concl B := I.h26 G I.T.ft h B
  have hV2 : IsPGroup 2 (pCoreIn 2 B.Hhat) := Work.CORE2A.thm26Concl_isPGroup_O2 h26
  have hVcU : pCoreIn 2 B.Hhat ≤ Subgroup.centralizer (B.U : Set G) := by
    rw [← Work.CORE2A.thm26Concl_centralizer_eq h26]; exact inf_le_right
  have hNV : Subgroup.normalizer ((pCoreIn 2 B.Hhat : Subgroup G) : Set G) = B.Hhat :=
    _root_.Work.CORE3.NormalizerPcoreEqHhat G h B D.four
  -- `V ≤ C_G(x)`, since `V ≤ C_G(U) ∋ x`
  have hVcx : pCoreIn 2 B.Hhat ≤ Subgroup.centralizer ({x} : Set G) :=
    le_trans hVcU (Subgroup.centralizer_le (by
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]; exact hxU))
  -- `y` normalizes `C_G(x)` (it inverts `x`)
  have hyC : Work.GW2.conjSub y (Subgroup.centralizer ({x} : Set G)) ≤
      Subgroup.centralizer ({x} : Set G) :=
    Work.CORE3.map_conj_le_centralizer_of_conj_eq_inv hxy le_rfl
  -- `V` is a Sylow 2-subgroup of `C_G(x)` (Bender's first step)
  have hodd : Odd ((pCoreIn 2 B.Hhat).relIndex
      (Subgroup.centralizer ({x} : Set G))) :=
    Work.CORE3.odd_relIndex_centralizer_of_mem_U I G h B h1 D hxU hx1 hy2 hyH hxy
  -- Sylow conjugacy inside the `y`-invariant `C_G(x)`: `yVy⁻¹ = c⁻¹ V c`
  obtain ⟨c, hc, hconj⟩ :=
    Work.CORE3.sylow_conj_of_odd_relIndex hVcx hyC hV2 hodd
  have hcx : c * x * c⁻¹ = x := by
    have hcomm : x * c = c * x := (Subgroup.mem_centralizer_iff.mp hc) x (by simp)
    rw [← hcomm]; group
  -- `z := c * y` lies in `N_G(V) = Ĥ` and inverts `x`
  refine ⟨c * y, ?_, ?_⟩
  · rw [← hNV, Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have h1' : y * z * y⁻¹ ∈ Work.GW2.conjSub y (pCoreIn 2 B.Hhat) := by
        rw [Work.CORE2A.mem_conjSub_iff]
        have h4 : y⁻¹ * (y * z * y⁻¹) * y = z := by group
        rw [h4]; exact hz
      have h2' : c * (y * z * y⁻¹) * c⁻¹ ∈ pCoreIn 2 B.Hhat := (hconj _).mp h1'
      have h3' : (c * y) * z * (c * y)⁻¹ = c * (y * z * y⁻¹) * c⁻¹ := by group
      rw [h3']; exact h2'
    · intro hz
      have h2' : c * (y * z * y⁻¹) * c⁻¹ ∈ pCoreIn 2 B.Hhat := by
        have h3' : c * (y * z * y⁻¹) * c⁻¹ = (c * y) * z * (c * y)⁻¹ := by group
        rw [h3']; exact hz
      have h1' : y * z * y⁻¹ ∈ Work.GW2.conjSub y (pCoreIn 2 B.Hhat) := (hconj _).mpr h2'
      rw [Work.CORE2A.mem_conjSub_iff] at h1'
      have h4 : y⁻¹ * (y * z * y⁻¹) * y = z := by group
      rwa [h4] at h1'
  · have hcxinv : c * x⁻¹ * c⁻¹ = x⁻¹ := by
      have h' := congrArg Inv.inv hcx
      simpa [mul_assoc] using h'
    have h3' : (c * y) * x * (c * y)⁻¹ = c * (y * x * y⁻¹) * c⁻¹ := by group
    rw [h3', hxy, hcxinv]

/-- An element `p ∈ Ĥ` of order `4` whose square lies in `O₂(Ĥ)` yields an involution
`s ∈ Ĥ \ O₂(Ĥ)` inverting `x`, whenever `p` inverts `x ∈ U`. -/
lemma exists_involution_of_orderOf_four {G : Type} [Group G] [Finite G] (I : Case1Inputs)
    (h : BenderCtx G) (B : BenderSetup G) (h1 : Case1 B) (D : Case1bData B) {p x : G}
    (hp : p ∈ B.Hhat) (hord : orderOf p = 4) (hp2V : p ^ 2 ∈ pCoreIn 2 B.Hhat)
    (hxU : x ∈ B.U) (hx1 : x ≠ 1) (hpc : p * x * p⁻¹ = x⁻¹) :
    ∃ s ∈ B.Hhat, orderOf s = 2 ∧ s ∉ pCoreIn 2 B.Hhat ∧ s * x * s⁻¹ = x⁻¹ :=
  Work.CORE3.InvolutionInvertingMemU I G h B h1 D hxU hx1 hp hpc

/-- If `x ∈ U \ {1}` is inverted by some element of `Ĥ`, then `x` lies in the Fitting
subgroup of `U`. -/
theorem fittingIn_of_mem_invSet_Hhat (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (h : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) {x : G} (hxU : x ∈ B.U) (hx1 : x ≠ 1)
    (hxin : ∃ k ∈ B.Hhat, k * x * k⁻¹ = x⁻¹) :
    x ∈ Work.GW2.fittingIn B.U := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hkH, hkx⟩ := hxin
  have h26 : Thm26Concl B := I.h26 G I.T.ft h B
  have hUodd : Odd (Nat.card B.U) := Work.CORE2A.bSetup_U_odd B
  have hxodd : Odd (orderOf x) := Odd.of_dvd_nat hUodd (Subgroup.orderOf_dvd_natCard B.U hxU)
  have hxne : x ≠ x⁻¹ := by
    intro hxx
    have hx2 : x ^ 2 = 1 := by rw [pow_two]; exact eq_inv_iff_mul_eq_one.mp hxx
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx2
    have h1 : orderOf x = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
      · exact h1
      · exact absurd (h1 ▸ hxodd) (by decide)
    exact hx1 (orderOf_eq_one_iff.mp h1)
  have hkeven : Even (orderOf k) := by
    by_contra hc
    rw [Nat.not_even_iff_odd] at hc
    exact hx1 (eq_one_of_conj_eq_inv_of_odd' hc hkx hxodd)
  set n := orderOf k with hn
  have hn0 : n ≠ 0 := (orderOf_pos k).ne'
  set f := n.factorization 2 with hf
  set m := n / 2 ^ f with hm
  have h2f : (2 : ℕ) ^ f ∣ n := pow_factorization_dvd n hn0 f hf
  have hmpos : 0 < m := by
    rw [hm]
    exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) h2f) (by positivity)
  have hmul : 2 ^ f * m = n := by rw [hm]; exact Nat.mul_div_cancel' h2f
  have hmn : m ∣ n := ⟨2 ^ f, by rw [mul_comm]; exact hmul.symm⟩
  have hmodd : Odd m := odd_div_pow_factorization n hn0 f hf m hm
  have hporder : orderOf (k ^ m) = 2 ^ f := by
    rw [orderOf_pow, Nat.gcd_eq_right hmn, ← hn, hmul.symm, Nat.mul_div_left _ hmpos]
  have hpc : k ^ m * x * (k ^ m)⁻¹ = x⁻¹ := pow_conj_eq_inv_of_odd hkx hmodd
  have hpH : k ^ m ∈ B.Hhat := B.Hhat.pow_mem hkH m
  have hp2V : (k ^ m) ^ 2 ∈ pCoreIn 2 B.Hhat :=
    sq_mem_pCoreIn_of_mem_Hhat I h B h1 D hpH ⟨f, hporder⟩
  have hp4 : (k ^ m) ^ 4 = 1 := by
    have h1 : ((k ^ m) ^ 2) ^ 2 = 1 := D.four.2 _ hp2V
    rwa [← pow_mul, show 2 * 2 = 4 from rfl] at h1
  have hVcentU : pCoreIn 2 B.Hhat ≤ Subgroup.centralizer (B.U : Set G) := by
    rw [← Work.CORE2A.thm26Concl_centralizer_eq h26]; exact inf_le_right
  have hpne1 : k ^ m ≠ 1 := by
    intro h0
    rw [h0, one_mul, inv_one] at hpc
    exact hxne (by simpa using hpc)
  have key : ∃ s ∈ B.Hhat, orderOf s = 2 ∧ s ∉ pCoreIn 2 B.Hhat ∧ s * x * s⁻¹ = x⁻¹ := by
    have hdvd : orderOf (k ^ m) ∣ 2 ^ 2 := by
      rw [show (2 : ℕ) ^ 2 = 4 from by norm_num]
      exact orderOf_dvd_iff_pow_eq_one.mpr hp4
    obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    interval_cases j
    · exact absurd (orderOf_eq_one_iff.mp (by simpa using hj)) hpne1
    · refine ⟨k ^ m, hpH, ?_, ?_, hpc⟩
      · rw [hj]; norm_num
      · intro hmem
        have hcomm : x * (k ^ m) = (k ^ m) * x :=
          (Subgroup.mem_centralizer_iff.mp (hVcentU hmem)) x hxU
        have h1 : x = x⁻¹ := by rw [← hpc, ← hcomm]; group
        exact hxne h1
    · rw [show (2 : ℕ) ^ 2 = 4 from by norm_num] at hj
      exact exists_involution_of_orderOf_four I h B h1 D hpH hj hp2V hxU hx1 hpc
  obtain ⟨s, hsH, hs2, hsV, hsx⟩ := key
  have hK : (D.K : Set G) = invSet B.U s := D.inv s hsH hs2 hsV
  have hxK : x ∈ D.K := by
    have h2 : x ∈ invSet B.U s := Work.CORE2A.mem_invSet.mpr ⟨hxU, hsx⟩
    rw [← hK] at h2
    exact h2
  exact D.hall.1 hxK

theorem InvSetVUSingleton (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs) (h : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B) (D : Work.GW2.Case1bData B) :
    ∀ y : G, orderOf y = 2 → y ∉ B.Hhat →
      Work.GW2.invSet (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) y = {1} := by
  intro y hy2 hyH
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy1 : y * y = 1 := by
    have h2 : y ^ 2 = 1 := by rw [← hy2]; exact pow_orderOf_eq_one y
    simpa [pow_two] using h2
  have h26 : Thm26Concl B := I.h26 G I.T.ft h B
  have hCA : ∀ v ∈ pCoreIn 2 B.Hhat, v ≠ 1 →
      Subgroup.centralizer ({v} : Set G) ≤ B.Hhat :=
    fun v hv hv1 => claimA G h B I.T.fus h26 D.four hv hv1
  have hVleH : pCoreIn 2 B.Hhat ≤ B.Hhat := Work.CORE2A.thm26Concl_O2_le_Hhat h26
  have hUleH : B.U ≤ B.Hhat := Work.CORE2A.thm26Concl_U_le_Hhat h26
  have hVcentU : pCoreIn 2 B.Hhat ≤ Subgroup.centralizer (B.U : Set G) := by
    rw [← Work.CORE2A.thm26Concl_centralizer_eq h26]; exact inf_le_right
  have hUodd : Odd (Nat.card B.U) := Work.CORE2A.bSetup_U_odd B
  have hNV : Subgroup.normalizer ((pCoreIn 2 B.Hhat : Subgroup G) : Set G) = B.Hhat :=
    _root_.Work.CORE3.NormalizerPcoreEqHhat G h B D.four
  have hVnorm : ∀ s ∈ B.Hhat, ∀ v ∈ pCoreIn 2 B.Hhat, s * v * s⁻¹ ∈ pCoreIn 2 B.Hhat := by
    intro s hs v hv
    have h1 : B.Hhat ≤ Subgroup.normalizer ((pCoreIn 2 B.Hhat : Subgroup G) : Set G) := by
      rw [hNV]
    exact ((Subgroup.mem_normalizer_iff.mp (h1 hs)) v).mp hv
  have hUnorm : ∀ s ∈ B.Hhat, ∀ u ∈ B.U, s * u * s⁻¹ ∈ B.U := by
    intro s hs u hu
    have h1 : B.Hhat ≤ Subgroup.normalizer (B.U : Set G) := by
      rw [← Work.CORE2A.thm26Concl_oddCore_eq h26]
      simpa [oddCoreIn] using
        _root_.Work.CORE3.le_normalizer_map_subtype B.Hhat (Work.GW2.oddCore ↥B.Hhat)
    exact ((Subgroup.mem_normalizer_iff.mp (h1 hs)) u).mp hu
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
  · exact ⟨Subgroup.mem_sup_left (Subgroup.one_mem _), by simp [hy1]⟩
  · intro x hx
    obtain ⟨hxVU, hxy⟩ := hx
    obtain ⟨v, hv, u, hu, hxeq⟩ :=
      _root_.Work.CORE3.exists_mul_of_mem_sup_of_normal (S := B.Hhat)
        (V := pCoreIn 2 B.Hhat) (U := B.U) hVleH hUleH hVnorm hUnorm x hxVU
    by_cases hv1 : v = 1
    · have hxU : x ∈ B.U := by rw [hxeq, hv1, one_mul]; exact hu
      by_cases hx1 : x = 1
      · exact hx1
      · exfalso
        obtain ⟨z, hzH, hzx⟩ := exists_hhat_conj_inv G I h B h1 D hxU hx1 hy2 hyH hxy
        have hxF : x ∈ fittingIn B.U :=
          fittingIn_of_mem_invSet_Hhat G I h B h1 D hxU hx1 ⟨z, hzH, hzx⟩
        have hzple : Subgroup.zpowers x ≤ fittingIn B.U := Subgroup.zpowers_le.mpr hxF
        have hNx : Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≤ B.Hhat :=
          h1.2 (Subgroup.zpowers x)
            (fun hbot => hx1 ((Subgroup.zpowers_eq_bot).mp hbot)) hzple
        have hyN : y ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) :=
          mem_normalizer_zpowers_of_inverts hy1 hxy
        exact hyH (hNx hyN)
    · exfalso
      have hum : u ^ Nat.card B.U = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard B.U hu)
      have hv2 : v ^ 2 = 1 := D.four.2 v hv
      have hvm : v ^ Nat.card B.U = v := by
        obtain ⟨k, hk⟩ := hUodd
        rw [hk, pow_succ, pow_mul, hv2, one_pow, one_mul]
      have hcomm : v * u = u * v := ((Subgroup.mem_centralizer_iff.mp (hVcentU hv)) u hu).symm
      have hpow : ∀ m : ℕ, (v * u) ^ m = v ^ m * u ^ m :=
        fun m => ((commute_iff_eq v u).mpr hcomm).mul_pow m
      have hxpow : x ^ Nat.card B.U = v := by
        rw [hxeq, hpow, hvm, hum, mul_one]
      have hyx : y * x ^ Nat.card B.U * y⁻¹ = (x ^ Nat.card B.U)⁻¹ := by
        rw [← MulAut.conj_apply, map_pow]
        have h1' : (MulAut.conj y) x = x⁻¹ := by rw [MulAut.conj_apply]; exact hxy
        rw [h1', inv_pow]
      have hvv : v⁻¹ = v := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hv2)
      have hyv : y * v * y⁻¹ = v := by rw [← hxpow, hyx, hxpow, hvv]
      have hyc : y ∈ Subgroup.centralizer ({v} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        rw [hw]
        have h2 := congrArg (fun t => t * y) hyv
        have h1' : y * v = v * y := by simpa [mul_assoc] using h2
        exact h1'.symm
      exact hyH (hCA v hv hv1 hyc)

end Work.CORE3
