import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.canonicalForm
import Submission.Work.ThmF.Bender.DTransitiveInv
import Submission.Work.ThmF.Bender.ncard_Kset_eq_ncard_InvHt
import Submission.Work.ThmF.Bender.ncard_InvHt_eq_ncard_involutions

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.structureIdentity` — Peterfalvi II, Ch. V §2 Lemma 1 b)

Let `H = Q ⋊ D` (`D = H ∩ Hᵗ`, `t` an involution outside `H`) be split rank-one data
(`IsSplitRankOneData G H Q t`).  Then there is a **unique** pair `(s, r)` with
`s ∈ Inv(Q)`, `r ∈ Q` and

  `t s t⁻¹ = r t r⁻¹`   (the source writes `t s t = r⁻¹ t r`),

the *structure identity* of Peterfalvi II Ch. V §2 (p. 243); `s` is the *distinguished
involution* of `Q` relative to `t`.

Route (following the source).  Fix an involution `u ∈ Q`.  With the canonical form
`t u t = x t y` (`x ∈ H`, `y ∈ Q`) of Ch. V §1 and `a := y x ∈ K = J(D,t)`, one shows

* always `t (k⁻¹ u k) t = (k y⁻¹ k⁻¹) (k a k) t (k y k⁻¹)` for `k ∈ K`;
* `(s, r) = (k⁻¹ u k, (k y k⁻¹)⁻¹)` is a solution **iff** `k a k = 1`, i.e. `k² = a⁻¹`.

Since `a` has odd order, `k₀ := a^(|a|/2) ∈ K` satisfies `k₀ a k₀ = 1`, giving existence.
For uniqueness one runs the correspondence with `u` replaced by the solution `s₀` just
produced: then `a = 1`, so the condition reads `k² = 1`, forcing `k = 1` because all elements
of `K ⊆ D` have odd order.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open LeanEval.GroupTheory.Defs

namespace Work.ThmF.ChV12

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-! ## Elementary facts about the datum -/

private lemma ht_mul_self (h : IsSplitRankOneData G H Q t) : t * t = 1 := by
  have h2 : t ^ 2 = 1 := by simpa [h.invol] using pow_orderOf_eq_one t
  simpa [pow_two] using h2

private lemma ht_inv (h : IsSplitRankOneData G H Q t) : t⁻¹ = t :=
  inv_eq_of_mul_eq_one_right (ht_mul_self h)

/-- `IsSplitRankOneData` gives an `IsSplitRankOne` (the strong embedding is the first three
fields). -/
private def toSplit (h : IsSplitRankOneData G H Q t) : IsSplitRankOne H Q t where
  stronglyEmbedded := ⟨h.ne_top, h.even_card, h.odd_inter⟩
  twoTransitive := h.twoTransitive
  invol := h.invol
  not_mem := h.not_mem
  le := h.le
  normal := h.normal
  inf_eq := h.inf_eq
  sup_eq := h.sup_eq

private lemma isStronglyEmbedded_of_data (h : IsSplitRankOneData G H Q t) :
    IsStronglyEmbedded H := ⟨h.ne_top, h.even_card, h.odd_inter⟩

/-! ## Facts about `K = J(D,t) = Kset H t` -/

private lemma Kset_inv_mem {H : Subgroup G} {t : G} {k : G} (hk : k ∈ Kset H t) :
    k⁻¹ ∈ Kset H t := by
  obtain ⟨hkD, hkinv⟩ := mem_Kset_iff.mp hk
  refine mem_Kset_iff.mpr ⟨(twoPoint H t).inv_mem hkD, ?_⟩
  have h1 : t * k⁻¹ * t⁻¹ = (t * k * t⁻¹)⁻¹ := by group
  rw [h1, hkinv, inv_inv]

private lemma Kset_conj_t (h : IsSplitRankOneData G H Q t) {k : G} (hk : k ∈ Kset H t) :
    t * k * t = k⁻¹ := by
  have h1 := (mem_Kset_iff.mp hk).2
  rwa [ht_inv h] at h1

private lemma Kset_mul_t_mul (h : IsSplitRankOneData G H Q t) {k : G} (hk : k ∈ Kset H t) :
    k * t * k = t := by
  have h1 : t * k * t = k⁻¹ := Kset_conj_t h hk
  have h2 : k * t * k * t = 1 := by
    calc k * t * k * t = k * (t * k * t) := by group
      _ = k * k⁻¹ := by rw [h1]
      _ = 1 := mul_inv_cancel k
  have h3 : (k * t * k) * (t * t) = t := by
    rw [show (k * t * k) * (t * t) = k * t * k * t * t from by group, h2, one_mul]
  rwa [ht_mul_self h, mul_one] at h3

private lemma Kset_mul_t (h : IsSplitRankOneData G H Q t) {k : G} (hk : k ∈ Kset H t) :
    k * t = t * k⁻¹ := by
  have h3 : k * t * k = t := Kset_mul_t_mul h hk
  calc k * t = (k * t * k) * k⁻¹ := by group
    _ = t * k⁻¹ := by rw [h3]

private lemma Kset_mem_twoPoint {k : G} (hk : k ∈ Kset H t) : k ∈ twoPoint H t :=
  Kset_subset H t hk

private lemma Kset_mem_H {k : G} (hk : k ∈ Kset H t) : k ∈ H :=
  (Work.Models.mem_twoPoint_iff.mp (Kset_mem_twoPoint hk)).1

private lemma Kset_conj_mem_Q (h : IsSplitRankOneData G H Q t) {k : G} (hk : k ∈ Kset H t)
    {x : G} (hx : x ∈ Q) : k * x * k⁻¹ ∈ Q :=
  (Subgroup.mem_normalizer_iff.mp (h.normal (Kset_mem_H hk)) x).mp hx

private lemma Kset_orderOf_odd (h : IsSplitRankOneData G H Q t) {k : G} (hk : k ∈ Kset H t) :
    Odd (orderOf k) := by
  have hD : Odd (Nat.card ↥(twoPoint H t)) := h.odd_inter t h.not_mem
  exact Odd.of_dvd_nat hD (Subgroup.orderOf_dvd_natCard _ (Kset_mem_twoPoint hk))

/-! ## `Q` has even order, so it contains an involution -/

private lemma even_card_Q (h : IsSplitRankOneData G H Q t) : Even (Nat.card Q) := by
  have hs := toSplit h
  have h1 : Nat.card H = Nat.card Q * Nat.card ↥(twoPoint H t) := split_card_H hs
  have hD : Odd (Nat.card ↥(twoPoint H t)) := split_odd_card_twoPoint hs
  have h2 : Even (Nat.card Q * Nat.card ↥(twoPoint H t)) := by
    rw [← h1]; exact h.even_card
  rw [Nat.even_mul] at h2
  exact h2.resolve_right (Nat.not_even_iff_odd.mpr hD)

private lemma exists_involution_Q (h : IsSplitRankOneData G H Q t) :
    ∃ u : G, u ∈ Q ∧ orderOf u = 2 := by
  have h2 : 2 ∣ Nat.card ↥Q := even_iff_two_dvd.mp (even_card_Q h)
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥Q) 2 h2
  exact ⟨(u : G), u.2, by rw [Subgroup.orderOf_coe, hu]⟩

/-! ## Uniqueness of the canonical form `a * t * q` -/

private lemma canon_unique (h : IsSplitRankOneData G H Q t) {a a' q q' : G}
    (ha : a ∈ H) (ha' : a' ∈ H) (hq : q ∈ Q) (hq' : q' ∈ Q)
    (heq : a * t * q = a' * t * q') : a = a' ∧ q = q' := by
  have hmem : a * t * q ∉ H := by
    intro hc
    refine h.not_mem ?_
    have h1 : t = a⁻¹ * (a * t * q) * q⁻¹ := by group
    rw [h1]
    exact H.mul_mem (H.mul_mem (H.inv_mem ha) hc) (H.inv_mem (h.le hq))
  obtain ⟨p, hp, huniq⟩ := canonicalForm h (a * t * q) hmem
  have h1 : (a, q) = p := huniq (a, q) ⟨ha, hq, rfl⟩
  have h2 : (a', q') = p := huniq (a', q') ⟨ha', hq', heq.symm⟩
  have h3 : (a, q) = (a', q') := by rw [h1, h2]
  exact ⟨congrArg Prod.fst h3, congrArg Prod.snd h3⟩

/-! ## The key identity and the condition on `k` -/

/-- `t u t ∉ H` for an involution `u ∈ Q`. -/
private lemma tut_not_mem_H (h : IsSplitRankOneData G H Q t) {u : G} (huQ : u ∈ Q)
    (hu2 : orderOf u = 2) : t * u * t ∉ H := by
  intro hc
  have huHt : u ∈ conj t H := by
    rw [Work.Models.mem_conj_iff, ht_inv h]
    exact hc
  have huD : u ∈ twoPoint H t := ⟨h.le huQ, huHt⟩
  have hubot : u ∈ (⊥ : Subgroup G) := by
    have hm : u ∈ Q ⊓ twoPoint H t := ⟨huQ, huD⟩
    rw [h.inf_eq] at hm
    exact hm
  have hu1 : u = 1 := Subgroup.mem_bot.mp hubot
  rw [hu1, orderOf_one] at hu2
  exact absurd hu2 (by norm_num)

/-- `a := y * x ∈ K = J(D,t)` when `t u t = x * t * y` is the canonical form of `t u t` for an
involution `u ∈ Q`. -/
private lemma a_mem_Kset (h : IsSplitRankOneData G H Q t) {u x y : G} (hu2 : orderOf u = 2)
    (hxH : x ∈ H) (hyQ : y ∈ Q) (hxy : x * t * y = t * u * t) : y * x ∈ Kset H t := by
  have htinv : t⁻¹ = t := ht_inv h
  have hu_sq : u * u = 1 := by
    have hh := pow_orderOf_eq_one u
    rw [hu2] at hh
    simpa [pow_two] using hh
  have h1 : x * t * y * (x * t * y) = 1 := by
    have h2 : t * u * t * (t * u * t) = 1 := by
      calc t * u * t * (t * u * t) = t * (u * (t * t) * u) * t := by group
        _ = t * (u * u) * t := by rw [ht_mul_self h, mul_one]
        _ = 1 := by rw [hu_sq, mul_one, ht_mul_self h]
    rw [hxy]; exact h2
  have h4 : t * y * x * t = x⁻¹ * y⁻¹ := by
    have h5 : x⁻¹ * (x * t * y * (x * t * y)) * y⁻¹ = x⁻¹ * 1 * y⁻¹ := by rw [h1]
    have hl : x⁻¹ * (x * t * y * (x * t * y)) * y⁻¹ = t * y * x * t := by group
    have hr : x⁻¹ * 1 * y⁻¹ = x⁻¹ * y⁻¹ := by group
    rw [hl, hr] at h5
    exact h5
  have h3 : t * (y * x) * t = (y * x)⁻¹ := by
    calc t * (y * x) * t = t * y * x * t := by group
      _ = x⁻¹ * y⁻¹ := h4
      _ = (y * x)⁻¹ := by rw [mul_inv_rev]
  refine mem_Kset_iff.mpr ⟨?_, ?_⟩
  · rw [Work.Models.mem_twoPoint_iff]
    exact ⟨H.mul_mem (h.le hyQ) hxH, by rw [htinv, h3]; exact H.inv_mem (H.mul_mem (h.le hyQ) hxH)⟩
  · rw [htinv]; exact h3

/-- **Key identity**: for `k ∈ K`, `t (k⁻¹ u k) t = (k y⁻¹ k⁻¹) (k a k) t (k y k⁻¹)`, where
`a = y x`. -/
private lemma key_identity (h : IsSplitRankOneData G H Q t) {u x y k : G}
    (hxH : x ∈ H) (hyQ : y ∈ Q) (hxy : x * t * y = t * u * t) (hk : k ∈ Kset H t) :
    t * (k⁻¹ * u * k) * t
      = (k * y⁻¹ * k⁻¹) * (k * (y * x) * k) * t * (k * y * k⁻¹) := by
  have hktk : k * t * k = t := Kset_mul_t_mul h hk
  have h1 : t * (k⁻¹ * u * k) * t = k * (t * u * t) * k⁻¹ := by
    have hkt : k * t = t * k⁻¹ := Kset_mul_t h hk
    have e1 : t * k⁻¹ = k * t := hkt.symm
    have s1 : t * (k⁻¹ * u * k) * t = (t * k⁻¹) * u * (k * t) := by group
    have s2 : (t * k⁻¹) * u * (k * t) = (k * t) * u * (k * t) := by rw [e1]
    have s3 : (k * t) * u * (k * t) = (k * t) * u * (t * k⁻¹) := by rw [hkt]
    have s4 : (k * t) * u * (t * k⁻¹) = k * (t * u * t) * k⁻¹ := by group
    exact s1.trans (s2.trans (s3.trans s4))
  rw [h1, ← hxy]
  have h6 : (k * y⁻¹ * k⁻¹) * (k * (y * x) * k) * t * (k * y * k⁻¹)
      = k * x * (k * t * k) * y * k⁻¹ := by group
  rw [h6, hktk]
  group

/-- The derivation: if `(s, r)` is a solution and `s = k⁻¹ u k` with `k ∈ K`, then
`k (y x) k = 1`. -/
private lemma solution_cond (h : IsSplitRankOneData G H Q t) {u x y s ρ k : G}
    (hxH : x ∈ H) (hyQ : y ∈ Q) (hxy : x * t * y = t * u * t) (hk : k ∈ Kset H t)
    (hs : k⁻¹ * u * k = s) (hρQ : ρ ∈ Q) (hsol : t * s * t = ρ * t * ρ⁻¹) :
    k * (y * x) * k = 1 := by
  have hkH : k ∈ H := Kset_mem_H hk
  have hP : k * y * k⁻¹ ∈ Q := Kset_conj_mem_Q h hk hyQ
  have hPeq : k * y⁻¹ * k⁻¹ = (k * y * k⁻¹)⁻¹ := by group
  have hA : (k * y⁻¹ * k⁻¹) * (k * (y * x) * k) * t * (k * y * k⁻¹) = ρ * t * ρ⁻¹ := by
    rw [← key_identity h hxH hyQ hxy hk, hs]
    exact hsol
  have hmain : (k * (y * x) * k) * t = ((k * y * k⁻¹) * ρ) * t * ((k * y * k⁻¹) * ρ)⁻¹ := by
    calc (k * (y * x) * k) * t
        = (k * y * k⁻¹) * ((k * y⁻¹ * k⁻¹) * (k * (y * x) * k) * t * (k * y * k⁻¹))
            * (k * y * k⁻¹)⁻¹ := by rw [hPeq]; group
      _ = (k * y * k⁻¹) * (ρ * t * ρ⁻¹) * (k * y * k⁻¹)⁻¹ := by rw [hA]
      _ = ((k * y * k⁻¹) * ρ) * t * ((k * y * k⁻¹) * ρ)⁻¹ := by group
  have hμQ : (k * y * k⁻¹) * ρ ∈ Q := Q.mul_mem hP hρQ
  have hμiQ : ((k * y * k⁻¹) * ρ)⁻¹ ∈ Q := Q.inv_mem hμQ
  have hkakH : k * (y * x) * k ∈ H := H.mul_mem (H.mul_mem hkH (H.mul_mem (h.le hyQ) hxH)) hkH
  have hμH : (k * y * k⁻¹) * ρ ∈ H := h.le hμQ
  obtain ⟨h1, h2⟩ := canon_unique h hkakH hμH Q.one_mem hμiQ (by rw [mul_one]; exact hmain)
  rw [h1]
  exact inv_eq_one.mp h2.symm

/-! ## Surjectivity of `k ↦ k⁻¹ u k` on `Inv(Q)` -/

private lemma exists_conj_Kset (h : IsSplitRankOneData G H Q t) {u : G} (huQ : u ∈ Q)
    (hu2 : orderOf u = 2) {s : G} (hsQ : s ∈ Q) (hs2 : orderOf s = 2) :
    ∃ k : G, k ∈ Kset H t ∧ k⁻¹ * u * k = s := by
  have hH : IsStronglyEmbedded H := isStronglyEmbedded_of_data h
  have himg_sub : (fun k : G => k⁻¹ * u * k) '' (Kset H t) ⊆ involutions (Q : Set G) := by
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨?_, ?_⟩
    · have hmem := (Subgroup.mem_normalizer_iff.mp (h.normal (H.inv_mem (Kset_mem_H hk))) u).mp huQ
      simpa using hmem
    · rw [show (fun k : G => k⁻¹ * u * k) k = k⁻¹ * u * (k⁻¹)⁻¹ from by simp,
        Work.ThmF.Bender.orderOf_conj_eq, hu2]
  have hinj : Set.InjOn (fun k : G => k⁻¹ * u * k) (Kset H t) := by
    intro k1 hk1 k2 hk2 heq
    have h1 : k1⁻¹ ∈ Kset H t := Kset_inv_mem hk1
    have h2 : k2⁻¹ ∈ Kset H t := Kset_inv_mem hk2
    have heq' : k1⁻¹ * u * (k1⁻¹)⁻¹ = k2⁻¹ * u * (k2⁻¹)⁻¹ := by simpa using heq
    exact inv_injective
      (Work.ThmF.Bender.Kset_conj_injective hH h.invol h.not_mem (h.le huQ) hu2 h1 h2 heq')
  have hcard1 : ((fun k : G => k⁻¹ * u * k) '' (Kset H t)).ncard = (Kset H t).ncard :=
    Set.InjOn.ncard_image hinj
  have hcard2 : (Kset H t).ncard = (involutions (H : Set G)).ncard :=
    (Work.ThmF.Bender.ncard_Kset_eq_ncard_InvHt hH h.invol h.not_mem).trans
      (Work.ThmF.Bender.ncard_InvHt_eq_ncard_involutions hH h.invol h.not_mem)
  have hcard3 : (involutions (Q : Set G)).ncard ≤ (involutions (H : Set G)).ncard :=
    Set.ncard_le_ncard (fun x hx => ⟨h.le hx.1, hx.2⟩)
  have hle : (involutions (Q : Set G)).ncard ≤ ((fun k : G => k⁻¹ * u * k) '' (Kset H t)).ncard := by
    rw [hcard1, hcard2]; exact hcard3
  have hset : (fun k : G => k⁻¹ * u * k) '' (Kset H t) = involutions (Q : Set G) :=
    Set.eq_of_subset_of_ncard_le himg_sub hle
  have hmem : s ∈ (fun k : G => k⁻¹ * u * k) '' (Kset H t) := by rw [hset]; exact ⟨hsQ, hs2⟩
  obtain ⟨k, hk, hkf⟩ := hmem
  exact ⟨k, hk, by simpa using hkf⟩

/-! ## The main theorem -/

open LeanEval.GroupTheory.Defs Submission.Blueprint Work.ThmF in theorem structureIdentity {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} (h : IsSplitRankOneData G H Q t) : ∃! p : G × G, p.1 ∈ Q ∧ orderOf p.1 = 2 ∧ p.2 ∈ Q ∧ t * p.1 * t⁻¹ = p.2 * t * p.2⁻¹ := by
  obtain ⟨u, huQ, hu2⟩ := exists_involution_Q h
  -- the canonical form of `t u t`
  have hnotH : t * u * t ∉ H := tut_not_mem_H h huQ hu2
  obtain ⟨⟨x, y⟩, hp, _huniq⟩ := canonicalForm h (t * u * t) hnotH
  have hxH : x ∈ H := hp.1
  have hyQ : y ∈ Q := hp.2.1
  have hxy : x * t * y = t * u * t := hp.2.2
  have haK : y * x ∈ Kset H t := a_mem_Kset h hu2 hxH hyQ hxy
  -- existence: `k₀ = a^(|a|/2)` satisfies `k₀ a k₀ = 1`
  have hodd_a : Odd (orderOf (y * x)) := Kset_orderOf_odd h haK
  have hidx : orderOf (y * x) / 2 + (orderOf (y * x) / 2 + 1) = orderOf (y * x) := by
    have hdiv := Nat.two_mul_div_two_add_one_of_odd hodd_a
    omega
  set k0 : G := (y * x) ^ (orderOf (y * x) / 2) with hk0def
  have hk0K : k0 ∈ Kset H t := pow_mem_Kset haK _
  have hk0a : k0 * (y * x) * k0 = 1 := by
    rw [hk0def, mul_assoc, ← pow_succ', ← pow_add, hidx, pow_orderOf_eq_one]
  set s0 : G := k0⁻¹ * u * k0 with hs0def
  set ρ0 : G := (k0 * y * k0⁻¹)⁻¹ with hρ0def
  have hk0H : k0 ∈ H := Kset_mem_H hk0K
  have hs0Q : s0 ∈ Q := by
    rw [hs0def]
    have hmem := (Subgroup.mem_normalizer_iff.mp (h.normal (H.inv_mem hk0H)) u).mp huQ
    simpa using hmem
  have hs02 : orderOf s0 = 2 := by
    rw [hs0def, show k0⁻¹ * u * k0 = k0⁻¹ * u * (k0⁻¹)⁻¹ from by group,
      Work.ThmF.Bender.orderOf_conj_eq, hu2]
  have hρ0Q : ρ0 ∈ Q := by
    rw [hρ0def]
    exact Q.inv_mem ((Subgroup.mem_normalizer_iff.mp (h.normal hk0H) y).mp hyQ)
  have hsol0 : t * s0 * t⁻¹ = ρ0 * t * ρ0⁻¹ := by
    have hPeq : k0 * y⁻¹ * k0⁻¹ = (k0 * y * k0⁻¹)⁻¹ := by group
    have hkey := key_identity h hxH hyQ hxy hk0K
    rw [ht_inv h, hs0def, hρ0def, inv_inv, hkey, hPeq, hk0a, mul_one]
  refine ⟨(s0, ρ0), ⟨hs0Q, hs02, hρ0Q, hsol0⟩, ?_⟩
  rintro ⟨s, ρ⟩ ⟨hsQ, hs2, hρQ, hsol⟩
  have hsQ' : s ∈ Q := hsQ
  have hs2' : orderOf s = 2 := hs2
  have hρQ' : ρ ∈ Q := hρQ
  have hsol'' : t * s * t⁻¹ = ρ * t * ρ⁻¹ := hsol
  have hsol' : t * s * t = ρ * t * ρ⁻¹ := by
    have hh := hsol
    rwa [ht_inv h] at hh
  have hsol0t : t * s0 * t = ρ0 * t * ρ0⁻¹ := by
    have hh := hsol0
    rwa [ht_inv h] at hh
  obtain ⟨k, hkK, hks⟩ := exists_conj_Kset h hs0Q hs02 hsQ' hs2'
  have hks' : k⁻¹ * s0 * k = s := hks
  have hcond := solution_cond h (h.le hρ0Q) (Q.inv_mem hρ0Q)
    (u := s0) (x := ρ0) (y := ρ0⁻¹) hsol0t.symm hkK hks' hρQ' hsol'
  have hkk : k * k = 1 := by simpa using hcond
  have hk1 : k = 1 := by
    have hoddk : Odd (orderOf k) := Kset_orderOf_odd h hkK
    have hdvd : orderOf k ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]
      exact hkk
    have hle2 : orderOf k ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < orderOf k := orderOf_pos k
    have hne2 : orderOf k ≠ 2 := fun hc =>
      (Nat.not_even_iff_odd.mpr hoddk) (hc ▸ even_two)
    have hone : orderOf k = 1 := by omega
    exact orderOf_eq_one_iff.mp hone
  have hs_eq : s = s0 := by rw [← hks']; rw [hk1]; group
  have hρ_eq : ρ = ρ0 := by
    have h1 : ρ * t * ρ⁻¹ = ρ0 * t * ρ0⁻¹ := by rw [← hsol', hs_eq, hsol0t]
    exact (canon_unique h (h.le hρQ') (h.le hρ0Q) (Q.inv_mem hρQ') (Q.inv_mem hρ0Q) h1).1
  exact Prod.ext hs_eq hρ_eq

end Work.ThmF.ChV12
