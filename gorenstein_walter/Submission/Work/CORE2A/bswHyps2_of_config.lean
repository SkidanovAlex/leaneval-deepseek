/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.Dihedral.Defs

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

/-!
# CORE2A: the configuration of Bender's Lemma 2.2 produces the BSW hypotheses

This file proves `Work.CORE2A.bswHyps2_of_config`: under the configuration of Bender's
Lemma 2.2 (`U = I_U(s)`, `S₀ ≤ C(U)`, `N(X) ≤ H` for `1 ≠ X ≤ U`) the subgroup
`K = U ⊔ S₀` satisfies the hypotheses of the Brauer–Suzuki–Wall theorem in the form
`Work.GW2.BSWHyps2 G t s K` (Bender 1974, (i)–(iv)).

The group-theoretic content is classical and is proved here from scratch:

* `K` is abelian (`U` is abelian because the involution `s` inverts it, `S₀` is cyclic and
  `S₀` centralizes `U`);
* `C(t) = K⟨s⟩` (using `C(t) = U ⊔ S` and `S = S₀ ⊔ ⟨s⟩`);
* `s` inverts `K` (componentwise on `U` and on `S₀`, the latter since `S` is dihedral);
* `C_K(s) = ⟨t⟩`;
* `K` is a TI subgroup (the only use of `N(X) ≤ H`): if `y ∈ K ∩ K^g`, then either some
  `2`-element of `y` is nontrivial, forcing `g ∈ C(t)`, or `y ∈ U ∩ U^g`, whence
  `⟨U, U^g⟩ ≤ N(⟨y⟩) ≤ H` and a Hall-type quotient argument forces `U^g = U`, so
  `g ∈ N(U) ≤ H`;
* all involutions of `G` are conjugate (`FUS`, using that `G` is a simple nonabelian group).
-/

open scoped MatrixGroups

namespace Work.CORE2A

open Subgroup

/-! ## 1. General group-theoretic lemmas -/

section General

variable {G : Type*} [Group G]

/-- If two subgroups commute elementwise, then every element of their join is a product
`a * b` with `a` in the first and `b` in the second. -/
theorem bsw_mem_sup_of_commute {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  let f : ↥A × ↥B →* G :=
    { toFun := fun p => (p.1 : G) * (p.2 : G)
      map_one' := by simp
      map_mul' := fun p q => by
        have hswap : (↑q.1 : G) * (↑p.2 : G) = (↑p.2 : G) * (↑q.1 : G) :=
          h _ q.1.property _ p.2.property
        show ((p.1 * q.1 : ↥A) : G) * ((p.2 * q.2 : ↥B) : G) =
          ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G))
        simp only [Subgroup.coe_mul]
        conv_lhs => rw [mul_assoc]
        conv_lhs => rw [← mul_assoc (↑q.1 : G) (↑p.2 : G) (↑q.2 : G)]
        conv_lhs => rw [hswap]
        conv_lhs => rw [mul_assoc]
        conv_lhs => rw [← mul_assoc (↑p.1 : G) (↑p.2 : G) ((↑q.1 : G) * (↑q.2 : G))] }
  have hrange : f.range = A ⊔ B := by
    apply le_antisymm
    · rintro x ⟨p, rfl⟩
      exact Subgroup.mul_mem_sup p.1.property p.2.property
    · apply sup_le
      · intro a ha
        exact ⟨(⟨a, ha⟩, 1), by simp [f]⟩
      · intro b hb
        exact ⟨(1, ⟨b, hb⟩), by simp [f]⟩
  rw [← hrange] at hx
  obtain ⟨p, hp⟩ := hx
  exact ⟨p.1, p.1.property, p.2, p.2.property, by rw [← hp]; rfl⟩

/-- A nontrivial element of odd order with `x * x = 1` is trivial. -/
theorem bsw_eq_one_of_odd_order_of_sq_eq_one {A : Subgroup G} (hA : Odd (Nat.card A))
    {a : G} (ha : a ∈ A) (ha2 : a * a = 1) : a = 1 := by
  have hdvdA : orderOf a ∣ Nat.card A := Subgroup.orderOf_dvd_natCard A ha
  have ho : Odd (orderOf a) := Odd.of_dvd_nat hA hdvdA
  have hdvd : orderOf a ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using ha2)
  exact orderOf_eq_one_iff.mp ((ho.coprime_two_right).eq_one_of_dvd hdvd)

/-- If `(a * c)² = 1` with `a` in an odd-order subgroup `A` and `c` in a subgroup `C` commuting
elementwise with `A` and meeting it trivially, then `a * c` lies in `C`. -/
theorem bsw_mul_mem_right_of_sq_eq_one {A C : Subgroup G}
    (hAc : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) (hbot : A ⊓ C = ⊥) (hA : Odd (Nat.card A))
    {a : G} (ha : a ∈ A) {c : G} (hc : c ∈ C) (hsq : (a * c) * (a * c) = 1) :
    a * c ∈ C := by
  have hsq2 : (a * a) * (c * c) = 1 := by
    rw [← hsq]
    conv_rhs => rw [mul_assoc]
    conv_rhs => rw [← mul_assoc c a c]
    conv_rhs => rw [← hAc a ha c hc]
    conv_rhs => rw [mul_assoc]
    conv_rhs => rw [← mul_assoc a a (c * c)]
  have ha2 : a * a = 1 := by
    have hmem : a * a ∈ A ⊓ C := by
      refine ⟨A.mul_mem ha ha, ?_⟩
      rw [eq_inv_of_mul_eq_one_left hsq2]
      exact C.inv_mem (C.mul_mem hc hc)
    rw [hbot] at hmem
    simpa using hmem
  have ha1 : a = 1 := bsw_eq_one_of_odd_order_of_sq_eq_one hA ha ha2
  rw [ha1, one_mul]
  exact hc

/-- If `a * c` has odd order, `a` lies in an odd-order subgroup `A` and `c` in a `2`-subgroup `C`
commuting elementwise with `A` and meeting it trivially, then `c = 1`. -/
theorem bsw_eq_one_of_mul_mem_of_odd_order {A C : Subgroup G}
    (hAc : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) (hbot : A ⊓ C = ⊥) (hC2 : IsPGroup 2 ↥C)
    {a : G} (ha : a ∈ A) {c : G} (hc : c ∈ C) (hodd : Odd (orderOf (a * c))) : c = 1 := by
  have hcomm : Commute a c := hAc a ha c hc
  have h1 : a ^ (orderOf (a * c)) * c ^ (orderOf (a * c)) = 1 := by
    rw [← hcomm.mul_pow (orderOf (a * c))]
    exact pow_orderOf_eq_one _
  have hcn : c ^ (orderOf (a * c)) = 1 := by
    have hmem : (c ^ orderOf (a * c))⁻¹ ∈ A ⊓ C := by
      refine ⟨?_, C.inv_mem (C.pow_mem hc _)⟩
      have h2 : c ^ orderOf (a * c) = (a ^ orderOf (a * c))⁻¹ :=
        eq_inv_of_mul_eq_one_right h1
      rw [h2, inv_inv]
      exact A.pow_mem ha _
    rw [hbot] at hmem
    simpa using hmem
  have hdvdn : orderOf c ∣ orderOf (a * c) := orderOf_dvd_iff_pow_eq_one.mpr hcn
  obtain ⟨k, hk⟩ := hC2 ⟨c, hc⟩
  have hdvd2 : orderOf c ∣ 2 ^ k := by
    apply orderOf_dvd_iff_pow_eq_one.mpr
    have := congrArg Subtype.val hk
    simpa using this
  have ho : Odd (orderOf c) := Odd.of_dvd_nat hodd hdvdn
  exact orderOf_eq_one_iff.mp (((ho.coprime_two_right).pow_right k).eq_one_of_dvd hdvd2)

/-- In a finite group, an element of even order has an associated involution: its
`(orderOf / 2)`-th power. -/
theorem bsw_orderOf_pow_div_two_of_even {H : Type*} [Group H] [Finite H] {x : H}
    (hx : x ≠ 1) (heven : Even (orderOf x)) :
    orderOf (x ^ (orderOf x / 2)) = 2 := by
  have hn1 : orderOf x ≠ 1 := fun h => hx (orderOf_eq_one_iff.mp h)
  have hn0 : orderOf x ≠ 0 := orderOf_ne_zero_iff.mpr (isOfFinOrder_of_finite x)
  have h2n : 2 * (orderOf x / 2) = orderOf x := Nat.mul_div_cancel' (even_iff_two_dvd.mp heven)
  have hpos : 0 < orderOf x / 2 := by omega
  have hdvd : orderOf x / 2 ∣ orderOf x := ⟨2, by rw [mul_comm]; exact h2n.symm⟩
  rw [orderOf_pow, Nat.gcd_eq_right hdvd]
  have h1 : (orderOf x / 2) * (orderOf x / (orderOf x / 2)) = orderOf x :=
    Nat.mul_div_cancel' hdvd
  have h2 : (orderOf x / 2) * (orderOf x / (orderOf x / 2)) = (orderOf x / 2) * 2 := by
    rw [h1, mul_comm (orderOf x / 2) 2, h2n]
  exact Nat.mul_left_cancel hpos h2

end General

/-! ## 2. Cyclic subgroups of index two in a dihedral group -/

/-- In `DihedralGroup n` with `n ≥ 2` a cyclic subgroup `T` of index two is the rotation
subgroup; hence every element outside `T` inverts `T`. -/
theorem bsw_dihedral_cyclic_index_two_inverts (n : ℕ) (hn : 2 ≤ n)
    (T : Subgroup (DihedralGroup n)) (hcyc : IsCyclic T) (hidx : T.relIndex ⊤ = 2)
    (y : DihedralGroup n) (hy : y ∉ T) : ∀ z ∈ T, y * z * y⁻¹ = z⁻¹ := by
  have hcardT : Nat.card T = n := by
    have h := Subgroup.relIndex_mul_card T ⊤
    rw [hidx, inf_top_eq, Subgroup.card_top, DihedralGroup.nat_card] at h
    exact Nat.mul_left_cancel (by norm_num : (0 : ℕ) < 2) h
  intro z hz
  rcases eq_or_ne n 2 with hn2 | hn2
  · subst hn2
    have hcard2 : Nat.card T = 2 := by rw [hcardT]
    have hsq : ∀ a : DihedralGroup 2, a ^ 2 = 1 := by
      intro a
      rcases eq_or_ne a 1 with h1 | ha
      · subst h1; simp
      · have h2 : orderOf a = 2 :=
          (orderOf_eq_two_iff (IsKleinFour.exponent_two (G := DihedralGroup 2))).mpr ha
        simpa [h2] using pow_orderOf_eq_one a
    have hcomm : ∀ a b : DihedralGroup 2, a * b = b * a := by
      intro a b
      have ha : a * a = 1 := by simpa [pow_two] using hsq a
      have hb : b * b = 1 := by simpa [pow_two] using hsq b
      have hab : (a * b) * (a * b) = 1 := by simpa [pow_two] using hsq (a * b)
      have h1 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_left hab
      rw [← h1, mul_inv_rev, inv_eq_of_mul_eq_one_left ha, inv_eq_of_mul_eq_one_left hb]
    have hzz : z * z = 1 := by
      have hdvd : orderOf z ∣ 2 := by
        have h := Subgroup.orderOf_dvd_natCard T hz
        rwa [hcard2] at h
      have h2 : z ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
      simpa [pow_two] using h2
    rw [inv_eq_of_mul_eq_one_left hzz, mul_assoc, hcomm z y⁻¹, ← mul_assoc, mul_inv_cancel,
      one_mul]
  · have hn3 : 3 ≤ n := by omega
    haveI : NeZero n := ⟨by omega⟩
    have hTrot : T = Work.Dihedral.rot n := by
      obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top T).mp hcyc
      have hordg : orderOf g = n := by rw [← Nat.card_zpowers g, hg, hcardT]
      have hgR : g ∈ Work.Dihedral.rot n := by
        rcases Work.Dihedral.eq_r_or_sr g with ⟨i, rfl⟩ | ⟨i, rfl⟩
        · exact Work.Dihedral.r_mem_rot i
        · rw [DihedralGroup.orderOf_sr] at hordg; omega
      have hTR : T ≤ Work.Dihedral.rot n := by
        rw [← hg]; exact Subgroup.zpowers_le.mpr hgR
      exact Subgroup.eq_of_le_of_card_ge hTR (by rw [Work.Dihedral.nat_card_rot, hcardT])
    have hy' : y ∉ Work.Dihedral.rot n := by rw [← hTrot]; exact hy
    have hz' : z ∈ Work.Dihedral.rot n := by rw [← hTrot]; exact hz
    obtain ⟨i, rfl⟩ := Work.Dihedral.notMem_rot.mp hy'
    obtain ⟨j, rfl⟩ := Work.Dihedral.mem_rot.mp hz'
    rw [DihedralGroup.sr_mul_r, DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr,
      DihedralGroup.inv_r]
    congr 1
    ring

/-- In a group `G`, if `S ≤ G` is isomorphic to `DihedralGroup n` (`n ≥ 2`) and `S₀ ≤ S` is a
cyclic subgroup of index two, then every `s ∈ S ∖ S₀` inverts `S₀`. -/
theorem bsw_dihedral_inverts_index_two {G : Type*} [Group G] (n : ℕ) (hn : 2 ≤ n)
    (S S0 : Subgroup G) (hD : Nonempty (S ≃* DihedralGroup n)) (hS0 : S0 ≤ S)
    (hcyc : IsCyclic S0) (hidx : S0.relIndex S = 2) (s : G) (hs : s ∈ S) (hs0 : s ∉ S0) :
    ∀ z ∈ S0, s * z * s⁻¹ = z⁻¹ := by
  obtain ⟨e⟩ := hD
  set T : Subgroup (DihedralGroup n) := (S0.subgroupOf S).map e.toMonoidHom with hT
  have hcardS : Nat.card ↥S = 2 * n := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hcardS0 : Nat.card ↥S0 = n := by
    have h := Subgroup.relIndex_mul_card S0 S
    rw [hidx, inf_eq_left.mpr hS0] at h
    rw [hcardS] at h
    exact Nat.mul_left_cancel (by norm_num : (0 : ℕ) < 2) h
  have hcardT : Nat.card T = n := by
    rw [hT, ← Nat.card_congr
        (Subgroup.equivMapOfInjective (S0.subgroupOf S) e.toMonoidHom e.injective).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS0).toEquiv]
    exact hcardS0
  have hcycT : IsCyclic T := by
    rw [hT]
    exact (MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective (S0.subgroupOf S) e.toMonoidHom e.injective)).mp
      ((MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hS0)).mpr hcyc)
  have hidxT : T.relIndex ⊤ = 2 := by
    have h := Subgroup.relIndex_mul_card T ⊤
    rw [inf_top_eq, Subgroup.card_top, DihedralGroup.nat_card, hcardT] at h
    exact Nat.mul_right_cancel (by omega : 0 < n) h
  have hy : e ⟨s, hs⟩ ∉ T := by
    intro hcon
    rw [hT, Subgroup.mem_map] at hcon
    obtain ⟨x, hx, hxe⟩ := hcon
    rw [Subgroup.mem_subgroupOf] at hx
    have hx' : x = ⟨s, hs⟩ := e.injective hxe
    rw [hx'] at hx
    exact hs0 hx
  have key := bsw_dihedral_cyclic_index_two_inverts n hn T hcycT hidxT (e ⟨s, hs⟩) hy
  intro z hz
  have hzS : z ∈ S := hS0 hz
  have hmem : s * z * s⁻¹ ∈ S := S.mul_mem (S.mul_mem hs hzS) (S.inv_mem hs)
  have hzmem : e ⟨z, hzS⟩ ∈ T :=
    Subgroup.mem_map.mpr ⟨⟨z, hzS⟩, by rw [Subgroup.mem_subgroupOf]; exact hz, rfl⟩
  have h1 : e ⟨s * z * s⁻¹, hmem⟩ = e ⟨s, hs⟩ * e ⟨z, hzS⟩ * (e ⟨s, hs⟩)⁻¹ := by
    rw [show (⟨s * z * s⁻¹, hmem⟩ : ↥S) = ⟨s, hs⟩ * ⟨z, hzS⟩ * (⟨s, hs⟩ : ↥S)⁻¹ from
        Subtype.ext (by simp [mul_assoc]), map_mul, map_mul, map_inv]
  have h2 : e ⟨z⁻¹, S.inv_mem hzS⟩ = (e ⟨z, hzS⟩)⁻¹ := by
    rw [show (⟨z⁻¹, S.inv_mem hzS⟩ : ↥S) = (⟨z, hzS⟩ : ↥S)⁻¹ from Subtype.ext rfl, map_inv]
  have hgoal : (⟨s * z * s⁻¹, hmem⟩ : ↥S) = ⟨z⁻¹, S.inv_mem hzS⟩ := by
    apply e.injective
    rw [h1, h2]
    exact key (e ⟨z, hzS⟩) hzmem
  exact congrArg Subtype.val hgoal

/-! ## 3. A Hall-type projection lemma -/

/-- If `H = U ⊔ S` with `S` a `2`-group and `U` normal in `H`, then every element of `H` of odd
order lies in `U`. -/
theorem bsw_mem_left_of_mem_sup_of_odd_order {G : Type*} [Group G] [Finite G]
    (U S H : Subgroup G) (hH : U ⊔ S = H) (hS2 : IsPGroup 2 S)
    (hUn : (U.subgroupOf H).Normal) {v : G} (hv : v ∈ H) (hodd : Odd (orderOf v)) :
    v ∈ U := by
  have hUH : U ≤ H := by rw [← hH]; exact le_sup_left
  have hSH : S ≤ H := by rw [← hH]; exact le_sup_right
  set N : Subgroup ↥H := U.subgroupOf H with hN
  haveI : N.Normal := hUn
  have hsupH : (U.subgroupOf H) ⊔ (S.subgroupOf H) = ⊤ := by
    rw [← hN, ← Subgroup.subgroupOf_sup hUH hSH, hH, Subgroup.subgroupOf_self]
  have htop : ((S.subgroupOf H).map (QuotientGroup.mk' N)) = ⊤ := by
    have h1 : ((U.subgroupOf H) ⊔ (S.subgroupOf H)).map (QuotientGroup.mk' N) = ⊤ := by
      rw [hsupH, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
    rw [Subgroup.map_sup] at h1
    have h2 : ((U.subgroupOf H).map (QuotientGroup.mk' N)) = ⊥ := by
      apply le_antisymm _ bot_le
      rintro x hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [Subgroup.mem_bot, ← MonoidHom.mem_ker, QuotientGroup.ker_mk' N]
      rw [← hN] at hy
      exact hy
    rw [h2, bot_sup_eq] at h1
    exact h1
  have hP : IsPGroup 2 (↥H ⧸ N) := by
    haveI : IsPGroup 2 ↥(S.subgroupOf H) :=
      IsPGroup.of_equiv hS2 (Subgroup.subgroupOfEquivOfLe hSH).symm
    have hP' : IsPGroup 2 ↥((S.subgroupOf H).map (QuotientGroup.mk' N)) :=
      IsPGroup.map (H := S.subgroupOf H) (K := ↥H ⧸ N)
        ‹IsPGroup 2 ↥(S.subgroupOf H)› (QuotientGroup.mk' N)
    rw [htop] at hP'
    exact IsPGroup.of_equiv hP' Subgroup.topEquiv
  have hmem : (⟨v, hv⟩ : ↥H) ∈ N := by
    by_contra hcon
    set x : ↥H ⧸ N := QuotientGroup.mk' N ⟨v, hv⟩ with hx
    have hx1 : x ≠ 1 := by
      intro h
      apply hcon
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
      rw [hx] at h
      exact h
    have hxv : x ^ (orderOf v) = 1 := by
      rw [hx, ← map_pow]
      have h1 : (⟨v, hv⟩ : ↥H) ^ (orderOf v) = 1 := by
        rw [Subgroup.orderOf_coe (⟨v, hv⟩ : ↥H)]
        exact pow_orderOf_eq_one _
      rw [h1, map_one]
    obtain ⟨k, hk⟩ := hP x
    have hoddx : Odd (orderOf x) := Odd.of_dvd_nat hodd (orderOf_dvd_iff_pow_eq_one.mpr hxv)
    have hdx : orderOf x ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hk
    have hcx : (orderOf x).Coprime (2 ^ k) := (hoddx.coprime_two_right).pow_right k
    exact hx1 (orderOf_eq_one_iff.mp (hcx.eq_one_of_dvd hdx))
  rw [hN, Subgroup.mem_subgroupOf] at hmem
  exact hmem

/-- `O(H)` is normal in `H`, in the relative form needed for quotients. -/
theorem bsw_oddCoreIn_subgroupOf_normal {G : Type*} [Group G] (H : Subgroup G) :
    ((Work.GW2.oddCoreIn H).subgroupOf H).Normal := by
  have h : (Work.GW2.oddCoreIn H).subgroupOf H = Work.GW2.oddCore ↥H := by
    rw [Work.GW2.oddCoreIn, Subgroup.subgroupOf]
    exact Subgroup.comap_map_eq_self (by simp)
  rw [h]
  exact Work.GW2.oddCore_normal ↥H

/-! ## 4. The main theorem -/

theorem bswHyps2_of_config (T : Work.GW2.LocalToolkit) {G : Type} [Group G] [Finite G]
    (hctx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (hdihed : ∃ n : ℕ, 2 ≤ n ∧ Nonempty ((B.S : Subgroup G) ≃* DihedralGroup n))
    (s : G) (hsS : s ∈ (B.S : Subgroup G)) (hs0 : s ∉ B.S0) (hsord : orderOf s = 2)
    (hI : (B.U : Set G) = Work.GW2.invSet B.U s)
    (hS0C : B.S0 ≤ Subgroup.centralizer (B.U : Set G))
    (hNX : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ B.U → Subgroup.normalizer (X : Set G) ≤ B.H) :
    Work.GW2.BSWHyps2 G B.t s (B.U ⊔ B.S0) := by
  obtain ⟨n, hn, hdih⟩ := hdihed
  haveI : IsCyclic ↥B.S0 := B.S0_cyclic
  have hUodd : Odd (Nat.card ↥B.U) := bSetup_U_odd B
  have hS0two : IsPGroup 2 ↥B.S0 := (B.S.isPGroup').to_le B.S0_le
  -- `U` and `S₀` commute
  have hUS0comm : ∀ u ∈ B.U, ∀ z ∈ B.S0, u * z = z * u := fun u hu z hz =>
    (Subgroup.mem_centralizer_iff.mp (hS0C hz)) u hu
  -- `s` inverts `U`
  have hinvU : ∀ x ∈ B.U, s * x * s⁻¹ = x⁻¹ := by
    intro x hx
    have hx' : x ∈ Work.GW2.invSet B.U s := by rw [← hI]; exact hx
    exact hx'.2
  -- `U` is abelian
  have hUab : ∀ x ∈ B.U, ∀ y ∈ B.U, x * y = y * x := by
    have key : ∀ a ∈ B.U, ∀ b ∈ B.U, a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := by
      intro a ha b hb
      have h3 : s * (a * b) * s⁻¹ = (a * b)⁻¹ := hinvU _ (B.U.mul_mem ha hb)
      have h4 : s * (a * b) * s⁻¹ = a⁻¹ * b⁻¹ := by
        rw [show s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) by group,
          hinvU a ha, hinvU b hb]
      have h5 : (a * b)⁻¹ = a⁻¹ * b⁻¹ := h3.symm.trans h4
      rw [mul_inv_rev] at h5
      exact h5.symm
    intro x hx y hy
    have := key x⁻¹ (B.U.inv_mem hx) y⁻¹ (B.U.inv_mem hy)
    simpa using this
  -- `S₀` is abelian (cyclic)
  have hS0comm : ∀ z1 ∈ B.S0, ∀ z2 ∈ B.S0, z1 * z2 = z2 * z1 := by
    intro z1 hz1 z2 hz2
    obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top B.S0).mp B.S0_cyclic
    have h1 : z1 ∈ Subgroup.zpowers g := hg ▸ hz1
    have h2 : z2 ∈ Subgroup.zpowers g := hg ▸ hz2
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp h1
    obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp h2
    rw [← ha, ← hb, zpow_mul_comm]
  -- `U ∩ S₀ = ⊥`
  have hUS0bot : B.U ⊓ B.S0 = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxU, hxS0⟩ := hx
    have hoddx : Odd (orderOf x) :=
      Odd.of_dvd_nat hUodd (Subgroup.orderOf_dvd_natCard B.U hxU)
    obtain ⟨k, hk⟩ := hS0two ⟨x, hxS0⟩
    have hdvd2 : orderOf x ∣ 2 ^ k := by
      apply orderOf_dvd_iff_pow_eq_one.mpr
      have := congrArg Subtype.val hk
      simpa using this
    exact orderOf_eq_one_iff.mp (((hoddx.coprime_two_right).pow_right k).eq_one_of_dvd hdvd2)
  -- `t` is the unique involution of the cyclic group `S₀`
  have hS0uniq : ∀ a ∈ B.S0, orderOf a = 2 → a = B.t := fun a ha h2 => by
    have h := eq_of_orderOf_eq_two_of_isCyclic (H := ↥B.S0)
      (a := (⟨a, ha⟩ : ↥B.S0)) (b := (⟨B.t, B.t_mem⟩ : ↥B.S0))
      (by rw [Subgroup.orderOf_mk]; exact h2) (by rw [Subgroup.orderOf_mk]; exact B.t_order)
    exact congrArg Subtype.val h
  -- `S = S₀ ⊔ ⟨s⟩`
  have hSs : B.S0 ⊔ Subgroup.zpowers s = (B.S : Subgroup G) := by
    have h2 : B.S0 ⊔ Subgroup.zpowers s ≤ (B.S : Subgroup G) :=
      sup_le B.S0_le (Subgroup.zpowers_le.mpr hsS)
    have hcard2 : 2 * Nat.card ↥B.S0 ≤ Nat.card ↥(B.S0 ⊔ Subgroup.zpowers s) := by
      have hinj : Function.Injective (fun p : ↥B.S0 ⊕ ↥B.S0 =>
          Sum.elim (fun z : ↥B.S0 => (z : G)) (fun z : ↥B.S0 => (z : G) * s) p) := by
        rintro (z1 | z1) (z2 | z2) h
        · simp only [Sum.elim_inl] at h
          exact congrArg Sum.inl (Subtype.ext h)
        · simp only [Sum.elim_inl, Sum.elim_inr] at h
          exfalso
          apply hs0
          have hs_eq : s = (z2 : G)⁻¹ * (z1 : G) := by rw [h]; group
          rw [hs_eq]
          exact B.S0.mul_mem (B.S0.inv_mem z2.2) z1.2
        · simp only [Sum.elim_inl, Sum.elim_inr] at h
          exfalso
          apply hs0
          have hs_eq : s = (z1 : G)⁻¹ * (z2 : G) := by rw [← h]; group
          rw [hs_eq]
          exact B.S0.mul_mem (B.S0.inv_mem z1.2) z2.2
        · simp only [Sum.elim_inr] at h
          exact congrArg Sum.inr (Subtype.ext (mul_right_cancel h))
      have hmem : ∀ p : ↥B.S0 ⊕ ↥B.S0,
          Sum.elim (fun z : ↥B.S0 => (z : G)) (fun z : ↥B.S0 => (z : G) * s) p
            ∈ (B.S0 ⊔ Subgroup.zpowers s : Subgroup G) := by
        rintro (z | z)
        · exact Subgroup.mem_sup_left z.2
        · exact (B.S0 ⊔ Subgroup.zpowers s).mul_mem (Subgroup.mem_sup_left z.2)
            (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
      have hle := Nat.card_le_card_of_injective
        (fun p : ↥B.S0 ⊕ ↥B.S0 =>
          (⟨Sum.elim (fun z : ↥B.S0 => (z : G)) (fun z : ↥B.S0 => (z : G) * s) p, hmem p⟩ :
            ↥(B.S0 ⊔ Subgroup.zpowers s)))
        (fun a b hab => hinj (Subtype.ext_iff.mp hab))
      rwa [Nat.card_sum, ← two_mul] at hle
    have hcardS : Nat.card ↥(B.S : Subgroup G) = 2 * Nat.card ↥B.S0 := bSetup_card_S_eq B
    exact Subgroup.eq_of_le_of_card_ge h2 (by rw [hcardS]; exact hcard2)
  -- `C(t) = U ⊔ S`
  have hBH : Subgroup.centralizer ({B.t} : Set G) = B.U ⊔ (B.S : Subgroup G) := by
    have htC : ∀ x ∈ (B.S : Subgroup G), x * B.t = B.t * x := fun x hx =>
      ((Subgroup.mem_centralizer_iff.mp (bSetup_S_le_H B hx)) B.t (by simp)).symm
    exact (T.split G B.S n hn hdih B.t (bSetup_t_mem_S B) B.t_order htC).symm
  have hHsplit : B.U ⊔ (B.S : Subgroup G) = B.H := hBH.symm
  -- `s` inverts `S₀`
  have hsinvS0 : ∀ z ∈ B.S0, s * z * s⁻¹ = z⁻¹ :=
    bsw_dihedral_inverts_index_two n hn B.S B.S0 hdih B.S0_le B.S0_cyclic B.S0_index s hsS hs0
  -- `s ∉ K`
  have hsK : s ∉ B.U ⊔ B.S0 := by
    intro hsk
    obtain ⟨u, hu, z, hz, huz⟩ := bsw_mem_sup_of_commute hUS0comm hsk
    have hux : ∀ x ∈ B.U, u * x * u⁻¹ = x⁻¹ := by
      intro x hx
      have h1 : s * x * s⁻¹ = x⁻¹ := hinvU x hx
      have hzc : z * x * z⁻¹ = x := by
        rw [← hUS0comm x hx z hz]
        group
      rw [← huz] at h1
      rw [show (u * z) * x * (u * z)⁻¹ = u * (z * x * z⁻¹) * u⁻¹ by group, hzc] at h1
      exact h1
    have hu2 : u * u = 1 := by
      have h := hux u hu
      have h' : u = u⁻¹ := by
        have h2 : u * u * u⁻¹ = u := by group
        rw [h2] at h
        exact h
      have : u * u⁻¹ = 1 := mul_inv_cancel u
      rwa [← h'] at this
    have hu1 : u = 1 := bsw_eq_one_of_odd_order_of_sq_eq_one hUodd hu hu2
    apply hs0
    rw [← huz, hu1, one_mul]
    exact hz
  -- `K` is abelian
  have hKcomm : IsMulCommutative ↥(B.U ⊔ B.S0) := by
    refine IsMulCommutative.of_comm fun a b => ?_
    obtain ⟨u1, hu1, z1, hz1, ha⟩ := bsw_mem_sup_of_commute hUS0comm a.2
    obtain ⟨u2, hu2, z2, hz2, hb⟩ := bsw_mem_sup_of_commute hUS0comm b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha, ← hb]
    have e1 : (u1 * z1) * (u2 * z2) = (u1 * u2) * (z1 * z2) := by
      conv_lhs => rw [mul_assoc]
      conv_lhs => rw [← mul_assoc z1 u2 z2]
      conv_lhs => rw [← hUS0comm u2 hu2 z1 hz1]
      conv_lhs => rw [mul_assoc]
      conv_lhs => rw [← mul_assoc u1 u2 (z1 * z2)]
    have e2 : (u2 * z2) * (u1 * z1) = (u1 * u2) * (z1 * z2) := by
      conv_lhs => rw [mul_assoc]
      conv_lhs => rw [← mul_assoc z2 u1 z1]
      conv_lhs => rw [← hUS0comm u1 hu1 z2 hz2]
      conv_lhs => rw [mul_assoc]
      conv_lhs => rw [← mul_assoc u2 u1 (z2 * z1)]
      rw [hUab u2 hu2 u1 hu1, hS0comm z2 hz2 z1 hz1]
    rw [e1, e2]
  -- `C(t) = K ⊔ ⟨s⟩`
  have h6 : Subgroup.centralizer ({B.t} : Set G) = (B.U ⊔ B.S0) ⊔ Subgroup.zpowers s := by
    rw [hBH]
    show B.U ⊔ (B.S : Subgroup G) = (B.U ⊔ B.S0) ⊔ Subgroup.zpowers s
    rw [← hSs, sup_assoc]
  -- `s` inverts `K`
  have h7 : Work.GW2.Inverts s (B.U ⊔ B.S0) := by
    intro x hx
    obtain ⟨u, hu, z, hz, rfl⟩ := bsw_mem_sup_of_commute hUS0comm hx
    rw [show s * (u * z) * s⁻¹ = (s * u * s⁻¹) * (s * z * s⁻¹) by group, hinvU u hu,
      hsinvS0 z hz]
    rw [mul_inv_rev, ← hUS0comm u⁻¹ (B.U.inv_mem hu) z⁻¹ (B.S0.inv_mem hz)]
  -- `C_K(s) = ⟨t⟩`
  have h8 : (B.U ⊔ B.S0) ⊓ Subgroup.centralizer ({s} : Set G) = Subgroup.zpowers B.t := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxK, hxc⟩ := hx
      obtain ⟨u, hu, z, hz, hux⟩ := bsw_mem_sup_of_commute hUS0comm hxK
      have hxc' : s * (u * z) = (u * z) * s := by
        have h := (Subgroup.mem_centralizer_iff.mp hxc) s (by simp)
        rwa [← hux] at h
      have hconj : s * (u * z) * s⁻¹ = u * z := by
        rw [hxc', mul_assoc, mul_inv_cancel, mul_one]
      rw [show s * (u * z) * s⁻¹ = (s * u * s⁻¹) * (s * z * s⁻¹) by group, hinvU u hu,
        hsinvS0 z hz] at hconj
      have h1 : u⁻¹ * z⁻¹ = (u * z)⁻¹ := by
        rw [mul_inv_rev, ← hUS0comm u⁻¹ (B.U.inv_mem hu) z⁻¹ (B.S0.inv_mem hz)]
      have hsq : (u * z) * (u * z) = 1 := by
        have h2 : (u * z)⁻¹ = u * z := by rw [← h1]; exact hconj
        exact mul_eq_one_iff_eq_inv.mpr h2.symm
      have hxS0 : x ∈ B.S0 := by
        rw [← hux]
        exact bsw_mul_mem_right_of_sq_eq_one hUS0comm hUS0bot hUodd hu hz hsq
      have hx2 : x * x = 1 := by rw [← hux]; exact hsq
      rcases eq_or_ne x 1 with hx1 | hx1
      · rw [hx1]; exact Subgroup.one_mem _
      · have hxord : orderOf x = 2 := by
          have hdvd : orderOf x ∣ 2 :=
            orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using hx2)
          rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd with h | h
          · exact absurd (orderOf_eq_one_iff.mp h) hx1
          · exact h
        rw [hS0uniq x hxS0 hxord]
        exact Subgroup.mem_zpowers _
    · rintro x hx
      rw [Subgroup.mem_zpowers_iff] at hx
      obtain ⟨k, rfl⟩ := hx
      have hxK : B.t ^ k ∈ B.U ⊔ B.S0 :=
        Subgroup.mem_sup_right (B.S0.zpow_mem B.t_mem k)
      have hxC : B.t ^ k ∈ Subgroup.centralizer ({s} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        have hst : Commute B.t s :=
          (Subgroup.mem_centralizer_iff.mp (bSetup_S_le_H B hsS)) B.t (by simp)
        exact (hst.symm.zpow_right k).eq
      exact ⟨hxK, hxC⟩
  -- the TI property
  have h9 : ∀ g : G, g ∉ Subgroup.centralizer ({B.t} : Set G) →
      (B.U ⊔ B.S0) ⊓ Work.GW2.conjSub g (B.U ⊔ B.S0) = ⊥ := by
    intro g hg
    have hgH : g ∉ B.H := hg
    have hcommg : ∀ a ∈ Work.GW2.conjSub g B.U, ∀ b ∈ Work.GW2.conjSub g B.S0,
        a * b = b * a := by
      intro a ha b hb
      have ha' : g⁻¹ * a * g ∈ B.U := mem_conjSub_iff.mp ha
      have hb' : g⁻¹ * b * g ∈ B.S0 := mem_conjSub_iff.mp hb
      have h := hUS0comm (g⁻¹ * a * g) ha' (g⁻¹ * b * g) hb'
      have h' : g⁻¹ * (a * b) * g = g⁻¹ * (b * a) * g := by
        rw [show g⁻¹ * (a * b) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) by group,
          show g⁻¹ * (b * a) * g = (g⁻¹ * b * g) * (g⁻¹ * a * g) by group, h]
      exact mul_left_cancel (mul_right_cancel h')
    have hUgc_ab : ∀ a ∈ Work.GW2.conjSub g B.U, ∀ b ∈ Work.GW2.conjSub g B.U,
        a * b = b * a := by
      intro a ha b hb
      have ha' : g⁻¹ * a * g ∈ B.U := mem_conjSub_iff.mp ha
      have hb' : g⁻¹ * b * g ∈ B.U := mem_conjSub_iff.mp hb
      have h := hUab (g⁻¹ * a * g) ha' (g⁻¹ * b * g) hb'
      have h' : g⁻¹ * (a * b) * g = g⁻¹ * (b * a) * g := by
        rw [show g⁻¹ * (a * b) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) by group,
          show g⁻¹ * (b * a) * g = (g⁻¹ * b * g) * (g⁻¹ * a * g) by group, h]
      exact mul_left_cancel (mul_right_cancel h')
    have hUbot_g : Work.GW2.conjSub g B.U ⊓ Work.GW2.conjSub g B.S0 = ⊥ := by
      rw [← conjSub_inf, hUS0bot, conjSub_bot]
    have hUodd_g : Odd (Nat.card ↥(Work.GW2.conjSub g B.U)) := by
      rw [card_conjSub]; exact hUodd
    have hS0two_g : IsPGroup 2 ↥(Work.GW2.conjSub g B.S0) := by
      rw [conjSub_eq_map]
      exact IsPGroup.map (H := B.S0) hS0two (MulAut.conj g).toMonoidHom
    rw [Subgroup.eq_bot_iff_forall]
    rintro y ⟨hyK, hyKg⟩
    have hyKg2 : y ∈ Work.GW2.conjSub g B.U ⊔ Work.GW2.conjSub g B.S0 := by
      rw [← conjSub_sup]
      exact hyKg
    by_contra hy1
    by_cases heven : Even (orderOf y)
    · set w : G := y ^ (orderOf y / 2) with hwdef
      have hword : orderOf w = 2 := by
        rw [hwdef]; exact bsw_orderOf_pow_div_two_of_even hy1 heven
      have hw2 : w * w = 1 := by rw [← pow_two, ← hword]; exact pow_orderOf_eq_one w
      have hwK : w ∈ B.U ⊔ B.S0 := by
        rw [hwdef]; exact (B.U ⊔ B.S0).pow_mem hyK _
      have hwKg : w ∈ Work.GW2.conjSub g (B.U ⊔ B.S0) := by
        rw [hwdef]; exact (Work.GW2.conjSub g (B.U ⊔ B.S0)).pow_mem hyKg _
      have hwKg' : w ∈ Work.GW2.conjSub g B.U ⊔ Work.GW2.conjSub g B.S0 := by
        rw [← conjSub_sup]; exact hwKg
      have hwS0 : w ∈ B.S0 := by
        obtain ⟨u', hu', z', hz', hwz⟩ := bsw_mem_sup_of_commute hUS0comm hwK
        have hsq : (u' * z') * (u' * z') = 1 := by rw [hwz]; exact hw2
        rw [← hwz]
        exact bsw_mul_mem_right_of_sq_eq_one hUS0comm hUS0bot hUodd hu' hz' hsq
      have hwS0g : w ∈ Work.GW2.conjSub g B.S0 := by
        obtain ⟨a', ha', b', hb', hab⟩ := bsw_mem_sup_of_commute hcommg hwKg'
        have hsq : (a' * b') * (a' * b') = 1 := by rw [hab]; exact hw2
        rw [← hab]
        exact bsw_mul_mem_right_of_sq_eq_one hcommg hUbot_g hUodd_g ha' hb' hsq
      haveI hcycS0g : IsCyclic ↥(Work.GW2.conjSub g B.S0) := by
        rw [conjSub_eq_map]
        exact (MulEquiv.isCyclic
          (Subgroup.equivMapOfInjective B.S0 (MulAut.conj g).toMonoidHom
            (MulAut.conj g).injective)).mp B.S0_cyclic
      have hsem : SemiconjBy g B.t (g * B.t * g⁻¹) := by
        show g * B.t = (g * B.t * g⁻¹) * g
        group
      have hord_tg : orderOf (g * B.t * g⁻¹) = 2 :=
        (SemiconjBy.orderOf_eq g hsem).symm.trans B.t_order
      have htg_mem : g * B.t * g⁻¹ ∈ Work.GW2.conjSub g B.S0 := by
        rw [mem_conjSub_iff]
        have h : g⁻¹ * (g * B.t * g⁻¹) * g = B.t := by group
        rw [h]
        exact B.t_mem
      have hwt : w = B.t := by
        have h := eq_of_orderOf_eq_two_of_isCyclic (H := ↥B.S0)
          (a := (⟨w, hwS0⟩ : ↥B.S0)) (b := (⟨B.t, B.t_mem⟩ : ↥B.S0))
          (by rw [Subgroup.orderOf_mk]; exact hword)
          (by rw [Subgroup.orderOf_mk]; exact B.t_order)
        exact congrArg Subtype.val h
      have hwtg : w = g * B.t * g⁻¹ := by
        have h := eq_of_orderOf_eq_two_of_isCyclic (H := ↥(Work.GW2.conjSub g B.S0))
          (a := (⟨w, hwS0g⟩ : ↥(Work.GW2.conjSub g B.S0)))
          (b := (⟨g * B.t * g⁻¹, htg_mem⟩ : ↥(Work.GW2.conjSub g B.S0)))
          (by rw [Subgroup.orderOf_mk]; exact hword)
          (by rw [Subgroup.orderOf_mk]; exact hord_tg)
        exact congrArg Subtype.val h
      have htfix : B.t = g * B.t * g⁻¹ := hwt.symm.trans hwtg
      apply hgH
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      calc B.t * g = (g * B.t * g⁻¹) * g := by rw [← htfix]
        _ = g * B.t := by group
    · have hodd : Odd (orderOf y) := Nat.not_even_iff_odd.mp heven
      obtain ⟨u, hu, z, hz, hy'⟩ := bsw_mem_sup_of_commute hUS0comm hyK
      have hz1 : z = 1 := bsw_eq_one_of_mul_mem_of_odd_order (A := B.U) (C := B.S0)
        hUS0comm hUS0bot hS0two hu hz (by rw [hy']; exact hodd)
      have hyu : y = u := by rw [← hy', hz1, mul_one]
      obtain ⟨a, ha, b, hb, hy''⟩ := bsw_mem_sup_of_commute hcommg hyKg2
      have hb1 : b = 1 := bsw_eq_one_of_mul_mem_of_odd_order
        (A := Work.GW2.conjSub g B.U) (C := Work.GW2.conjSub g B.S0)
        hcommg hUbot_g hS0two_g ha hb (by rw [hy'']; exact hodd)
      have hya : y = a := by rw [← hy'', hb1, mul_one]
      have hCyU : B.U ≤ Subgroup.centralizer ({y} : Set G) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro w' hw'
        rw [Set.mem_singleton_iff] at hw'
        subst hw'
        rw [hyu]
        exact (hUab x hx u hu).symm
      have hCyUg : Work.GW2.conjSub g B.U ≤ Subgroup.centralizer ({y} : Set G) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro w' hw'
        rw [Set.mem_singleton_iff] at hw'
        subst hw'
        rw [hya]
        exact (hUgc_ab x hx a ha).symm
      have hzbot : Subgroup.zpowers y ≠ ⊥ := by
        intro h
        have : y ∈ (⊥ : Subgroup G) := by rw [← h]; exact Subgroup.mem_zpowers y
        rw [Subgroup.mem_bot] at this
        exact hy1 this
      have hNyH : Subgroup.normalizer ((Subgroup.zpowers y : Subgroup G) : Set G) ≤ B.H :=
        hNX _ hzbot (Subgroup.zpowers_le.mpr (by rw [hyu]; exact hu))
      have hUgN : Work.GW2.conjSub g B.U ≤
          Subgroup.normalizer ((Subgroup.zpowers y : Subgroup G) : Set G) := by
        rw [Subgroup.le_normalizer_iff]
        intro x hx k hk
        rw [Subgroup.mem_zpowers_iff] at hk
        obtain ⟨m, rfl⟩ := hk
        have hcomm_xy : Commute x y := ((Subgroup.mem_centralizer_iff.mp (hCyUg hx)) y
          (by simp)).symm
        rw [show x * y ^ m * x⁻¹ = (y ^ m * x) * x⁻¹ by rw [(hcomm_xy.zpow_right m).eq],
          mul_assoc, mul_inv_cancel, mul_one]
        exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) m
      have hUgH : Work.GW2.conjSub g B.U ≤ B.H := le_trans hUgN hNyH
      have hUne : B.U ≠ ⊥ := by
        intro h
        have : y ∈ (⊥ : Subgroup G) := by rw [← h, hyu]; exact hu
        rw [Subgroup.mem_bot] at this
        exact hy1 this
      have hUgU : Work.GW2.conjSub g B.U ≤ B.U := by
        intro v hv
        refine bsw_mem_left_of_mem_sup_of_odd_order B.U (B.S : Subgroup G) B.H hHsplit
          B.S.isPGroup' (bsw_oddCoreIn_subgroupOf_normal B.H) (hUgH hv) ?_
        have hdv := Subgroup.orderOf_dvd_natCard (Work.GW2.conjSub g B.U) hv
        rw [card_conjSub] at hdv
        exact Odd.of_dvd_nat hUodd hdv
      have hUgUeq : Work.GW2.conjSub g B.U = B.U :=
        Subgroup.eq_of_le_of_card_ge hUgU (by rw [card_conjSub])
      have hgN : g ∈ Subgroup.normalizer (B.U : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro h
        constructor
        · intro hh
          have hmem : g⁻¹ * (g * h * g⁻¹) * g = h := by group
          have h2 : g * h * g⁻¹ ∈ Work.GW2.conjSub g B.U :=
            mem_conjSub_iff.mpr (by rw [hmem]; exact hh)
          rwa [hUgUeq] at h2
        · intro hh
          have h2 : g * h * g⁻¹ ∈ Work.GW2.conjSub g B.U := by rwa [hUgUeq]
          have hmem : g⁻¹ * (g * h * g⁻¹) * g = h := by group
          rw [mem_conjSub_iff, hmem] at h2
          exact h2
      exact hgH (hNX B.U hUne le_rfl hgN)
  -- all involutions are conjugate
  have hno2 : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
    intro N hN h2
    haveI := hN
    rcases hctx.simple.eq_bot_or_eq_top_of_normal N with h | h
    · rw [h, Subgroup.index_bot] at h2
      have hcomm : ∀ x y : G, x * y = y * x := by
        have hsq : ∀ x : G, x * x = 1 := by
          intro x
          rcases eq_or_ne x 1 with hx1 | hx1
          · rw [hx1, one_mul]
          · have hdvd : orderOf x ∣ 2 := by
              have h := Subgroup.orderOf_dvd_natCard (⊤ : Subgroup G) (Subgroup.mem_top x)
              rwa [Subgroup.card_top, h2] at h
            rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd with hh | hh
            · exact absurd (orderOf_eq_one_iff.mp hh) hx1
            · rw [← pow_two, ← hh]; exact pow_orderOf_eq_one x
        intro x y
        have hx := hsq x
        have hy := hsq y
        have hxy := hsq (x * y)
        have h1 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_left hxy
        rw [← h1, mul_inv_rev, inv_eq_of_mul_eq_one_left hx, inv_eq_of_mul_eq_one_left hy]
      obtain ⟨a, b, hab⟩ := hctx.nonab
      exact hab (hcomm a b)
    · rw [h, Subgroup.index_top] at h2
      exact absurd h2 (by norm_num)
  have hconj := (T.fus G B.S n hn hdih hno2).1
  exact ⟨B.t_order, hsord, Subgroup.mem_sup_right B.t_mem, hsK, hKcomm, h6, h7, h8, h9,
    fun x hx => hconj x B.t hx B.t_order⟩

end Work.CORE2A
