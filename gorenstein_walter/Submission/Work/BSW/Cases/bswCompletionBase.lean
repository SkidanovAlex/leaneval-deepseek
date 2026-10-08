/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, `Work.BSW`)

# Area BSW: Bender §3, the counting lemmas (`3.1`–`3.8`)

Bender, *The Brauer–Suzuki–Wall theorem*, Illinois J. Math. **18** (1974) 229–235, §3
(`REFS/bender1974_bsw.txt`, pp. 232–235).

Setting: `G` is finite with `BSWHyps2 G t s K` (Bender's (i)–(iv)), `k = |K| > 4`,
`H = C_G(t) = K⟨s⟩`, `I = |G : H|` is the number of involutions of `G`
(`Work.BSW.Api.ncard_involutions_eq_index`), and

`i(x) = #{u : u involution, u⁻¹ * x * u = x⁻¹}`   (`Work.BSW.iFn`).

This file develops the counting part of §3: `i(x) = k + 1` for every involution `x` (so that
`i(x) = k` is Bender's own count of involutions *different from* `x`), the double count

`∑_x i(x) = I² + I`,

and its restriction to `H`, `∑_{x ∈ H} i(x) = I + 2k² + 1`, which yields an element `x ∉ H` with
`i(x)` large.
-/
import Submission.Work.BSW.Char.iFn_t
import Submission.Work.BSW.Char.iFn_eq_card_of_mem_K
import Submission.Work.BSW.Api.ncard_involutions_eq_index
import Submission.Work.BSW.Char.ncard_coset_sK
import Submission.Work.BSW.Char.coset_sK_involutions
import Submission.Work.BSW.Char.inv_inverting_t_mem_coset
import Submission.Work.BSW.Api.mem_centralizer_iff
import Submission.Work.BSW.Api.card_sup_zpowers
import Submission.Work.BSW.Concl

open scoped BigOperators

namespace Work.BSW.Cases

open Subgroup Work.GW2

variable {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}

section Conjugation

/-- `a⁻¹ * x * a` has the same order as `x`. -/
theorem orderOf_conj_inv {G : Type} [Group G] (a x : G) :
    orderOf (a⁻¹ * x * a) = orderOf x := by
  have h : a⁻¹ * x * a = (MulAut.conj a⁻¹) x := by simp
  rw [h, MulEquiv.orderOf_eq]

/-- The conjugation relation `v⁻¹ * (a * x * a⁻¹) * v = (a * x * a⁻¹)⁻¹` is transported by
`v ↦ a⁻¹ * v * a`. -/
theorem conj_inv_iff {G : Type} [Group G] (a x v : G) :
    (v⁻¹ * (a * x * a⁻¹) * v = (a * x * a⁻¹)⁻¹) ↔
      ((a⁻¹ * v * a)⁻¹ * x * (a⁻¹ * v * a) = x⁻¹) := by
  constructor
  · intro hv
    calc (a⁻¹ * v * a)⁻¹ * x * (a⁻¹ * v * a)
        = a⁻¹ * (v⁻¹ * (a * x * a⁻¹) * v) * a := by group
      _ = a⁻¹ * (a * x * a⁻¹)⁻¹ * a := by rw [hv]
      _ = x⁻¹ := by group
  · intro hv
    calc v⁻¹ * (a * x * a⁻¹) * v
        = a * ((a⁻¹ * v * a)⁻¹ * x * (a⁻¹ * v * a)) * a⁻¹ := by group
      _ = a * x⁻¹ * a⁻¹ := by rw [hv]
      _ = (a * x * a⁻¹)⁻¹ := by group

/-- `i` is invariant under conjugation: `u ↦ a⁻¹ * u * a` is a bijection between the
involutions inverting `a * x * a⁻¹` and those inverting `x`. -/
theorem iFn_conj {G : Type} [Group G] (a x : G) :
    Work.BSW.iFn G (a * x * a⁻¹) = Work.BSW.iFn G x := by
  rw [Work.BSW.iFn, Work.BSW.iFn]
  refine Set.ncard_congr (fun u _ => a⁻¹ * u * a) ?_ ?_ ?_
  · rintro u ⟨hu2, hu⟩
    exact ⟨by rw [orderOf_conj_inv, hu2], (conj_inv_iff a x u).mp hu⟩
  · intro u v _ _ huv
    have h : a⁻¹ * u * a = a⁻¹ * v * a := huv
    calc u = a * (a⁻¹ * u * a) * a⁻¹ := by group
      _ = a * (a⁻¹ * v * a) * a⁻¹ := by rw [h]
      _ = v := by group
  · intro b hb
    refine ⟨a * b * a⁻¹, ⟨?_, ?_⟩, by group⟩
    · have h : a * b * a⁻¹ = (MulAut.conj a) b := by simp
      rw [h, MulEquiv.orderOf_eq, hb.1]
    · exact (conj_inv_iff a x (a * b * a⁻¹)).mpr (by
        calc (a⁻¹ * (a * b * a⁻¹) * a)⁻¹ * x * (a⁻¹ * (a * b * a⁻¹) * a)
            = b⁻¹ * x * b := by group
          _ = x⁻¹ := hb.2)

end Conjugation

section Involution

/-- For every involution `x` of `G`, `i(x) = |K| + 1`: all involutions are conjugate to `t`
(`BSWHyps2` (iv)), conjugation preserves `i`, and `i(t) = |K| + 1` (Bender's count of the coset
`Ks` together with `t` itself, `Work.BSW.Char.iFn_t`). -/
theorem iFn_of_orderOf_eq_two (h : BSWHyps2 G t s K) {x : G} (hx : orderOf x = 2) :
    Work.BSW.iFn G x = Nat.card K + 1 := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (Work.BSW.involutions_conj h x hx)
  have hx' : x = c⁻¹ * t * c := by rw [← hc]; group
  rw [hx']
  have hconj : Work.BSW.iFn G (c⁻¹ * t * c) = Work.BSW.iFn G t := by
    simpa only [inv_inv] using iFn_conj c⁻¹ t
  rw [hconj, Work.BSW.Char.iFn_t h]

/-- An involution inverts an involution `x` exactly when it commutes with `x`, so the involutions
of `C_G(x)` are exactly the involutions counted by `iFn G x`; there are `|K| + 1` of them. -/
theorem ncard_involutions_centralizer_of_involution (h : BSWHyps2 G t s K) {x : G}
    (hx : orderOf x = 2) :
    {u : G | orderOf u = 2 ∧ u ∈ Subgroup.centralizer ({x} : Set G)}.ncard =
      Nat.card K + 1 := by
  rw [← iFn_of_orderOf_eq_two h hx]
  congr 1
  ext u
  constructor
  · rintro ⟨hu2, hu⟩
    have hxinv : x⁻¹ = x :=
      inv_eq_of_mul_eq_one_left (Work.BSW.mul_self_eq_one_of_orderOf_eq_two hx)
    have h2 : u⁻¹ = u :=
      inv_eq_of_mul_eq_one_left (Work.BSW.mul_self_eq_one_of_orderOf_eq_two hu2)
    have huu2 : u * u = 1 := Work.BSW.mul_self_eq_one_of_orderOf_eq_two hu2
    have hcomm : u * x = x * u := by
      rw [Subgroup.mem_centralizer_iff] at hu
      exact (hu x (Set.mem_singleton x)).symm
    have h1 : u⁻¹ * x * u = x := by
      rw [h2, hcomm, mul_assoc, huu2, mul_one]
    exact ⟨hu2, by rw [h1, hxinv]⟩
  · rintro ⟨hu2, hu⟩
    refine ⟨hu2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have hxinv : x⁻¹ = x :=
      inv_eq_of_mul_eq_one_left (Work.BSW.mul_self_eq_one_of_orderOf_eq_two hx)
    have h2 : u⁻¹ = u :=
      inv_eq_of_mul_eq_one_left (Work.BSW.mul_self_eq_one_of_orderOf_eq_two hu2)
    have h3 : u * x * u = x⁻¹ := by simpa only [h2] using hu
    have h4 : u * (u * x * u) = x * u := by
      rw [← mul_assoc u (u * x) u, ← mul_assoc u u x,
        Work.BSW.mul_self_eq_one_of_orderOf_eq_two hu2, one_mul]
    calc x * u = u * (u * x * u) := h4.symm
      _ = u * x⁻¹ := by rw [h3]
      _ = u * x := by rw [hxinv]

end Involution

section SumOverG

/-- An involution `u` inverts exactly `|involutions| + 1` elements of `G`: the map `x ↦ x * u` is
a bijection between `{x | u⁻¹ * x * u = x⁻¹}` and `{v | orderOf v = 2} ∪ {1}`. -/
theorem ncard_inv_inverting_eq (u : G) (hu : orderOf u = 2) :
    {x : G | u⁻¹ * x * u = x⁻¹}.ncard = Work.BSW.invCount G + 1 := by
  classical
  have huu : u * u = 1 := Work.BSW.mul_self_eq_one_of_orderOf_eq_two hu
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_left huu
  have hbij : {x : G | u⁻¹ * x * u = x⁻¹}.ncard
      = ({v : G | orderOf v = 2} ∪ {(1 : G)} : Set G).ncard := by
    refine Set.ncard_congr (fun x _ => x * u) ?_ ?_ ?_
    · rintro x hx
      have hx' : u⁻¹ * x * u = x⁻¹ := hx
      have h2 : u * (x * u) = x⁻¹ := by
        have h := hx'
        rw [huinv] at h
        simpa only [mul_assoc] using h
      have h1 : x * u = u * x⁻¹ := by
        calc x * u = u * u * (x * u) := by rw [huu, one_mul]
          _ = u * (u * (x * u)) := by rw [mul_assoc]
          _ = u * x⁻¹ := by rw [h2]
      have hs : (x * u) * (x * u) = 1 := by
        calc (x * u) * (x * u) = x * (u * (x * u)) := by rw [mul_assoc]
          _ = x * x⁻¹ := by rw [h2]
          _ = 1 := mul_inv_cancel x
      have hdvd : orderOf (x * u) ∣ 2 :=
        orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hs)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1' | h1'
      · exact Or.inr (Set.mem_singleton_iff.mpr (orderOf_eq_one_iff.mp h1'))
      · exact Or.inl h1'
    · intro x y _ _ hxy
      exact mul_right_cancel hxy
    · rintro v (hv | hv)
      · refine ⟨v * u, ?_, by rw [mul_assoc, huu, mul_one]⟩
        have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_left
          (Work.BSW.mul_self_eq_one_of_orderOf_eq_two hv)
        have h2 : u * (v * u) * u = u * v := by
          rw [mul_assoc, mul_assoc v u u, huu, mul_one]
        show u⁻¹ * (v * u) * u = (v * u)⁻¹
        rw [huinv, mul_inv_rev, huinv, hv']
        exact h2
      · rw [Set.mem_singleton_iff] at hv
        subst hv
        refine ⟨u, ?_, by rw [huu]⟩
        show u⁻¹ * u * u = u⁻¹
        rw [huinv, huu, one_mul]
  rw [hbij, Set.ncard_union_eq (by
    rw [Set.disjoint_left]
    intro y hy hy1
    rw [Set.mem_setOf_eq] at hy
    rw [Set.mem_singleton_iff] at hy1
    rw [hy1, orderOf_one] at hy
    exact absurd hy (by norm_num)), Set.ncard_singleton]
  rfl

/-- **The double count of Bender §3**: `∑_x i(x) = I² + I` where `I` is the number of
involutions of `G`. (Each pair `(u, v)` of involutions is assigned to `x = u * v`; dual to this,
for a fixed involution `u` the assignment `x ↦ x * u` is a bijection onto the involutions
together with `1`.) -/
theorem sum_iFn (G : Type) [Group G] [Fintype G] :
    ∑ x : G, Work.BSW.iFn G x = Work.BSW.invCount G ^ 2 + Work.BSW.invCount G := by
  classical
  have hite : ∀ x : G, Work.BSW.iFn G x
      = ∑ u : G, (if (orderOf u = 2 ∧ u⁻¹ * x * u = x⁻¹) then 1 else 0) := by
    intro x
    rw [Work.BSW.iFn, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, Finset.card_filter]
  have h1 : ∑ x : G, Work.BSW.iFn G x
      = ∑ u : G, (if orderOf u = 2 then Work.BSW.invCount G + 1 else 0) := by
    calc ∑ x : G, Work.BSW.iFn G x
        = ∑ x : G, ∑ u : G, (if (orderOf u = 2 ∧ u⁻¹ * x * u = x⁻¹) then 1 else 0) := by
          exact Finset.sum_congr rfl (fun x _ => hite x)
      _ = ∑ u : G, ∑ x : G, (if (orderOf u = 2 ∧ u⁻¹ * x * u = x⁻¹) then 1 else 0) :=
          Finset.sum_comm
      _ = ∑ u : G, (if orderOf u = 2 then Work.BSW.invCount G + 1 else 0) := by
          refine Finset.sum_congr rfl (fun u _ => ?_)
          by_cases hu : orderOf u = 2
          · rw [if_pos hu]
            have hsum : ∑ x : G, (if (orderOf u = 2 ∧ u⁻¹ * x * u = x⁻¹) then 1 else 0)
                = ∑ x : G, (if (u⁻¹ * x * u = x⁻¹) then 1 else 0) := by
              refine Finset.sum_congr rfl (fun x _ => ?_)
              by_cases hP : u⁻¹ * x * u = x⁻¹
              · rw [if_pos ⟨hu, hP⟩, if_pos hP]
              · rw [if_neg (fun hc => hP hc.2), if_neg hP]
            rw [hsum, ← Finset.card_filter, ← Set.toFinset_ofPred,
              ← Set.ncard_eq_toFinset_card', ncard_inv_inverting_eq u hu]
          · rw [if_neg hu]
            refine Finset.sum_eq_zero (fun x _ => ?_)
            rw [if_neg (fun hc => hu hc.1)]
  rw [h1, ← Finset.sum_filter]
  have hcard : (Finset.univ.filter (fun u : G => orderOf u = 2)).card = Work.BSW.invCount G := by
    rw [Work.BSW.invCount, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  rw [Finset.sum_const, smul_eq_mul, hcard]
  ring

end SumOverG

section BenderS31

/-- Bender 1974, p. 232 (the remark opening §3): an element commuting with a non-identity element
of the TI-subgroup `K` lies in `C_G(t)`. -/
theorem mem_centralizer_of_commute_mem_K (h : BSWHyps2 G t s K) {y w : G} (hyK : y ∈ K)
    (hy1 : y ≠ 1) (hw : w * y = y * w) : w ∈ Subgroup.centralizer ({t} : Set G) := by
  by_contra hwC
  have hwC' : w⁻¹ ∉ Subgroup.centralizer ({t} : Set G) := fun hh =>
    hwC (by simpa using (Subgroup.centralizer ({t} : Set G)).inv_mem hh)
  have hbot := Work.BSW.TI h w⁻¹ hwC'
  have hyconj : y ∈ Work.GW2.conjSub w⁻¹ K := by
    rw [Work.GW2.conjSub, Subgroup.mem_map]
    refine ⟨y, hyK, ?_⟩
    show MulAut.conj w⁻¹ y = y
    rw [MulAut.conj_apply, inv_inv]
    calc w⁻¹ * y * w = w⁻¹ * (y * w) := by group
      _ = w⁻¹ * (w * y) := by rw [hw.symm]
      _ = y := by group
  have hmem : y ∈ K ⊓ Work.GW2.conjSub w⁻¹ K := ⟨hyK, hyconj⟩
  rw [hbot] at hmem
  exact hy1 (Subgroup.mem_bot.mp hmem)

/-- An element whose centralizer has odd order commutes with no involution. -/
theorem not_mem_centralizer_of_involution_of_odd {x v : G}
    (hodd : Odd (Nat.card ↥(Subgroup.centralizer ({x} : Set G)))) (hv : orderOf v = 2) :
    x ∉ Subgroup.centralizer ({v} : Set G) := by
  intro hx
  have hvC : v ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (hx v (Set.mem_singleton v)).symm
  have hle : Subgroup.zpowers v ≤ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.zpowers_le.mpr hvC
  have hdvd : Nat.card ↥(Subgroup.zpowers v) ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set G)) :=
    Subgroup.card_dvd_of_le hle
  rw [Nat.card_zpowers, hv] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

/-- Conjugation by `a` preserves the order. -/
theorem orderOf_conj {G : Type} [Group G] (a x : G) : orderOf (a * x * a⁻¹) = orderOf x := by
  have h : a * x * a⁻¹ = (MulAut.conj a) x := by simp
  rw [h, MulEquiv.orderOf_eq]

/-- Bender 1974, p. 232: for an involution `u = t^k` (conjugate of `t`), every non-identity
element `c` of `C_G(u) = K^k ∪ K^k s^k` is either an involution (then `c` lies in `K^k s^k`) or
satisfies `C_G(c) ≤ C_G(u)` (`c ∈ (K^k)^#`, by the TI property of `K^k`). -/
theorem isInvolution_or_centralizer_le_of_mem_centralizer (h : BSWHyps2 G t s K) {u c : G}
    (hu : orderOf u = 2) (hc : c ∈ Subgroup.centralizer ({u} : Set G)) (hc1 : c ≠ 1) :
    orderOf c = 2 ∨
      Subgroup.centralizer ({c} : Set G) ≤ Subgroup.centralizer ({u} : Set G) := by
  obtain ⟨k, hk⟩ := isConj_iff.mp (Work.BSW.involutions_conj h u hu)
  have hu_eq : u = k⁻¹ * t * k := by rw [← hk]; group
  have hcomm : u * c = c * u := by
    rw [Subgroup.mem_centralizer_iff] at hc
    exact hc u (Set.mem_singleton u)
  have hc'1 : k * c * k⁻¹ ≠ 1 := by
    intro h1
    apply hc1
    calc c = k⁻¹ * (k * c * k⁻¹) * k := by group
      _ = k⁻¹ * 1 * k := by rw [h1]
      _ = 1 := by group
  have hc' : k * c * k⁻¹ ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have h2 : c * (k⁻¹ * t * k) = (k⁻¹ * t * k) * c := by rw [← hu_eq]; exact hcomm.symm
    calc t * (k * c * k⁻¹) = k * ((k⁻¹ * t * k) * c) * k⁻¹ := by group
      _ = k * (c * (k⁻¹ * t * k)) * k⁻¹ := by rw [h2]
      _ = (k * c * k⁻¹) * t := by group
  rcases (Work.BSW.Api.mem_centralizer_iff h (k * c * k⁻¹)).mp hc' with hK | ⟨k', hk', hk''⟩
  · by_cases hc'2 : orderOf (k * c * k⁻¹) = 2
    · left
      rwa [orderOf_conj k c] at hc'2
    · right
      intro z hz
      rw [Subgroup.mem_centralizer_iff] at hz ⊢
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have hzc : c * z = z * c := hz c (Set.mem_singleton c)
      have hconj : (k * z * k⁻¹) * (k * c * k⁻¹) = (k * c * k⁻¹) * (k * z * k⁻¹) := by
        calc (k * z * k⁻¹) * (k * c * k⁻¹) = k * (z * c) * k⁻¹ := by group
          _ = k * (c * z) * k⁻¹ := by rw [hzc]
          _ = (k * c * k⁻¹) * (k * z * k⁻¹) := by group
      have hmem : k * z * k⁻¹ ∈ Subgroup.centralizer ({t} : Set G) :=
        mem_centralizer_of_commute_mem_K h hK hc'1 hconj
      rw [Subgroup.mem_centralizer_iff] at hmem
      have ht : t * (k * z * k⁻¹) = (k * z * k⁻¹) * t := hmem t (Set.mem_singleton t)
      rw [hu_eq]
      calc (k⁻¹ * t * k) * z = k⁻¹ * (t * (k * z * k⁻¹)) * k := by group
        _ = k⁻¹ * ((k * z * k⁻¹) * t) * k := by rw [ht]
        _ = z * (k⁻¹ * t * k) := by group
  · left
    have h2 : orderOf (k * c * k⁻¹) = 2 := by
      rw [hk'']
      exact ((Work.BSW.Char.coset_sK_involutions h).1 k' hk').1
    rwa [orderOf_conj k c] at h2

end BenderS31

end Work.BSW.Cases
