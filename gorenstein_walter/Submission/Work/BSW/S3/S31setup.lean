/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW)

# Bender §3.1: the elementary core (`Work.BSW.S3.s31`)

Bender, *The Brauer–Suzuki–Wall theorem*, Illinois J. Math. **18** (1974) 229–235, §3.1.

Setting: `G` is finite with `BSWHyps2 G t s K` (Bender's (i)–(iv)), `H = C_G(t) = K⟨s⟩`,
and `x ∉ H^G` is inverted by `t` (`t * x * t = x⁻¹`).  Write `F = C_G(x)` for the centralizer
of `x` and `M = N_G(F)` for its normalizer.

This file collects the elementary consequences used to prove `Work.BSW.BSWS31Prop`:

* no involution commutes with `x` (`not_mem_centralizer_of_involution_of_notMem_HG`), so `|F|`
  is odd (`odd_card_centralizer_of_notMem_HG`);
* hence Bender's §3.1 (i),(iv) (`Work.BSW.Cases.S31core`): `F` is abelian, `|F| = i(x)`, and
  `C_G(a) = F` for every `a ∈ F#` (`centralizer_eq_of_mem_centralizer`);
* `t` normalizes (and inverts) `F`, `C_G(F) = F`, `F ∩ K = 1`, `F ∩ C_G(t) = 1`;
* every involution of `M` inverts `F` and acts fixed-point-freely on it.
-/
import Mathlib
import Submission.Work.BSW.S3.Defs
import Submission.Work.BSW.Cases.S31core
import Submission.Work.BSW.Api.mem_centralizer_iff
import Submission.Work.BSW.Api.normalizer_K_eq
import Submission.Work.BSW.Api.card_sup_zpowers
import Submission.Work.BSW.Basic
import Submission.Work.BSW.Vocab

namespace Work.BSW.S3

open Subgroup Work.GW2

/-- An involution `v` commuting with `x ∉ H^G` would conjugate `x` into `H = C_G(t)`
(all involutions are conjugate to `t`). -/
theorem not_mem_centralizer_of_involution_of_notMem_HG {G : Type} [Group G] [Finite G]
    {t s x : G} {K : Subgroup G} (h : BSWHyps2 G t s K) (hx : x ∉ HG t) {v : G}
    (hv : orderOf v = 2) : x ∉ Subgroup.centralizer ({v} : Set G) := by
  intro hmem
  obtain ⟨a, ha⟩ := isConj_iff.mp (Work.BSW.involutions_conj h v hv)
  have hcomm : x * v = v * x := Subgroup.mem_centralizer_singleton_iff.mp hmem
  refine hx ⟨a, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 : (a * x * a⁻¹) * (a * v * a⁻¹) = (a * v * a⁻¹) * (a * x * a⁻¹) := by
    calc (a * x * a⁻¹) * (a * v * a⁻¹) = a * (x * v) * a⁻¹ := by group
      _ = a * (v * x) * a⁻¹ := by rw [hcomm]
      _ = (a * v * a⁻¹) * (a * x * a⁻¹) := by group
  rwa [ha] at h1

/-- `F = C_G(x)` has odd order for `x ∉ H^G`: a group of even order contains an involution,
and no involution commutes with `x`. -/
theorem odd_card_centralizer_of_notMem_HG {G : Type} [Group G] [Finite G] {t s x : G}
    {K : Subgroup G} (h : BSWHyps2 G t s K) (hx : x ∉ HG t) :
    Odd (Nat.card ↥(Subgroup.centralizer ({x} : Set G))) := by
  by_contra hodd
  have heven : Even (Nat.card ↥(Subgroup.centralizer ({x} : Set G))) :=
    Nat.not_odd_iff_even.mp hodd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype ↥(Subgroup.centralizer ({x} : Set G)) := Fintype.ofFinite _
  have hdvd : 2 ∣ Fintype.card ↥(Subgroup.centralizer ({x} : Set G)) := by
    rw [← Nat.card_eq_fintype_card]
    exact even_iff_two_dvd.mp heven
  obtain ⟨v, hv⟩ :=
    exists_prime_orderOf_dvd_card (G := ↥(Subgroup.centralizer ({x} : Set G))) 2 hdvd
  have hv2 : orderOf ((v : G)) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · have h1 := pow_orderOf_eq_one v
      rw [hv] at h1
      simpa using congrArg (fun w : ↥(Subgroup.centralizer ({x} : Set G)) => (w : G)) h1
    · intro hcon
      have h1 : v = 1 := Subtype.ext hcon
      rw [h1, orderOf_one] at hv
      exact absurd hv (by norm_num)
  have hmem : x ∈ Subgroup.centralizer ({(v : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp v.2).symm
  exact not_mem_centralizer_of_involution_of_notMem_HG h hx hv2 hmem

/-- Bender §3.1(i),(iv) in the form needed below (`Work.BSW.Cases.S31core` plus the oddness of
`|C_G(x)|`). -/
theorem S31core_apply {G : Type} [Group G] [Finite G] {t s x : G} {K : Subgroup G}
    (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set G)) = Work.BSW.iFn G x ∧
      IsMulCommutative ↥(Subgroup.centralizer ({x} : Set G)) ∧
      (∀ a ∈ Subgroup.centralizer ({x} : Set G), a ≠ 1 →
        Subgroup.centralizer ({a} : Set G) = Subgroup.centralizer ({x} : Set G)) :=
  Work.BSW.Cases.S31core h (odd_card_centralizer_of_notMem_HG h hx) (Work.BSW.orderOf_t h) hinv

/-- Every non-identity element of `F = C_G(x)` has centralizer `F`. -/
theorem centralizer_eq_of_mem_centralizer {G : Type} [Group G] [Finite G] {t s x : G}
    {K : Subgroup G} (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹) :
    ∀ a ∈ Subgroup.centralizer ({x} : Set G), a ≠ 1 →
      Subgroup.centralizer ({a} : Set G) = Subgroup.centralizer ({x} : Set G) :=
  (S31core_apply h hx hinv).2.2

/-- `F = C_G(x)` is abelian. -/
theorem isMulCommutative_centralizer {G : Type} [Group G] [Finite G] {t s x : G}
    {K : Subgroup G} (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹) :
    IsMulCommutative ↥(Subgroup.centralizer ({x} : Set G)) :=
  (S31core_apply h hx hinv).2.1

/-- `i(x) = |F|`. -/
theorem card_centralizer_eq_iFn {G : Type} [Group G] [Finite G] {t s x : G}
    {K : Subgroup G} (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set G)) = Work.BSW.iFn G x :=
  (S31core_apply h hx hinv).1

/-- `t` inverts every element of `F`. -/
theorem inverts_centralizer {G : Type} [Group G] [Finite G] {t s x : G} {K : Subgroup G}
    (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹) :
    ∀ c ∈ Subgroup.centralizer ({x} : Set G), t * c * t = c⁻¹ :=
  (Work.BSW.Cases.centralizer_of_inverting_involution h (Work.BSW.orderOf_t h) hinv
    (fun v hv => not_mem_centralizer_of_involution_of_notMem_HG h hx hv)).2.1

/-- `t` normalizes `F = C_G(x)` (it inverts it). -/
theorem t_mem_normalizer_centralizer {G : Type} [Group G] [Finite G] {t s x : G}
    {K : Subgroup G} (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹) :
    t ∈ Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    have h1 : t * c * t⁻¹ = c⁻¹ := by
      rw [Work.BSW.t_inv h]
      exact inverts_centralizer h hx hinv c hc
    rw [h1]
    exact (Subgroup.centralizer ({x} : Set G)).inv_mem hc
  · intro hc
    have h2 := inverts_centralizer h hx hinv (t * c * t⁻¹) hc
    have h3 : t * (t * c * t⁻¹) * t = c := by
      calc t * (t * c * t⁻¹) * t = (t * t) * c * (t⁻¹ * t) := by group
        _ = c := by rw [Work.BSW.t_mul_self h, inv_mul_cancel, mul_one, one_mul]
    rw [← h3, h2]
    exact (Subgroup.centralizer ({x} : Set G)).inv_mem hc

/-- `t` is not centralizing `x`, so `t ∉ F`. -/
theorem t_notMem_centralizer {G : Type} [Group G] [Finite G] {t s x : G} {K : Subgroup G}
    (h : BSWHyps2 G t s K) (hx : x ∉ HG t) : t ∉ Subgroup.centralizer ({x} : Set G) := by
  intro ht
  have hxt : x ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp ht).symm
  exact hx ⟨1, by simpa using hxt⟩

/-- `x ≠ 1`. -/
theorem x_ne_one {G : Type} [Group G] [Finite G] {t s x : G} {K : Subgroup G}
    (h : BSWHyps2 G t s K) (hx : x ∉ HG t) : x ≠ 1 := by
  intro h1
  refine hx ⟨1, ?_⟩
  rw [h1]
  simp

/-- `C_G(F) = F`. -/
theorem centralizer_centralizer_eq_self {G : Type} [Group G] [Finite G] {t s x : G}
    {K : Subgroup G} (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹) :
    Subgroup.centralizer ((Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) =
      Subgroup.centralizer ({x} : Set G) := by
  refine le_antisymm ?_ ?_
  · intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxF : x ∈ Subgroup.centralizer ({x} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr rfl
    exact (Subgroup.mem_centralizer_iff.mp hc x hxF).symm
  · intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    haveI := isMulCommutative_centralizer h hx hinv
    exact congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := ↥(Subgroup.centralizer ({x} : Set G)))).comm
        ⟨b, hb⟩ ⟨a, ha⟩)

/-- `F ∩ K = 1`: a non-identity element of `K` has its centralizer inside `H = C_G(t)`, so `x`
would lie in `H^G`. -/
theorem inf_K_centralizer_eq_bot {G : Type} [Group G] [Finite G] {t s x : G}
    {K : Subgroup G} (h : BSWHyps2 G t s K) (hx : x ∉ HG t) :
    Subgroup.centralizer ({x} : Set G) ⊓ K = ⊥ := by
  rw [eq_bot_iff]
  rintro y ⟨hyF, hyK⟩
  rw [Subgroup.mem_bot]
  by_contra hy1
  have hcomm : x * y = y * x := (Subgroup.mem_centralizer_singleton_iff.mp hyF).symm
  have hxC : x ∈ Subgroup.centralizer ({t} : Set G) :=
    Work.BSW.Cases.mem_centralizer_of_commute_mem_K h hyK hy1 hcomm
  exact hx ⟨1, by simpa using hxC⟩

/-- Every element of `H ∖ K` is `k * s`, an involution. -/
theorem mul_s_sq_eq_one {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : BSWHyps2 G t s K) {k : G} (hk : k ∈ K) : (k * s) * (k * s) = 1 := by
  calc (k * s) * (k * s) = k * (s * k * s⁻¹) * (s * s) := by group
    _ = k * k⁻¹ * (s * s) := by rw [Work.BSW.inverts_s_K h k hk]
    _ = 1 := by rw [Work.BSW.s_mul_self h, mul_one, mul_inv_cancel]

/-- `k * s ≠ 1`, since `s ∉ K`. -/
theorem k_mul_s_ne_one {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : BSWHyps2 G t s K) {k : G} (hk : k ∈ K) : k * s ≠ 1 := by
  intro h1
  have h2 : s = k⁻¹ := by
    calc s = k⁻¹ * (k * s) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
      _ = k⁻¹ * 1 := by rw [h1]
      _ = k⁻¹ := mul_one _
  exact Work.BSW.s_notMem_K h (h2 ▸ K.inv_mem hk)

/-- Every element of `H ∖ K` has order `2`. -/
theorem orderOf_mul_s_eq_two {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : BSWHyps2 G t s K) {k : G} (hk : k ∈ K) : orderOf (k * s) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by simpa [pow_two] using mul_s_sq_eq_one h hk) (k_mul_s_ne_one h hk)

/-- `F ∩ C_G(t) = 1`. -/
theorem inf_centralizer_t_eq_bot {G : Type} [Group G] [Finite G] {t s x : G}
    {K : Subgroup G} (h : BSWHyps2 G t s K) (hx : x ∉ HG t) :
    Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({t} : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro y ⟨hyF, hyH⟩
  rw [Subgroup.mem_bot]
  by_contra hy1
  by_cases hyK : y ∈ K
  · have hmem : y ∈ Subgroup.centralizer ({x} : Set G) ⊓ K := ⟨hyF, hyK⟩
    rw [inf_K_centralizer_eq_bot h hx] at hmem
    exact hy1 (Subgroup.mem_bot.mp hmem)
  · have hsq : y * y = 1 := by
      rcases (Work.BSW.Api.mem_centralizer_iff h y).mp hyH with hyK' | ⟨k, hk, rfl⟩
      · exact absurd hyK' hyK
      · exact mul_s_sq_eq_one h hk
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hy2 : orderOf y = 2 := orderOf_eq_prime (by simpa [pow_two] using hsq) hy1
    have hxy : x ∈ Subgroup.centralizer ({y} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hyF).symm
    exact not_mem_centralizer_of_involution_of_notMem_HG h hx hy2 hxy

/-- Every involution of `M = N_G(F)` inverts `F` and acts fixed-point-freely on it. -/
theorem involution_mem_normalizer_inverts {G : Type} [Group G] [Finite G] {t s x : G}
    {K : Subgroup G} (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹)
    {u : G} (hu : u ∈ Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G))
    (hu2 : orderOf u = 2) :
    (∀ c ∈ Subgroup.centralizer ({x} : Set G), u * c * u⁻¹ = c⁻¹) ∧
      (∀ c ∈ Subgroup.centralizer ({x} : Set G), c * u = u * c → c = 1) := by
  have hcore := centralizer_eq_of_mem_centralizer h hx hinv
  have huu : u * u = 1 := Work.BSW.mul_self_eq_one_of_orderOf_eq_two hu2
  have hfix : ∀ c ∈ Subgroup.centralizer ({x} : Set G), u * c * u⁻¹ = c → c = 1 := by
    intro c hc hconj
    by_contra hc1
    have hc_comm : c * u = u * c := by
      calc c * u = (u * c * u⁻¹) * u := by rw [hconj]
        _ = u * c := by group
    have huCc : u ∈ Subgroup.centralizer ({c} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hc_comm.symm
    rw [hcore c hc hc1] at huCc
    have hxu : x ∈ Subgroup.centralizer ({u} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp huCc).symm
    exact not_mem_centralizer_of_involution_of_notMem_HG h hx hu2 hxu
  obtain ⟨-, hinv'⟩ := Work.BSW.Cases.K4.inverts_of_fixedPointFree_involution
      (Subgroup.centralizer ({x} : Set G)) u huu hu hfix
  exact ⟨hinv', fun c hc hcu => hfix c hc (by rw [← hcu]; group)⟩

/-- An involution does not lie in `F = C_G(x)`. -/
theorem involution_notMem_centralizer {G : Type} [Group G] [Finite G] {t s x : G}
    {K : Subgroup G} (h : BSWHyps2 G t s K) (hx : x ∉ HG t) {u : G}
    (hu2 : orderOf u = 2) : u ∉ Subgroup.centralizer ({x} : Set G) := by
  intro hu
  have hxu : x ∈ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp hu).symm
  exact not_mem_centralizer_of_involution_of_notMem_HG h hx hu2 hxu

/-- `M ∩ C_G(t) = M ∩ K`. -/
theorem inf_normalizer_centralizer_t_eq_inf_K {G : Type} [Group G] [Finite G] {t s x : G}
    {K : Subgroup G} (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹) :
    Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G) ⊓
        Subgroup.centralizer ({t} : Set G) =
      Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G) ⊓ K := by
  refine le_antisymm ?_ fun m hm => ⟨hm.1, Work.BSW.K_le_centralizer_t h hm.2⟩
  · intro m hm
    rcases (Work.BSW.Api.mem_centralizer_iff h m).mp hm.2 with hmK | ⟨k, hk, rfl⟩
    · exact ⟨hm.1, hmK⟩
    · exfalso
      have h2 : orderOf (k * s) = 2 := orderOf_mul_s_eq_two h hk
      have h3 := (involution_mem_normalizer_inverts h hx hinv hm.1 h2).1
      have ht3 := inverts_centralizer h hx hinv
      -- `t * (k * s)` centralizes `F`, hence lies in `C_G(F) = F`, hence in `F ∩ C_G(t) = 1`
      have h4 : ∀ c ∈ Subgroup.centralizer ({x} : Set G),
          (t * (k * s)) * c * (t * (k * s))⁻¹ = c := by
        intro c hc
        have key : (t * (k * s)) * c * (t * (k * s))⁻¹
            = t * ((k * s) * c * (k * s)⁻¹) * t := by
          rw [mul_inv_rev, Work.BSW.t_inv h]
          group
        rw [key, h3 c hc]
        simpa using ht3 c⁻¹ ((Subgroup.centralizer ({x} : Set G)).inv_mem hc)
      have h5 : t * (k * s) ∈ Subgroup.centralizer
          ((Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro c hc
        have hh := h4 c hc
        calc c * (t * (k * s)) = ((t * (k * s)) * c * (t * (k * s))⁻¹) * (t * (k * s)) := by
              rw [hh]
          _ = (t * (k * s)) * c := by group
      rw [centralizer_centralizer_eq_self h hx hinv] at h5
      have h6 : t * (k * s) ∈ Subgroup.centralizer ({x} : Set G) ⊓
          Subgroup.centralizer ({t} : Set G) :=
        ⟨h5, Subgroup.mul_mem _ (Work.BSW.t_mem_centralizer_t h) hm.2⟩
      rw [inf_centralizer_t_eq_bot h hx] at h6
      have h7 : t * (k * s) = 1 := Subgroup.mem_bot.mp h6
      have h7' : t = (k * s)⁻¹ := mul_eq_one_iff_eq_inv.mp h7
      have h8 : k * s = t := by
        have h9 : t⁻¹ = k * s := by rw [h7', inv_inv]
        rw [Work.BSW.t_inv h] at h9
        exact h9.symm
      refine Work.BSW.s_notMem_K h ?_
      have h10 : s = k⁻¹ * t := by
        calc s = k⁻¹ * (k * s) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
          _ = k⁻¹ * t := by rw [h8]
      rw [h10]
      exact K.mul_mem (K.inv_mem hk) (Work.BSW.t_mem_K h)

end Work.BSW.S3
