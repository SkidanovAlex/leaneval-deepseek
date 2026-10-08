/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, §3 leaves)

# BSW §3, leaf 3.6: auxiliary lemmas (`N(X)` for a nontrivial `p`-subgroup `X`)

Auxiliary lemmas for `Work.BSW.S3.s36` (Bender 1974, (3.6)).
-/
import Mathlib
import Submission.Work.BSW.S3.Defs
import Submission.Work.BSW.Basic
import Submission.Work.BSW.S3.case2Facts
import Submission.Work.BSW.Api.normalizer_K_eq
import Submission.Work.BSW.Api.card_sup_zpowers
import Submission.Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot
import Submission.Work.BSW.Cases.S31core
import Submission.OddOrder.Isaacs.Ch05_Transfer.Basic

open scoped Pointwise

namespace Work.BSW.S3

open Subgroup Work.GW2

variable {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G} {x : G} {p : ℕ}

/-! ## Conjugation helpers -/

theorem mem_conjSub {g : G} {H : Subgroup G} {a : G} :
    a ∈ conjSub g H ↔ ∃ h ∈ H, g * h * g⁻¹ = a :=
  Subgroup.mem_map

theorem mem_conjSub_iff {g : G} {H : Subgroup G} {a : G} :
    a ∈ conjSub g H ↔ g⁻¹ * a * g ∈ H := by
  rw [mem_conjSub]
  constructor
  · rintro ⟨h, hh, rfl⟩
    rwa [show g⁻¹ * (g * h * g⁻¹) * g = h from by group]
  · intro ha
    exact ⟨g⁻¹ * a * g, ha, by group⟩

theorem conjSub_mono {H K : Subgroup G} (h : H ≤ K) (g : G) : conjSub g H ≤ conjSub g K :=
  Subgroup.map_mono h

theorem conjSub_conjSub {g h : G} {H : Subgroup G} :
    conjSub g (conjSub h H) = conjSub (g * h) H := by
  ext a
  rw [mem_conjSub_iff, mem_conjSub_iff, mem_conjSub_iff]
  have : (g * h)⁻¹ * a * (g * h) = h⁻¹ * (g⁻¹ * a * g) * h := by group
  rw [this]

@[simp] theorem conjSub_one (H : Subgroup G) : conjSub 1 H = H := by
  rw [conjSub]
  have h1 : (MulAut.conj (1 : G)) = 1 := by ext y; simp
  rw [h1]
  have h2 : (MulEquiv.toMonoidHom (1 : MulAut G)) = MonoidHom.id G := by ext y; simp
  rw [h2, Subgroup.map_id]

theorem card_conjSub (g : G) (H : Subgroup G) :
    Nat.card ↥(conjSub g H) = Nat.card ↥H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem conjSub_centralizer (g y : G) :
    conjSub g (Subgroup.centralizer ({y} : Set G)) =
      Subgroup.centralizer ({g * y * g⁻¹} : Set G) := by
  ext a
  rw [mem_conjSub_iff, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h2 : g * (g⁻¹ * a * g * y) * g⁻¹ = g * (y * (g⁻¹ * a * g)) * g⁻¹ := by rw [h]
    simpa [mul_assoc] using h2
  · intro h
    have h2 : g⁻¹ * (a * (g * y * g⁻¹)) * g = g⁻¹ * ((g * y * g⁻¹) * a) * g := by rw [h]
    simpa [mul_assoc] using h2

theorem normalizer_conjSub (g : G) (H : Subgroup G) :
    Subgroup.normalizer ((conjSub g H : Subgroup G) : Set G) =
      conjSub g (Subgroup.normalizer (H : Set G)) := by
  ext v
  rw [mem_conjSub_iff, Subgroup.mem_normalizer_iff_map_conj_eq,
    Subgroup.mem_normalizer_iff_map_conj_eq]
  constructor
  · intro h
    change Work.GW2.conjSub (g⁻¹ * v * g) H = H
    change Work.GW2.conjSub v (Work.GW2.conjSub g H) = Work.GW2.conjSub g H at h
    have h3 := congrArg (Work.GW2.conjSub g⁻¹) h
    rw [conjSub_conjSub, conjSub_conjSub, conjSub_conjSub,
      show g⁻¹ * g = 1 from by group, conjSub_one] at h3
    exact h3
  · intro h
    change Work.GW2.conjSub v (Work.GW2.conjSub g H) = Work.GW2.conjSub g H
    change Work.GW2.conjSub (g⁻¹ * v * g) H = H at h
    rw [conjSub_conjSub, show v * g = g * (g⁻¹ * v * g) from by group,
      ← conjSub_conjSub, h]

/-! ## Basic facts about the bundle -/

/-- `2 ∣ |K|`. -/
theorem two_dvd_card_K (h : BSWHyps2 G t s K) : 2 ∣ Nat.card ↥K := by
  have h1 : Nat.card ↥(Subgroup.zpowers t) ∣ Nat.card ↥K :=
    Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr (Work.BSW.t_mem_K h))
  rwa [Nat.card_zpowers, Work.BSW.orderOf_t h] at h1

/-- `F = C_G(x)` has odd order. -/
theorem odd_card_centralizer_x (h : BSWCase2 G t s K x p) :
    Odd (Nat.card ↥(Subgroup.centralizer ({x} : Set G))) := by
  rw [card_centralizer_x (h := h)]
  refine Nat.Even.sub_odd (n := 1) ?_ ?_ (by norm_num)
  · have : 0 < Nat.card ↥K := Nat.card_pos
    omega
  · exact even_iff_two_dvd.mpr (two_dvd_card_K (hyps (h := h)))

/-- `t` inverts every element of `F = C_G(x)`, and `F` is abelian. -/
theorem inverts_centralizer_x (h : BSWCase2 G t s K x p) :
    (∀ a ∈ Subgroup.centralizer ({x} : Set G), t * a * t⁻¹ = a⁻¹) ∧
      IsMulCommutative ↥(Subgroup.centralizer ({x} : Set G)) := by
  have ht2 : orderOf t = 2 := Work.BSW.orderOf_t (hyps (h := h))
  have hnin : ∀ v : G, orderOf v = 2 → x ∉ Subgroup.centralizer ({v} : Set G) :=
    fun v hv => Work.BSW.Cases.not_mem_centralizer_of_involution_of_odd
      (odd_card_centralizer_x h) hv
  obtain ⟨-, hinv, hab⟩ :=
    Work.BSW.Cases.centralizer_of_inverting_involution (hyps (h := h)) ht2
      (t_inverts_x (h := h)) hnin
  refine ⟨fun a ha => ?_, hab⟩
  have hta : t * a * t = a⁻¹ := hinv a ha
  rw [Work.BSW.t_inv (hyps (h := h))]
  exact hta

/-- `t ∈ N_G(F)`. -/
theorem t_mem_normalizer_centralizer_x (h : BSWCase2 G t s K x p) :
    t ∈ Subgroup.normalizer ((Subgroup.centralizer ({x} : Set G)) : Set G) := by
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  change Work.GW2.conjSub t (Subgroup.centralizer ({x} : Set G)) = Subgroup.centralizer ({x} : Set G)
  rw [conjSub_centralizer]
  have ht : t⁻¹ = t := Work.BSW.t_inv (hyps (h := h))
  have h0 := t_inverts_x (h := h)
  rw [ht] at h0
  have htx : t * x * t⁻¹ = x⁻¹ := by rw [ht]; exact h0
  rw [htx]
  ext n
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hn
    simpa using (Commute.inv_right (show Commute n x⁻¹ from hn)).eq
  · intro hn
    simpa using (Commute.inv_right (show Commute n x from hn)).eq

/-- For `1 ≠ a ∈ F`, `C_G(a) = F`. -/
theorem centralizer_eq_of_mem_centralizer_x (h : BSWCase2 G t s K x p) {a : G}
    (ha : a ∈ Subgroup.centralizer ({x} : Set G)) (ha1 : a ≠ 1) :
    Subgroup.centralizer ({a} : Set G) = Subgroup.centralizer ({x} : Set G) :=
  (Work.BSW.Cases.S31core (hyps (h := h)) (odd_card_centralizer_x h)
    (Work.BSW.orderOf_t (hyps (h := h))) (t_inverts_x (h := h))).2.2 a ha ha1

/-- For `1 ≠ a ∈ F^g`, `C_G(a) = F^g`. -/
theorem centralizer_eq_of_mem_conjSub_centralizer_x (h : BSWCase2 G t s K x p) {g a : G}
    (ha : a ∈ conjSub g (Subgroup.centralizer ({x} : Set G))) (ha1 : a ≠ 1) :
    Subgroup.centralizer ({a} : Set G) = conjSub g (Subgroup.centralizer ({x} : Set G)) := by
  rw [conjSub_centralizer] at ha ⊢
  have hodd : Odd (Nat.card ↥(Subgroup.centralizer ({g * x * g⁻¹} : Set G))) := by
    rw [← conjSub_centralizer, card_conjSub]
    exact odd_card_centralizer_x h
  have ht2 : orderOf (g * t * g⁻¹) = 2 := by
    rw [show g * t * g⁻¹ = (MulAut.conj g) t from by rw [MulAut.conj_apply],
      MulEquiv.orderOf_eq, Work.BSW.orderOf_t (hyps (h := h))]
  have hinv : (g * t * g⁻¹)⁻¹ * (g * x * g⁻¹) * (g * t * g⁻¹) = (g * x * g⁻¹)⁻¹ := by
    have h1 := t_inverts_x (h := h)
    have := congrArg (fun z => g * z * g⁻¹) h1
    simpa [mul_assoc] using this
  exact (Work.BSW.Cases.S31core (hyps (h := h)) hodd ht2 hinv).2.2 a ha ha1

/-- `1 ≠ x`. -/
theorem x_ne_one_of_case2 (h : BSWCase2 G t s K x p) : x ≠ 1 := by
  intro h1
  refine not_mem_HG (h := h) ?_
  rw [h1, Work.BSW.HG]
  exact ⟨1, by simp⟩

/-- `t ∉ F = C_G(x)`. -/
theorem t_notMem_centralizer_x (h : BSWCase2 G t s K x p) :
    t ∉ Subgroup.centralizer ({x} : Set G) := by
  intro htF
  have hcomm : t * x = x * t := Subgroup.mem_centralizer_singleton_iff.mp htF
  have ht : t⁻¹ = t := Work.BSW.t_inv (hyps (h := h))
  have h0 := t_inverts_x (h := h)
  rw [ht] at h0
  have h1 : t * x * t⁻¹ = x⁻¹ := by rw [ht]; exact h0
  rw [hcomm, mul_assoc, mul_inv_cancel, mul_one] at h1
  have hxx : x * x = 1 := by rw [congrArg (· * x) h1, inv_mul_cancel]
  have hord : orderOf x = 2 := by
    have h2 : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hxx)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h3 | h3
    · exact absurd (orderOf_eq_one_iff.mp h3) (x_ne_one_of_case2 h)
    · exact h3
  obtain ⟨k, hk⟩ := isConj_iff.mp (Work.BSW.involutions_conj (hyps (h := h)) x hord)
  refine not_mem_HG (h := h) ?_
  rw [Work.BSW.HG]
  exact ⟨k, by rw [← hk]; exact Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

/-- `F = C_G(x)` is a TI subgroup: `F ⊓ F^g = ⊥` for `g ∉ N_G(F)`. -/
theorem centralizer_x_inf_conjSub_eq_bot (h : BSWCase2 G t s K x p) {g : G}
    (hg : g ∉ Subgroup.normalizer ((Subgroup.centralizer ({x} : Set G)) : Set G)) :
    Subgroup.centralizer ({x} : Set G) ⊓ conjSub g (Subgroup.centralizer ({x} : Set G)) =
      ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  by_contra ha1
  have h1 := centralizer_eq_of_mem_centralizer_x h ha.1 ha1
  have h2 := centralizer_eq_of_mem_conjSub_centralizer_x h ha.2 ha1
  have hsub : Subgroup.centralizer ({x} : Set G) =
      conjSub g (Subgroup.centralizer ({x} : Set G)) := h1.symm.trans h2
  exact hg (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hsub.symm)

/-! ## Odd order elements of `H = C_G(t)` and of `M = N_G(F)` -/

/-- Elements of `C_G(t)` of odd order lie in `K`. -/
theorem mem_K_of_mem_centralizer_t_of_odd (h : BSWHyps2 G t s K) {w : G}
    (hw : w ∈ Subgroup.centralizer ({t} : Set G)) (hodd : Odd (orderOf w)) : w ∈ K := by
  rcases (Work.BSW.Api.mem_centralizer_iff h w).mp hw with hK | ⟨k, hkK, hkw⟩
  · exact hK
  · rw [hkw] at hodd ⊢
    have hsk : s * k * s⁻¹ = k⁻¹ := Work.BSW.inverts_s_K h k hkK
    have hss : s * s = 1 := Work.BSW.s_mul_self h
    have hsk' : s * k = k⁻¹ * s := by
      have h := congrArg (fun z => z * s) hsk
      simpa [mul_assoc] using h
    have hpow : (k * s) * (k * s) = 1 := by
      calc (k * s) * (k * s) = k * (s * k) * s := by group
        _ = k * (k⁻¹ * s) * s := by rw [hsk']
        _ = (k * k⁻¹) * (s * s) := by group
        _ = 1 := by rw [mul_inv_cancel, hss, mul_one]
    have h2 : orderOf (k * s) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hpow)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
    · rw [orderOf_eq_one_iff.mp h1]; exact K.one_mem
    · exact absurd (h1 ▸ hodd) (by decide)

/-- Elements of `N_G(F)` (`F = C_G(x)`) of odd order lie in `F`. -/
theorem mem_centralizer_x_of_mem_normalizer_of_odd (h : BSWCase2 G t s K x p) {w : G}
    (hw : w ∈ Subgroup.normalizer ((Subgroup.centralizer ({x} : Set G)) : Set G))
    (hodd : Odd (orderOf w)) :
    w ∈ Subgroup.centralizer ({x} : Set G) := by
  by_contra hwF
  have hzt : Subgroup.zpowers t ≤
      Subgroup.normalizer ((Subgroup.centralizer ({x} : Set G)) : Set G) :=
    Subgroup.zpowers_le.mpr (t_mem_normalizer_centralizer_x (h := h))
  have hinfsup : Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.zpowers t = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    rcases Work.BSW.mem_zpowers_t (hyps (h := h)) hy.2 with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hy.1) (t_notMem_centralizer_x (h := h))
  have hcard : Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊔ Subgroup.zpowers t) =
      Nat.card ↥(Subgroup.normalizer ((Subgroup.centralizer ({x} : Set G)) : Set G)) := by
    rw [Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot hzt hinfsup,
      Nat.card_zpowers, Work.BSW.orderOf_t (hyps (h := h)),
      cardinal_normalizer_centralizer_x (h := h), card_centralizer_x (h := h),
      Nat.mul_comm]
  have hsup_le : Subgroup.centralizer ({x} : Set G) ⊔ Subgroup.zpowers t ≤
      Subgroup.normalizer ((Subgroup.centralizer ({x} : Set G)) : Set G) :=
    sup_le Subgroup.le_normalizer hzt
  have hMeq : Subgroup.centralizer ({x} : Set G) ⊔ Subgroup.zpowers t =
      Subgroup.normalizer ((Subgroup.centralizer ({x} : Set G)) : Set G) :=
    Subgroup.eq_of_le_of_card_ge hsup_le (le_of_eq hcard.symm)
  have hcoe : (↑(Subgroup.centralizer ({x} : Set G) ⊔ Subgroup.zpowers t) : Set G) =
      (Subgroup.centralizer ({x} : Set G) : Set G) * (Subgroup.zpowers t : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hzt
  have hw' : w ∈ (↑(Subgroup.centralizer ({x} : Set G) ⊔ Subgroup.zpowers t) : Set G) :=
    hMeq ▸ hw
  rw [hcoe] at hw'
  obtain ⟨f, hf, z, hz, hfz⟩ := Set.mem_mul.mp hw'
  rcases Work.BSW.mem_zpowers_t (hyps (h := h)) hz with h1 | h1
  · refine hwF ?_
    rw [← hfz, h1, mul_one]; exact hf
  · rw [h1] at hfz
    have hinv := (inverts_centralizer_x h).1
    have hft : t * f * t⁻¹ = f⁻¹ := hinv f hf
    have hft' : t * f = f⁻¹ * t := by
      have := congrArg (fun z => z * t) hft
      simpa [mul_assoc] using this
    have hpow : w * w = 1 := by
      rw [← hfz]
      calc (f * t) * (f * t) = f * (t * f) * t := by group
        _ = f * (f⁻¹ * t) * t := by rw [hft']
        _ = (f * f⁻¹) * (t * t) := by group
        _ = 1 := by rw [mul_inv_cancel, Work.BSW.t_mul_self (hyps (h := h)), mul_one]
    have h2 : orderOf w ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hpow)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h3 | h3
    · refine hwF ?_
      rw [orderOf_eq_one_iff.mp h3]; exact Subgroup.one_mem _
    · exact absurd (h3 ▸ hodd) (by decide)

/-! ## The normalizer of the cyclic subgroup generated by a conjugate of an element of `K` or `F` -/

/-- If `1 ≠ u ∈ K^g` then `N_G(⟨u⟩) ≤ C_G(t)^g`.  (Bender (3.6): an element normalizing `K` lies
in `N_G(K) = C_G(t)`, since `K` is TI.) -/
theorem normalizer_zpowers_le_of_mem_conjSub_K (h : BSWCase2 G t s K x p) {u g : G}
    (hu1 : u ≠ 1) (hu : u ∈ conjSub g K) :
    Subgroup.normalizer (Subgroup.zpowers u : Set G) ≤
      conjSub g (Subgroup.centralizer ({t} : Set G)) := by
  intro v hv
  have huK : u ∈ conjSub g K := hu
  rw [mem_conjSub_iff] at hu ⊢
  by_contra hw
  have hu₁ne : g⁻¹ * u * g ≠ 1 := by
    intro h1
    apply hu1
    calc u = g * (g⁻¹ * u * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hvu : v * u * v⁻¹ ∈ conjSub g K :=
    (Subgroup.zpowers_le.mpr huK)
      ((Subgroup.mem_normalizer_iff.mp hv u).mp (Subgroup.mem_zpowers u))
  have hwu : (g⁻¹ * v * g) * (g⁻¹ * u * g) * (g⁻¹ * v * g)⁻¹ ∈ K := by
    have h3 := mem_conjSub_iff.mp hvu
    convert h3 using 1
    group
  have hmem₂ : g⁻¹ * u * g ∈ conjSub ((g⁻¹ * v * g)⁻¹) K := by
    rw [mem_conjSub_iff]
    simpa using hwu
  have hmem : g⁻¹ * u * g ∈ K ⊓ conjSub ((g⁻¹ * v * g)⁻¹) K := ⟨hu, hmem₂⟩
  rw [Work.BSW.TI (hyps (h := h)) ((g⁻¹ * v * g)⁻¹)
      (fun hh => hw (by simpa using (Subgroup.centralizer ({t} : Set G)).inv_mem hh))] at hmem
  exact hu₁ne (Subgroup.mem_bot.mp hmem)

/-- If `1 ≠ u ∈ F^g` (`F = C_G(x)`) then `N_G(⟨u⟩) ≤ N_G(F)^g`. -/
theorem normalizer_zpowers_le_of_mem_conjSub_F (h : BSWCase2 G t s K x p) {u g : G}
    (hu1 : u ≠ 1) (hu : u ∈ conjSub g (Subgroup.centralizer ({x} : Set G))) :
    Subgroup.normalizer (Subgroup.zpowers u : Set G) ≤
      conjSub g (Subgroup.normalizer ((Subgroup.centralizer ({x} : Set G)) : Set G)) := by
  intro v hv
  have hvu : v * u * v⁻¹ ∈ conjSub g (Subgroup.centralizer ({x} : Set G)) :=
    (Subgroup.zpowers_le.mpr hu)
      ((Subgroup.mem_normalizer_iff.mp hv u).mp (Subgroup.mem_zpowers u))
  have hvune : v * u * v⁻¹ ≠ 1 := by
    intro h1
    apply hu1
    calc u = v⁻¹ * (v * u * v⁻¹) * v := by group
      _ = 1 := by rw [h1]; group
  have h1 : conjSub g (Subgroup.centralizer ({x} : Set G)) =
      Subgroup.centralizer ({u} : Set G) :=
    (centralizer_eq_of_mem_conjSub_centralizer_x h hu hu1).symm
  have h2 : Subgroup.centralizer ({v * u * v⁻¹} : Set G) =
      conjSub g (Subgroup.centralizer ({x} : Set G)) :=
    centralizer_eq_of_mem_conjSub_centralizer_x h hvu hvune
  rw [← normalizer_conjSub, Subgroup.mem_normalizer_iff_map_conj_eq]
  change Work.GW2.conjSub v (Work.GW2.conjSub g (Subgroup.centralizer ({x} : Set G))) =
    Work.GW2.conjSub g (Subgroup.centralizer ({x} : Set G))
  rw [h1, conjSub_centralizer, h2, h1]


/-! ## Descending along `H.subtype` -/

/-- Conjugation commutes with `Subgroup.map H.subtype`. -/
theorem map_subtype_conjSub {H : Subgroup G} (x : ↥H) (S : Subgroup ↥H) :
    conjSub (x : G) (S.map H.subtype) = (conjSub x S).map H.subtype := by
  rw [conjSub, conjSub, Subgroup.map_map, Subgroup.map_map]
  congr 1

/-! ## Odd order elements in conjugates of `K` and `F` -/

/-- An odd-order element of `C_G(t)^g` lies in `K^g`. -/
theorem mem_conjSub_K_of_mem_conjSub_centralizer_t (h : BSWCase2 G t s K x p) {w g : G}
    (hw : w ∈ conjSub g (Subgroup.centralizer ({t} : Set G))) (hodd : Odd (orderOf w)) :
    w ∈ conjSub g K := by
  rw [mem_conjSub_iff] at hw ⊢
  have hord : orderOf (g⁻¹ * w * g) = orderOf w := by
    rw [show g⁻¹ * w * g = (MulAut.conj g⁻¹) w from by rw [MulAut.conj_apply]; group,
      MulEquiv.orderOf_eq]
  exact mem_K_of_mem_centralizer_t_of_odd (hyps (h := h)) hw (hord ▸ hodd)

/-- An odd-order element of `N_G(F)^g` (`F = C_G(x)`) lies in `F^g`. -/
theorem mem_conjSub_centralizer_x_of_mem_conjSub_normalizer_of_odd (h : BSWCase2 G t s K x p)
    {w g : G} (hw : w ∈ conjSub g
      (Subgroup.normalizer ((Subgroup.centralizer ({x} : Set G)) : Set G)))
    (hodd : Odd (orderOf w)) :
    w ∈ conjSub g (Subgroup.centralizer ({x} : Set G)) := by
  rw [mem_conjSub_iff] at hw ⊢
  have hord : orderOf (g⁻¹ * w * g) = orderOf w := by
    rw [show g⁻¹ * w * g = (MulAut.conj g⁻¹) w from by rw [MulAut.conj_apply]; group,
      MulEquiv.orderOf_eq]
  exact mem_centralizer_x_of_mem_normalizer_of_odd h hw (hord ▸ hodd)

/-- `Odd m` and `n ∣ m` imply `Odd n`. -/
theorem Odd.of_dvd' {n m : ℕ} (hm : Odd m) (h : n ∣ m) : Odd n := by
  by_contra hn
  have hne : Even n := Nat.not_odd_iff_even.mp hn
  exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hne).trans h))

/-- An odd-order subgroup of `C_G(t)^g` lies in `K^g`. -/
theorem le_conjSub_K_of_le_conjSub_centralizer_t (h : BSWCase2 G t s K x p) {D : Subgroup G}
    {g : G} (hD : D ≤ conjSub g (Subgroup.centralizer ({t} : Set G)))
    (hodd : Odd (Nat.card ↥D)) : D ≤ conjSub g K := by
  intro w hw
  exact mem_conjSub_K_of_mem_conjSub_centralizer_t h (hD hw)
    (Odd.of_dvd' hodd (Subgroup.orderOf_dvd_natCard D hw))

/-- An odd-order subgroup of `N_G(F)^g` (`F = C_G(x)`) lies in `F^g`. -/
theorem le_conjSub_centralizer_x_of_le_conjSub_normalizer_of_odd (h : BSWCase2 G t s K x p)
    {D : Subgroup G} {g : G} (hD : D ≤ conjSub g
      (Subgroup.normalizer ((Subgroup.centralizer ({x} : Set G)) : Set G)))
    (hodd : Odd (Nat.card ↥D)) : D ≤ conjSub g (Subgroup.centralizer ({x} : Set G)) := by
  intro w hw
  exact mem_conjSub_centralizer_x_of_mem_conjSub_normalizer_of_odd h (hD hw)
    (Odd.of_dvd' hodd (Subgroup.orderOf_dvd_natCard D hw))


/-- Two elements of `H^g` commute when `H` is abelian. -/
theorem commute_of_mem_conjSub {H : Subgroup G} (hH : IsMulCommutative ↥H) {g a b : G}
    (ha : a ∈ conjSub g H) (hb : b ∈ conjSub g H) : a * b = b * a := by
  rw [mem_conjSub_iff] at ha hb
  have hc : (⟨g⁻¹ * a * g, ha⟩ : ↥H) * ⟨g⁻¹ * b * g, hb⟩ =
      ⟨g⁻¹ * b * g, hb⟩ * ⟨g⁻¹ * a * g, ha⟩ := hH.is_comm.comm _ _
  have h2 := congrArg (fun z : ↥H => (z : G)) hc
  simp only [Subgroup.coe_mul] at h2
  have h3 : g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ =
      g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [h2]
  have e1 : g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ = a * b := by group
  have e2 : g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ = b * a := by group
  rw [e1, e2] at h3
  exact h3

end Work.BSW.S3
