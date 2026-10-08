/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — Bender p. 227: "Being centralized by `S`, `P` is not conjugate to `A ∩ K`"

The §4 objects of Bender 1981 fix a prime `p`, a subgroup `P ≤ F` of order `p` and the unique
`(p,p)`-subgroup `A ≤ F · K₁` with `P ≤ A` (`Case2EightObj`).  On p. 227 Bender writes

> Being centralized by `S`, `P` is not conjugate to `A ∩ K`.

This file supplies that step.  The mathematical content is a self-contained group-theoretic
observation, `Work.CORE4.not_conjSub_eq_of_inverts_of_sylow_le_centralizer`:

> if `S` is a Sylow 2-subgroup of `G` contained in `C_G(P)`, if `s² = 1` inverts a subgroup `X`,
> and if `X` has odd order `≥ 2`, then no `G`-conjugate of `P` is `X`.

Indeed `u := g⁻¹ s g` (for a putative `P^g = X`) has order `2`, inverts `P` and normalises `P`.
But `C_G(P) ⊴ N_G(P)` has **odd index** in `N_G(P)`: `S ≤ C_G(P) ≤ N_G(P) ≤ G` with `S` Sylow
forces `2` to divide `|C_G(P)|` and `|N_G(P)|` to the same power, so `2 ∤ |N_G(P) : C_G(P)|`.
Hence the image of `u` in the quotient `N_G(P)/C_G(P)` — a group of odd order — has order dividing
both `2` and that odd number, so it is trivial: `u ∈ C_G(P)`.  Then `u` both centralizes and
inverts `P`, so every element of `P` is an involution; `|P|` odd forces `P = ⊥`, contradicting
`X = P^g ≠ ⊥`.

Applied in the §4 configuration with `X := A ⊓ D.K`: `A ⊓ D.K` has order `p` (`K` is cyclic,
`F ⊓ K = ⊥`, `A` is elementary abelian of order `p²`), it is inverted by `s = D.s` (as
`D.K = I_{U∩M}(s)`), and `S ≤ E(M) ≤ C_G(F) ≤ C_G(P)`, so the general lemma applies.

-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Case2CountAssembly
import Submission.Work.CORE4.Case2NormalizerP
import Submission.Work.CORE4.OneInvClassM
import Submission.Work.CORE4.Case2CentA
import Submission.Work.CORE4.BadCountInH

namespace Work.CORE4

open Subgroup

/-- **A conjugate of `P` is not inverted by an involution among the "2-part" of `N_G(P)`.**

Let `S` be a Sylow 2-subgroup of `G` with `S ≤ C_G(P)`, let `s² = 1` invert a subgroup `X` of odd
order `≥ 2`.  Then no conjugate of `P` equals `X`.

Proof: let `P^g = X` and `u := g⁻¹ s g`; then `u² = 1`, `u` normalises `P` and inverts `P`.  Since
`S ≤ C_G(P) ≤ N_G(P)` and `S` is Sylow in `G`, the index `|N_G(P) : C_G(P)|` is odd, so the image
of the 2-element `u` in `N_G(P)/C_G(P)` is trivial, i.e. `u ∈ C_G(P)`.  Then every `x ∈ P`
satisfies `x = u x u⁻¹ = x⁻¹`, so `x² = 1`, and `orderOf x` divides the odd number `|X| = |P|`;
hence `x = 1` for all `x`, i.e. `P = ⊥`, contradicting `X ≠ ⊥`. -/
theorem not_conjSub_eq_of_inverts_of_sylow_le_centralizer {G : Type} [Group G] [Finite G]
    (S : Sylow 2 G) {P X : Subgroup G} {s : G}
    (hS : (S : Subgroup G) ≤ Subgroup.centralizer (P : Set G))
    (hs2 : s * s = 1) (hInv : ∀ y ∈ X, s * y * s⁻¹ = y⁻¹)
    (hodd : Odd (Nat.card X)) (h2 : 2 ≤ Nat.card X) :
    ¬ ∃ g : G, Work.GW2.conjSub g P = X := by
  rintro ⟨g, hg⟩
  have hcard : Nat.card X = Nat.card P := by
    rw [← hg, Work.GW2.conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  set u : G := g⁻¹ * s * g with hu
  -- `u` is an involution
  have hu2 : u * u = 1 := by
    rw [hu]
    calc (g⁻¹ * s * g) * (g⁻¹ * s * g) = g⁻¹ * (s * s) * g := by group
      _ = 1 := by rw [hs2]; group
  -- `u` inverts `P`
  have huInv : ∀ x ∈ P, u * x * u⁻¹ = x⁻¹ := by
    intro x hx
    have hxg : g * x * g⁻¹ ∈ X := by
      rw [← hg, Work.GW2.conjSub]
      exact ⟨x, hx, rfl⟩
    have h1 := hInv (g * x * g⁻¹) hxg
    rw [hu]
    calc g⁻¹ * s * g * x * (g⁻¹ * s * g)⁻¹
        = g⁻¹ * (s * (g * x * g⁻¹) * s⁻¹) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹)⁻¹ * g := by rw [h1]
      _ = x⁻¹ := by group
  have hle1 : ∀ y ∈ P, u * y * u⁻¹ ∈ P := fun y hy => by rw [huInv y hy]; exact P.inv_mem hy
  -- hence `u` normalises `P`
  have huN : u ∈ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact fun hy => hle1 y hy
    · intro hy
      have h1 : u * (u * y * u⁻¹) * u⁻¹ = (u * y * u⁻¹)⁻¹ := huInv _ hy
      have key : u * (u * y * u⁻¹) * u⁻¹ = y := by
        calc u * (u * y * u⁻¹) * u⁻¹ = (u * u) * (y * (u⁻¹ * u⁻¹)) := by group
          _ = (u * u) * (y * (u * u)⁻¹) := by rw [← mul_inv_rev]
          _ = y := by rw [hu2]; group
      rw [key] at h1
      rw [h1]
      exact P.inv_mem hy
  -- the index `|N_G(P) : C_G(P)|` is odd
  have h2S : ¬ 2 ∣ (S : Subgroup G).index := Sylow.not_dvd_index S
  have h2H : ¬ 2 ∣ (Subgroup.centralizer (P : Set G)).index := by
    intro hd
    have hdvd : (Subgroup.centralizer (P : Set G)).index ∣ (S : Subgroup G).index :=
      ⟨_, by rw [← Subgroup.relIndex_mul_index hS, mul_comm]⟩
    exact h2S (hd.trans hdvd)
  have hHK : Subgroup.centralizer (P : Set G) ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have h2HK : ¬ 2 ∣ (Subgroup.centralizer (P : Set G)).relIndex (Subgroup.normalizer (P : Set G)) :=
    fun hd => h2H (hd.trans (Subgroup.relIndex_dvd_index_of_le hHK))
  have hoddRel : Odd ((Subgroup.centralizer (P : Set G)).relIndex (Subgroup.normalizer (P : Set G))) :=
    Nat.not_even_iff_odd.mp (fun he => h2HK he.two_dvd)
  have hNorm : ((Subgroup.centralizer (P : Set G)).subgroupOf
      (Subgroup.normalizer (P : Set G))).Normal :=
    Subgroup.normal_subgroupOf_centralizer_normalizer (P : Set G)
  haveI := hNorm
  let w : ↥(Subgroup.normalizer (P : Set G)) := ⟨u, huN⟩
  let y : ↥(Subgroup.normalizer (P : Set G)) ⧸
      (Subgroup.centralizer (P : Set G)).subgroupOf (Subgroup.normalizer (P : Set G)) :=
    QuotientGroup.mk' ((Subgroup.centralizer (P : Set G)).subgroupOf
      (Subgroup.normalizer (P : Set G))) w
  have hwval : (w : G) = u := rfl
  have hy2 : y * y = 1 := by
    have h1 : (w * w : ↥(Subgroup.normalizer (P : Set G))) = 1 := by
      ext; simpa [hwval] using hu2
    show QuotientGroup.mk' _ (w * w) = 1
    rw [h1, map_one]
  -- the image of `u` in the odd-order quotient is trivial
  have hord2 : orderOf y ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hy2)
  have hordQ : orderOf y ∣ Nat.card (↥(Subgroup.normalizer (P : Set G)) ⧸
      (Subgroup.centralizer (P : Set G)).subgroupOf (Subgroup.normalizer (P : Set G))) :=
    orderOf_dvd_natCard y
  have hNcard : Nat.card (↥(Subgroup.normalizer (P : Set G)) ⧸
      (Subgroup.centralizer (P : Set G)).subgroupOf (Subgroup.normalizer (P : Set G))) =
      (Subgroup.centralizer (P : Set G)).relIndex (Subgroup.normalizer (P : Set G)) :=
    (Subgroup.index_eq_card _).symm
  have hoddord : Odd (orderOf y) := Odd.of_dvd_nat (by rw [hNcard]; exact hoddRel) hordQ
  have hord1 : orderOf y = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hord2 with hh | hh
    · exact hh
    · rw [hh] at hoddord; exact absurd hoddord (by norm_num)
  have hy1 : y = 1 := orderOf_eq_one_iff.mp hord1
  have hmem : w ∈ (Subgroup.centralizer (P : Set G)).subgroupOf (Subgroup.normalizer (P : Set G)) :=
    (QuotientGroup.eq_one_iff _).mp hy1
  have huH : u ∈ Subgroup.centralizer (P : Set G) := by
    rw [← hwval]; exact Subgroup.mem_subgroupOf.mp hmem
  -- `u` centralizes and inverts `P`: `P` has exponent `2`, contradicting oddness
  have hex : ∃ x ∈ P, x ≠ 1 := by
    by_contra hcon
    have hcon' : ∀ x ∈ P, x = 1 := by
      intro x hx
      by_contra hx1
      exact hcon ⟨x, hx, hx1⟩
    have hbot : P = ⊥ := (Subgroup.eq_bot_iff_forall P).mpr hcon'
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  obtain ⟨x, hxP, hx1⟩ := hex
  have hxcomm : u * x = x * u := (Subgroup.mem_centralizer_iff.mp huH x hxP).symm
  have hinvx : u * x * u⁻¹ = x⁻¹ := huInv x hxP
  have hxeq : x = x⁻¹ := by
    rw [← hinvx, hxcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hx2 : x * x = 1 := by nth_rewrite 1 [hxeq]; exact inv_mul_cancel x
  have hdvd2 : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hx2)
  have hdvdN : orderOf x ∣ Nat.card ↥P := Subgroup.orderOf_dvd_natCard P hxP
  have hoddx : Odd (orderOf x) := Odd.of_dvd_nat (hcard ▸ hodd) hdvdN
  have hordx1 : orderOf x = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with hh | hh
    · exact hh
    · rw [hh] at hoddx; exact absurd hoddx (by norm_num)
  exact hx1 (orderOf_eq_one_iff.mp hordx1)

/-- **Bender 1981, §4, p. 227 (the step "`P` is not conjugate to `A ∩ K`").**

In the §4 configuration (`Case2Ctx B`, `Case2PrePlus`, `Case2SevenFacts`, `Case2EightAll`), for a
prime `p`, a subgroup `P ≤ D.F` of order `p` and the `(p,p)`-subgroup `A` of `D.F · D.K` with
`P ≤ A` (`Case2EightObj`), no `G`-conjugate of `P` equals `A ⊓ D.K`.

`A ⊓ D.K` is the unique subgroup of order `p` of the cyclic `D.K` (it has order `p` by
`eq_sup_inf_of_le_sup_of_card_eq_sq`, `D.F ⊓ D.K = ⊥` and `D.F` cyclic); it is inverted by
`s = D.s`, because `D.K = I_{U∩M}(s)`; and it has odd order because `D.K ≤ U = O(H)` has odd
order.  On the other side `P ≤ D.F ≤ C_G(E(M)) ≥ S`, so the Sylow 2-subgroup `S = B.S` lies in
`C_G(P)`.  The general lemma above then gives the claim. -/
theorem Case2PNotConjKp9 (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B), Work.GW2.Case2 B →
        Work.GW2.Case2PrePlus B h.D → Work.GW2.Case2SevenFacts B h.D →
        Work.GW2.Case2EightAll B h.D →
      ∀ (p : ℕ) (P A : Subgroup G),
        p.Prime → P ≤ h.D.F → Nat.card ↥P = p → Work.GW2.Case2EightObj h.D p P A →
        ¬ ∃ g : G, Work.GW2.conjSub g P = A ⊓ h.D.K := by
  intro G _ _ _ B h _hcase2 hplus _h7 _h8 p P A hp hPF hPcard hObj
  obtain ⟨_hpp, _hPFo, _hPcardo, hAle, hAcard, hAexp, hPleA, _huniq⟩ := hObj
  -- `S ≤ E(M) ≤ C_G(F) ≤ C_G(P)`
  obtain ⟨_pF, _kF, _hpFfact, _hpFodd, _hq7, _hiso, hSleE⟩ := h.nine
  have hFcent := Work.GW2.Case2Pre.F_cent B h.D h.pre
  have hKleE : h.D.K ≤ Work.GW2.layerIn h.D.M := Work.CORE4.K_le_layerIn_of_case2 h hplus
  have hScent : (B.S : Subgroup G) ≤ Subgroup.centralizer (P : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hFcent (hPF hy)) x (hSleE hx)).symm
  -- `A ⊓ D.K` has order `p`
  have hcomm_FK : ∀ f ∈ h.D.F, ∀ k ∈ h.D.K, f * k = k * f := by
    intro f hf k hk
    exact (Subgroup.mem_centralizer_iff.mp (hFcent hf) k (hKleE hk)).symm
  have hsupinf := Work.CORE4.eq_sup_inf_of_le_sup_of_card_eq_sq (F := h.D.F) (K := h.D.K)
    (A := A) (P := P) hp h.F_cyclic (Work.CORE4.F_inf_K_eq_bot_of_case2 h) hcomm_FK
    hAle hAcard hAexp hPleA hPF hPcard
  have hXcard : Nat.card ↥(A ⊓ h.D.K) = p := hsupinf.2
  -- `A ⊓ D.K` has odd order `≥ 2` and is inverted by `s = D.s`
  have hXodd : Odd (Nat.card ↥(A ⊓ h.D.K)) := by
    have hXleU : A ⊓ h.D.K ≤ B.U :=
      le_trans inf_le_right (Work.GW2.Case2Data.K_le_U B h.D)
    exact Odd.of_dvd_nat (Work.GW2.BenderSetup.U_odd B) (Subgroup.card_dvd_of_le hXleU)
  have h2X : 2 ≤ Nat.card ↥(A ⊓ h.D.K) := by rw [hXcard]; exact hp.two_le
  have hs2 : h.D.s * h.D.s = 1 := by
    have h1 := pow_orderOf_eq_one h.D.s
    rw [h.D.s_order] at h1
    simpa [pow_two] using h1
  have hInv : ∀ y ∈ A ⊓ h.D.K, h.D.s * y * h.D.s⁻¹ = y⁻¹ :=
    fun y hy => Work.GW2.Case2Data.K_inv B h.D y hy.2
  exact not_conjSub_eq_of_inverts_of_sylow_le_centralizer B.S hScent hs2 hInv hXodd h2X

end Work.CORE4
