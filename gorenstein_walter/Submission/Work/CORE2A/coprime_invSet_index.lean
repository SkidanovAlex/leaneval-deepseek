/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.dihedral_index_two
import Submission.Work.CORE2A.inf_U_S_eq_bot
import Submission.Work.CORE2A.mul_mem_involutionSet_H
import Submission.Work.CORE2A.exists_mul_of_mem_involutionSet_H
import Submission.Work.CORE2A.ncard_invSet_dvd_ncard_involutions_compl
import Submission.Work.CORE2A.cpi_involutions_conj
import Submission.Work.FUS.centralizer_has_normal_two_complement
import Submission.Work.CORE3.SylowDihedral

/-!
# CORE2A: `|I_U(s)|` is coprime to `[G : H]` (Bender 1981, Lemma 2.2)

Let `G` be a minimal counterexample to the Gorenstein–Walter theorem (`Work.GW2.BenderCtx G`),
`B : BenderSetup G` Bender's notation for it, `s ∈ S − S₀` an involution and
`I = I_U(s) = {u ∈ U | s u s⁻¹ = u⁻¹}` (with `U = O(H)`, `H = C_G(t)`), satisfying Bender's
Lemma 2.2 hypotheses:

* `I ◁ U`,
* `N_G(X) ≤ H` for every `1 ≠ X ≤ I`.

The main result is `Work.CORE2A.coprime_invSet_index`:

`Nat.Coprime (Nat.card I) B.H.index`.

This is exactly the coprimality hypothesis `(|K₁ ∩ K₂|, |G : H|) = 1` of Bender–Glauberman
(1981, Theorem C), which Bender's proof of Lemma 2.2 needs in order to deduce `U = I_U(s)`.

## The argument (Bender's counting argument)

Write `ℐ(K)` for the set of involutions of a subgroup `K`, and `J = |ℐ(G) ∖ ℐ(H)|`.

1. `|I| ∣ J`.  `I` acts on `ℐ(G) ∖ ℐ(H)` by conjugation; the action is free, because if
   `1 ≠ i ∈ I` fixes the involution `x`, then `x ∈ N_G(⟨i⟩) ≤ H` by hypothesis (`hNX`),
   contrary to `x ∉ H`.  (Proved in `ncard_invSet_dvd_ncard_involutions_compl`.)

2. `|ℐ(H)| = 1 + n·|I|` where `|S| = 2n` (`n ≥ 2`), and `H = U ⋊ S` because `C_G(t)` has a
   normal `2`-complement (`Work.FUS.centralizer_has_normal_two_complement`, Frobenius' normal
   `p`-complement theorem).  The involutions of `H`: the central one `t`, plus, in each of the
   `n` reflection cosets `U·(s·c)` (`c ∈ S₀`), exactly the `|I|` elements `u·(s·c)` with
   `u ∈ I_U(s)` — this uses `S₀ ≤ C_G(U)` (`hS0C`).

3. `|ℐ(G)| = [G : H]`: all involutions of `G` are conjugate (`cpi_involutions_conj`, via
   Thompson's transfer lemma), and the involutions form the conjugacy class of `t`, whose size
   is `[G : C_G(t)] = [G : H]`.

Since `ℐ(G)` is the disjoint union of `ℐ(H)` and `ℐ(G) ∖ ℐ(H)`, steps 1–3 give

`[G : H] = 1 + n·|I| + (multiple of |I|)`,

so `|I| ∣ [G : H] - 1`, whence `|I|` is coprime to `[G : H]`.
-/

namespace Work.CORE2A

open Subgroup
open Work.GW2

/-- If `a ∣ b - 1` then `a` is coprime to `b`. -/
private theorem coprime_of_dvd_sub_one {a b : ℕ} (hb : 1 ≤ b) (h : a ∣ b - 1) :
    Nat.Coprime a b := by
  show Nat.gcd a b = 1
  have h1 : Nat.gcd a b ∣ a := Nat.gcd_dvd_left a b
  have h2 : Nat.gcd a b ∣ b := Nat.gcd_dvd_right a b
  have h3 : Nat.gcd a b ∣ b - 1 := dvd_trans h1 h
  have h4 : Nat.gcd a b ∣ b - (b - 1) := Nat.dvd_sub h2 h3
  have h5 : b - (b - 1) = 1 := by omega
  rw [h5] at h4
  exact Nat.dvd_one.mp h4

/-! ## 1. `H = U ⊔ S` (`C_G(t)` splits over `O(C_G(t))`) -/

/-- **Bender 1981, p. 219**: `H = C_G(t) = O(H)·S`, stated as `B.U ⊔ B.S = B.H`.

This is `Work.GW2.CentralizerSplitProp` in Bender's notation, deduced from the fact that
`C_G(t)` has a normal `2`-complement (`Work.FUS.centralizer_has_normal_two_complement`,
Frobenius' normal `p`-complement theorem): for `t` the central involution of the dihedral Sylow
`2`-subgroup `S`, a complement `N` of the Sylow inside `C_G(t)` has odd order, hence is
contained in `O(C_G(t))`, and `N ⊔ S = C_G(t)`. -/
theorem cpi_U_sup_S_eq_H_aux {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    (n : ℕ) (hn : 2 ≤ n) (hdih : Nonempty ((B.S : Subgroup G) ≃* DihedralGroup n)) :
    (B.U : Subgroup G) ⊔ (B.S : Subgroup G) = B.H := by
  let H : Subgroup G := Subgroup.centralizer ({B.t} : Set G)
  have hSH : (B.S : Subgroup G) ≤ H := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr (fun y hy => by
      obtain rfl : y = B.t := Set.mem_singleton_iff.mp hy
      exact Subgroup.mem_centralizer_iff.mp (bSetup_S_le_H B hx) B.t (by simp))
  have htc : ∀ x ∈ (B.S : Subgroup G), x * B.t = B.t * x := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp (bSetup_S_le_H B hx) B.t (by simp)).symm
  obtain ⟨N, hNnorm, hcomp⟩ :=
    Work.FUS.centralizer_has_normal_two_complement (G := G) B.S n hn hdih B.t
      (bSetup_t_mem_S B) B.t_order htc
  haveI : N.Normal := hNnorm
  let P : Sylow 2 ↥H := B.S.subtype hSH
  have hPcarrier : (P : Subgroup ↥H) = (B.S : Subgroup G).subgroupOf H :=
    Sylow.coe_subtype (P := B.S) (N := H) hSH
  have hcompP : N.IsComplement' (P : Subgroup ↥H) := hcomp P
  have hsup : N ⊔ (P : Subgroup ↥H) = ⊤ := hcompP.sup_eq_top
  -- `N` has odd order: its cardinality is the index of the Sylow `P`, which is odd
  have hNodd : Odd (Nat.card N) := by
    have hrel : (P : Subgroup ↥H).index = (B.S : Subgroup G).relIndex H := by
      rw [hPcarrier]
      rfl
    have hidx : (P : Subgroup ↥H).index = Nat.card N := hcompP.index_eq_card
    rw [hrel] at hidx
    rw [← hidx]
    have hmul : (B.S : Subgroup G).relIndex H * H.index = (B.S : Subgroup G).index :=
      Subgroup.relIndex_mul_index hSH
    have hSodd : Odd (B.S : Subgroup G).index := by
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      exact B.S.not_dvd_index
    rcases hSodd with ⟨m, hm⟩
    rcases Nat.even_or_odd ((B.S : Subgroup G).relIndex H) with hev | hodd
    · exfalso
      rw [even_iff_two_dvd] at hev
      have h2 : (2 : ℕ) ∣ (B.S : Subgroup G).relIndex H * H.index :=
        dvd_mul_of_dvd_left hev _
      rw [hmul, hm] at h2
      omega
    · exact hodd
  -- hence `N ≤ O(H)`
  have hNle : N ≤ Work.GW2.oddCore ↥H :=
    Subgroup.normal_le_normalCore.mpr (le_sSup ⟨hNnorm, hNodd⟩)
  have hPmap : (P : Subgroup ↥H).map H.subtype = (B.S : Subgroup G) := by
    rw [hPcarrier]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hSH hx⟩, hx, rfl⟩
  have hmap_eq : Work.GW2.oddCoreIn H ⊔ (B.S : Subgroup G)
      = (Work.GW2.oddCore ↥H ⊔ (P : Subgroup ↥H)).map H.subtype := by
    simp only [Work.GW2.oddCoreIn]
    rw [Subgroup.map_sup (Work.GW2.oddCore ↥H) (P : Subgroup ↥H) H.subtype, hPmap]
  have hsup' : Work.GW2.oddCore ↥H ⊔ (P : Subgroup ↥H) = ⊤ := by
    refine le_antisymm le_top ?_
    calc (⊤ : Subgroup ↥H) = N ⊔ (P : Subgroup ↥H) := hsup.symm
      _ ≤ Work.GW2.oddCore ↥H ⊔ (P : Subgroup ↥H) := sup_le_sup_right hNle _
  have htop2 : (⊤ : Subgroup ↥H).map H.subtype = H := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
  have hfinal : Work.GW2.oddCoreIn H ⊔ (B.S : Subgroup G) = H := by
    rw [hmap_eq, hsup', htop2]
  exact hfinal

/-! ## 2. The involutions of `H` other than `t` are `u·(s·c)` with `u ∈ I_U(s)` -/

/-- Surjectivity statement behind the count of the involutions of `H`: if `H = U ⊔ S`, then every
involution `h ∈ H`, `h ≠ t`, has the shape `u·(s·c)` with `c ∈ S₀` and `u ∈ I_U(s)`.

This is `Work.CORE2A.exists_mul_of_mem_involutionSet_H` with the identity `H = U ⊔ S` (there
obtained from the toolkit's `T.split`) taken as a hypothesis. -/
theorem cpi_exists_mul_of_mem_involutionSet_H {G : Type} [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) (n : ℕ) (hn : 2 ≤ n)
    (hdih : Nonempty ((B.S : Subgroup G) ≃* DihedralGroup n))
    (hUS : (B.U : Subgroup G) ⊔ (B.S : Subgroup G) = B.H)
    {s : G} (hsS : s ∈ (B.S : Subgroup G)) (hs0 : s ∉ B.S0)
    (hS0C : B.S0 ≤ Subgroup.centralizer (B.U : Set G))
    {h : G} (hh : h ∈ Work.GW2.involutionSet B.H) (hne : h ≠ B.t) :
    ∃ c ∈ B.S0, ∃ u ∈ Work.GW2.invSet B.U s, u * (s * c) = h := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- `U ◁ H`, hence `H ≤ N_G(U)`; and `U` has odd order.
  have hUnorm : (B.U.subgroupOf B.H).Normal := subgroupOf_oddCoreIn_normal B.H
  have hHN : B.H ≤ Subgroup.normalizer (B.U : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (bSetup_U_le_H B)).mp hUnorm
  have hUodd : Odd (Nat.card B.U) := bSetup_U_odd B
  -- `U ⊓ S₀ = 1` (coprime orders).
  have hUS0 : B.U ⊓ B.S0 = ⊥ := by
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (B.S.isPGroup'.to_le B.S0_le)
    rw [hk]
    exact (hUodd.coprime_two_right).pow_right k
  -- Decompose `h = u * y` with `u ∈ U`, `y ∈ S`.
  obtain ⟨u, hu, y, hy, huy⟩ :=
    mem_sup_decomposition (A := B.U) (B := B.S) (K := B.H) (bSetup_U_le_H B) (bSetup_S_le_H B)
      hUnorm hUS h hh.1
  -- `h` is an involution.
  have hh2 : h * h = 1 := by
    have h2 : h ^ 2 = 1 := by rw [← hh.2]; exact pow_orderOf_eq_one h
    simpa [pow_two] using h2
  by_cases hy0 : y ∈ B.S0
  · -- Case `y ∈ S₀`: then `u = 1` and `h = y = t`, contradicting `h ≠ t`.
    have hcent : u * y = y * u := Subgroup.mem_centralizer_iff.mp (hS0C hy0) u hu
    have hmul : (u * y) * (u * y) = u ^ 2 * y ^ 2 := by
      calc (u * y) * (u * y) = u * (y * u) * y := by group
        _ = u * (u * y) * y := by rw [← hcent]
        _ = u ^ 2 * y ^ 2 := by rw [pow_two, pow_two]; group
    have hsq : u ^ 2 * y ^ 2 = 1 := by
      rw [← hmul, huy]; exact hh2
    have hmem : u ^ 2 ∈ B.U ⊓ B.S0 :=
      ⟨B.U.pow_mem hu 2, by
        rw [eq_inv_of_mul_eq_one_left hsq]
        exact B.S0.inv_mem (B.S0.pow_mem hy0 2)⟩
    have hu2 : u ^ 2 = 1 := by simpa [hUS0] using hmem
    have hu1 : u = 1 := by
      have hdvd2 : orderOf u ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hu2
      have hdvdU : orderOf u ∣ Nat.card B.U := Subgroup.orderOf_dvd_natCard B.U hu
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd2 with h | h
      · exact orderOf_eq_one_iff.mp h
      · exfalso
        rw [h] at hdvdU
        exact (Nat.not_even_iff_odd.mpr hUodd) (even_iff_two_dvd.mpr hdvdU)
    have hyh : y = h := by rw [← huy, hu1, one_mul]
    have hyt : y = B.t := by
      haveI : IsCyclic ↥B.S0 := B.S0_cyclic
      have h1 : (⟨y, hy0⟩ : ↥B.S0) = ⟨B.t, B.t_mem⟩ :=
        eq_of_orderOf_eq_two_of_isCyclic (a := (⟨y, hy0⟩ : ↥B.S0)) (b := ⟨B.t, B.t_mem⟩)
          (by rw [Subgroup.orderOf_mk, hyh]; exact hh.2)
          (by rw [Subgroup.orderOf_mk]; exact B.t_order)
      exact congrArg Subtype.val h1
    exact absurd (hyh ▸ hyt) hne
  · -- Case `y ∉ S₀`: `y = s * c`, and involutivity of `h` forces `s * u * s⁻¹ = u⁻¹`.
    obtain ⟨c, hc, hyc⟩ :=
      exists_mul_of_notMem_relIndex_two (S := (B.S : Subgroup G)) (S0 := B.S0) B.S0_index
        hsS hs0 hy hy0
    -- `y ^ 2 ∈ S₀` because `S₀` has index two in `S`.
    have hy2 : y ^ 2 ∈ B.S0 := by
      have hidx' : (B.S0.subgroupOf (B.S : Subgroup G)).index = 2 := B.S0_index
      have h := Subgroup.sq_mem_of_index_two hidx' (⟨y, hy⟩ : ↥(B.S : Subgroup G))
      exact Subgroup.mem_subgroupOf.mp h
    -- `y` normalizes `U` (as an element of `S ≤ H`).
    have hyuy : y * u * y⁻¹ ∈ B.U :=
      (Subgroup.mem_normalizer_iff.mp (hHN (bSetup_S_le_H B hy)) u).mp hu
    -- The key computation: `u * y * u = y⁻¹`, hence `u * (y * u * y⁻¹) = y⁻²`.
    have hUU : u * (y * u * y⁻¹) = (y ^ 2)⁻¹ := by
      have h1 : (u * y * u) * y = 1 := by
        have h2 := hh2
        rw [← huy] at h2
        calc (u * y * u) * y = (u * y) * (u * y) := by group
          _ = 1 := h2
      have h2 : u * y * u = y⁻¹ := by
        calc u * y * u = (u * y * u) * 1 := (mul_one _).symm
          _ = (u * y * u) * (y * y⁻¹) := by rw [mul_inv_cancel]
          _ = ((u * y * u) * y) * y⁻¹ := by group
          _ = 1 * y⁻¹ := by rw [h1]
          _ = y⁻¹ := one_mul _
      calc u * (y * u * y⁻¹) = (u * y * u) * y⁻¹ := by group
        _ = y⁻¹ * y⁻¹ := by rw [h2]
        _ = (y ^ 2)⁻¹ := by rw [pow_two, mul_inv_rev]
    -- Hence `y * u * y⁻¹ = u⁻¹`, since `U ⊓ S₀ = 1`.
    have hyuy1 : y * u * y⁻¹ = u⁻¹ := by
      have hmem : u * (y * u * y⁻¹) ∈ B.U ⊓ B.S0 :=
        ⟨B.U.mul_mem hu hyuy, by rw [hUU]; exact B.S0.inv_mem hy2⟩
      have h1 : u * (y * u * y⁻¹) = 1 := by simpa [hUS0] using hmem
      calc y * u * y⁻¹ = 1 * (y * u * y⁻¹) := (one_mul _).symm
        _ = (u⁻¹ * u) * (y * u * y⁻¹) := by rw [inv_mul_cancel]
        _ = u⁻¹ * (u * (y * u * y⁻¹)) := by group
        _ = u⁻¹ * 1 := by rw [h1]
        _ = u⁻¹ := mul_one _
    -- `c ∈ S₀` centralizes `U`, so `s * u * s⁻¹ = (s * c) * u * (s * c)⁻¹ = u⁻¹`.
    have hcu : c * u * c⁻¹ = u := by
      rw [← Subgroup.mem_centralizer_iff.mp (hS0C hc) u hu, mul_inv_cancel_right]
    have hsu : s * u * s⁻¹ = u⁻¹ := by
      have hstep : (s * c) * u * (s * c)⁻¹ = s * u * s⁻¹ := by
        calc (s * c) * u * (s * c)⁻¹ = s * (c * u * c⁻¹) * s⁻¹ := by rw [mul_inv_rev]; group
          _ = s * u * s⁻¹ := by rw [hcu]
      calc s * u * s⁻¹ = (s * c) * u * (s * c)⁻¹ := hstep.symm
        _ = u⁻¹ := by rw [← hyc]; exact hyuy1
    exact ⟨c, hc, u, ⟨hu, hsu⟩, by rw [← hyc]; exact huy⟩

/-! ## 3. The number of involutions of `H` -/

/-- **The number of involutions of `H = C_G(t)`** (Bender 1981 §2, p. 219):
`|I(H)| = 1 + n·|I_U(s)|` when `H = U ⊔ S` and `S ≃* DihedralGroup n`.

This is the statement of `Work.CORE2A.ncard_involutionSet_H`, with the splitting `H = U ⊔ S`
(obtained there from the toolkit) taken as a hypothesis `hUS`, and with `(invSet B.U s).ncard`
replaced by `Nat.card I` for a subgroup `I` with underlying set `invSet B.U s`. -/
theorem cpi_involutionSet_H_card_aux {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    (n : ℕ) (hn : 2 ≤ n) (hdih : Nonempty ((B.S : Subgroup G) ≃* DihedralGroup n))
    (hUS : (B.U : Subgroup G) ⊔ (B.S : Subgroup G) = B.H)
    {s : G} (hsS : s ∈ (B.S : Subgroup G)) (hs0 : s ∉ B.S0)
    (I : Subgroup G) (hI : (I : Set G) = Work.GW2.invSet B.U s)
    (hS0C : B.S0 ≤ Subgroup.centralizer (B.U : Set G)) :
    (Work.GW2.involutionSet B.H).ncard = 1 + n * Nat.card I := by
  classical
  -- ## 0.  Numerical facts: `|S| = 2n`, `|S₀| = n`, `U ⊓ S = ⊥`.
  have hUS' : B.U ⊓ (B.S : Subgroup G) = ⊥ := inf_U_S_eq_bot B
  have hdih' : Nonempty ((B.S : Subgroup G) ≃* DihedralGroup n) := hdih
  obtain ⟨e⟩ := hdih'
  have hcardS : Nat.card (B.S : Subgroup G) = 2 * n := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hcardS0 : Nat.card B.S0 = n := by
    have h := Subgroup.relIndex_mul_card B.S0 (B.S : Subgroup G)
    rw [B.S0_index, inf_eq_left.mpr B.S0_le, hcardS] at h
    exact Nat.mul_left_cancel (by norm_num : (0 : ℕ) < 2) h
  have hS0ncard : (B.S0 : Set G).ncard = n := by
    rw [← Nat.card_coe_set_eq (B.S0 : Set G)]
    exact hcardS0
  -- ## 1.  `I(H) = insert t J` where `J` is the set of involutions of `H` different from `t`.
  let J : Set G := {h : G | h ∈ Work.GW2.involutionSet B.H ∧ h ≠ B.t}
  have ht_mem : B.t ∈ Work.GW2.involutionSet B.H := ⟨bSetup_t_mem_H B, B.t_order⟩
  have ht_notMem : B.t ∉ J := fun h => h.2 rfl
  have hInv : Work.GW2.involutionSet B.H = insert B.t J := by
    ext x
    rw [Set.mem_insert_iff]
    exact ⟨fun hx => if hxt : x = B.t then Or.inl hxt else Or.inr ⟨hx, hxt⟩,
      fun hx => hx.elim (fun h => h ▸ ht_mem) (fun h => h.1)⟩
  have hInv_card : (Work.GW2.involutionSet B.H).ncard = J.ncard + 1 := by
    rw [hInv, Set.ncard_insert_of_notMem ht_notMem]
  -- ## 2.  The bijection `S₀ × I_U(s) ≃ J`, `(c, u) ↦ u · (s c)`.
  have hI' : ∀ x : G, x ∈ (I : Set G) ↔ x ∈ Work.GW2.invSet B.U s := fun x => by rw [hI]
  have hbij : ((B.S0 : Set G) ×ˢ (I : Set G)).ncard = J.ncard := by
    refine Set.ncard_congr (fun p _ => p.2 * (s * p.1)) ?_ ?_ ?_
    · -- the values are involutions of `H` different from `t`
      rintro ⟨c, u⟩ hp
      exact mul_mem_involutionSet_H B n hn hdih hsS hs0 hS0C hp.1 ((hI' u).mp hp.2)
    · -- injectivity on `S₀ × I_U(s)`
      rintro ⟨c₁, u₁⟩ ⟨c₂, u₂⟩ hp₁ hp₂ h
      have hc₁ : c₁ ∈ B.S0 := hp₁.1
      have hc₂ : c₂ ∈ B.S0 := hp₂.1
      have hu₁ : u₁ ∈ B.U := ((hI' u₁).mp hp₁.2).1
      have hu₂ : u₂ ∈ B.U := ((hI' u₂).mp hp₂.2).1
      -- from `u₁ (s c₁) = u₂ (s c₂)` we get `u₂⁻¹ u₁ = (s c₂) (s c₁)⁻¹ ∈ U ⊓ S = ⊥`
      have key : u₂⁻¹ * u₁ = (s * c₂) * (s * c₁)⁻¹ := by
        have h' := congrArg (fun x => u₂⁻¹ * x * (s * c₁)⁻¹) h
        simpa [mul_assoc] using h'
      have hm1 : s * c₂ ∈ (B.S : Subgroup G) := (B.S).mul_mem hsS (B.S0_le hc₂)
      have hm2 : s * c₁ ∈ (B.S : Subgroup G) := (B.S).mul_mem hsS (B.S0_le hc₁)
      have hmemS : (s * c₂) * (s * c₁)⁻¹ ∈ (B.S : Subgroup G) :=
        (B.S).mul_mem hm1 ((B.S).inv_mem hm2)
      have hmemU : u₂⁻¹ * u₁ ∈ B.U := B.U.mul_mem (B.U.inv_mem hu₂) hu₁
      have hmemS' : u₂⁻¹ * u₁ ∈ (B.S : Subgroup G) := by
        rw [key]; exact hmemS
      have hone : u₂⁻¹ * u₁ = 1 := by
        have hbot : u₂⁻¹ * u₁ ∈ B.U ⊓ (B.S : Subgroup G) := ⟨hmemU, hmemS'⟩
        rw [hUS'] at hbot
        exact Subgroup.mem_bot.mp hbot
      have hueq : u₁ = u₂ := by
        have h2 : u₂ * (u₂⁻¹ * u₁) = u₂ * 1 := by rw [hone]
        simpa [mul_assoc] using h2
      have hceq : c₁ = c₂ := by
        have hy : s * c₁ = s * c₂ := by
          rw [hueq] at h
          exact mul_left_cancel h
        exact mul_left_cancel hy
      exact Prod.ext hceq hueq
    · -- surjectivity onto `J`
      rintro h hh
      obtain ⟨c, hc, u, hu, heq⟩ :=
        cpi_exists_mul_of_mem_involutionSet_H B n hn hdih hUS hsS hs0 hS0C hh.1 hh.2
      exact ⟨(c, u), ⟨hc, (hI' u).mpr hu⟩, heq⟩
  -- ## 3.  Counting.
  have hprod : ((B.S0 : Set G) ×ˢ (I : Set G)).ncard = n * Nat.card I := by
    rw [Set.ncard_prod, hS0ncard]
    rfl
  have hJcard : J.ncard = n * Nat.card I := by
    rw [← hbij, hprod]
  rw [hInv_card, hJcard]
  omega

/-! ## 4. The number of involutions of `G` is `[G : H]` -/

/-- A simple group of order `≠ 2` has no normal subgroup of index `2`. -/
private theorem no_normal_index_two {G : Type} [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (hcard : Nat.card G ≠ 2) : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
  intro N hN hIdx
  have hbot : N ≠ ⊥ := by
    intro h
    rw [h, Subgroup.index_bot] at hIdx
    exact hcard hIdx
  have htop : N ≠ ⊤ := by
    intro h
    rw [h, Subgroup.index_top] at hIdx
    omega
  haveI := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact hbot h
  · exact htop h

/-- The Sylow `2`-subgroup `S` of a minimal counterexample has order `2n ≥ 4`, hence `|G| ≠ 2`. -/
private theorem card_G_ne_two {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    (n : ℕ) (hn : 2 ≤ n) (hdih : Nonempty ((B.S : Subgroup G) ≃* DihedralGroup n)) :
    Nat.card G ≠ 2 := by
  obtain ⟨e⟩ := hdih
  have hcardS : Nat.card (B.S : Subgroup G) = 2 * n := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hle : Nat.card (B.S : Subgroup G) ≤ Nat.card G := Subgroup.card_le_card_group _
  rw [hcardS] at hle
  omega

/-- Bender 1981 §2: the involutions of `G` are precisely the conjugates of `t`, hence number
`[G : C_G(t)] = [G : H]`.  Uses that all involutions of `G` are conjugate
(`cpi_involutions_conj`, Thompson's transfer lemma) and that `G` has no normal subgroup of
index two. -/
theorem cpi_ncard_involutions_eq_index {G : Type} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G) (B : Work.GW2.BenderSetup G) (n : ℕ) (hn : 2 ≤ n)
    (hdih : Nonempty ((B.S : Subgroup G) ≃* DihedralGroup n)) :
    {x : G | orderOf x = 2}.ncard = B.H.index := by
  have hNoIndex2 := no_normal_index_two hsimple (card_G_ne_two B n hn hdih)
  have hfus : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y :=
    cpi_involutions_conj B.S n hn hdih hNoIndex2
  have hset : {x : G | orderOf x = 2} = conjugatesOf B.t := by
    ext x
    constructor
    · intro hx
      exact (hfus x B.t hx B.t_order).symm
    · intro hx
      change IsConj B.t x at hx
      rw [isConj_iff] at hx
      obtain ⟨c, hc⟩ := hx
      change orderOf x = 2
      rw [← hc, ← MulAut.conj_apply c B.t, MulEquiv.orderOf_eq (MulAut.conj c) B.t, B.t_order]
  rw [hset, ← Subgroup.index_centralizer_eq_ncard B.t]

/-! ## 5. The coprimality -/

theorem coprime_invSet_index {G : Type} [Group G] [Finite G] (hFT : Work.GW2.FeitThompsonProp)
    (hctx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (s : G)
    (hsS : s ∈ (B.S : Subgroup G)) (hs0 : s ∉ B.S0) (hsord : orderOf s = 2)
    (I : Subgroup G) (hI : (I : Set G) = Work.GW2.invSet B.U s)
    (hInorm : (I.subgroupOf B.U).Normal)
    (hNX : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ I → Subgroup.normalizer (X : Set G) ≤ B.H)
    (hS0C : B.S0 ≤ Subgroup.centralizer (B.U : Set G)) :
    Nat.Coprime (Nat.card I) (B.H).index := by
  classical
  -- `S` is dihedral of order `2n`, `n ≥ 2`.
  obtain ⟨n, hn, hdih⟩ := Work.CORE3.SylowDihedral G hctx B
  -- `H = U ⊔ S`, the count of the involutions of `H`, and the count of those outside `H`.
  have hUS : (B.U : Subgroup G) ⊔ (B.S : Subgroup G) = B.H := cpi_U_sup_S_eq_H_aux B n hn hdih
  have hcardH := cpi_involutionSet_H_card_aux B n hn hdih hUS hsS hs0 I hI hS0C
  have hdvd := ncard_invSet_dvd_ncard_involutions_compl B I hI hNX
  -- `[G : H]` is the total number of involutions of `G`.
  have hidx := cpi_ncard_involutions_eq_index hctx.simple B n hn hdih
  -- Split the involutions of `G` into those inside and those outside `H`.
  have hsplit : ({x : G | orderOf x = 2} : Set G).ncard
      = (Work.GW2.involutionSet B.H).ncard + {x : G | orderOf x = 2 ∧ x ∉ B.H}.ncard := by
    have h := Set.ncard_inter_add_ncard_sdiff_eq_ncard (s := {x : G | orderOf x = 2})
      (t := Work.GW2.involutionSet B.H)
    have h1 : ({x : G | orderOf x = 2} ∩ Work.GW2.involutionSet B.H : Set G)
        = Work.GW2.involutionSet B.H := by
      ext x
      exact ⟨fun hx => hx.2, fun hx => ⟨hx.2, hx⟩⟩
    have h2 : ({x : G | orderOf x = 2} \ Work.GW2.involutionSet B.H : Set G)
        = {x : G | orderOf x = 2 ∧ x ∉ B.H} := by
      ext x
      constructor
      · rintro ⟨hx2, hxnot⟩
        exact ⟨hx2, fun hxH => hxnot ⟨hxH, hx2⟩⟩
      · rintro ⟨hx2, hxH⟩
        exact ⟨hx2, fun hmem => hxH hmem.1⟩
    rw [h1, h2] at h
    exact h.symm
  -- Hence `|I| ∣ [G : H] - 1`.
  obtain ⟨k, hk⟩ := hdvd
  have hk' : {x : G | orderOf x = 2 ∧ x ∉ B.H}.ncard = k * Nat.card I := by
    rw [hk, mul_comm]
  have hidx' : B.H.index = (Work.GW2.involutionSet B.H).ncard
      + {x : G | orderOf x = 2 ∧ x ∉ B.H}.ncard := by
    rw [← hsplit]; exact hidx.symm
  have hmain : B.H.index = 1 + (n * Nat.card I + k * Nat.card I) := by
    rw [hidx', hcardH, hk']; ring
  have hdvd' : Nat.card I ∣ B.H.index - 1 := by
    have h1 : B.H.index - 1 = n * Nat.card I + k * Nat.card I := by
      rw [hmain]; omega
    exact h1 ▸ dvd_add (Dvd.intro n (by ring)) (Dvd.intro k (by ring))
  exact coprime_of_dvd_sub_one (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hdvd'

end Work.CORE2A
