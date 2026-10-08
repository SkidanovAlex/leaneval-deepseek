import Mathlib
import Submission.Work.CORE2B.Defs

/-!
# `Work.CORE2B.L29_case_ii` — Bender 1981, Lemma 2.9, case (ii)

Let `B` be Bender's setup: `S` is a Sylow 2-subgroup of `G`, `S₀ ≤ S` is a **cyclic** subgroup of
index two, and `t ∈ S₀` is an involution.  Suppose `V ≤ S` is a Klein four-group with `t ∈ V`,
`S ≤ N`, and `z ∈ C_G(N)` is an involution.  Then `V ∩ O₂(N) ≠ 1`.

This is case (ii) of the D-group analysis of Lemma 2.9 (`∃ z ∈ Z(↥N)` an involution), and the
argument is elementary:

* `z` centralises `N ⊇ S`.  Then `⟨z⟩ · S` is a 2-subgroup of `G` (its order is `|S|` or `2|S|`)
  containing the Sylow 2-subgroup `S`, hence equals `S`; so `z ∈ S`.
* Since `S₀` is cyclic, `S₀` has at most one involution, and since `S₀` has index two in `S`
  every element of `S` outside `S₀` generates the same non-trivial coset.
* `z ∈ S` is an involution with `z ∈ C_G(V)`.  If `z ∈ S₀` then `z = t ∈ V` (uniqueness of the
  involution in the cyclic group `S₀`).  If `z ∉ S₀`, pick `w ∈ V ∖ S₀`; then `z w⁻¹ ∈ S₀` and
  `z` commutes with `w`, whence `(z w⁻¹)² = 1`, so `z w⁻¹ ∈ {1, t}` and again `z ∈ V`.
* Finally `z ∈ V ≤ N` and `z ∈ Z(N)` make `⟨z⟩` a normal 2-subgroup of `↥N`, i.e.
  `z ∈ O₂(N) = pCoreIn 2 N`, contradicting `V ∩ O₂(N) = 1` since `z ≠ 1`.

The fact `V ⊄ S₀` (used in the second step) is itself a consequence of `S₀` being cyclic:
`V ≤ S₀` would make `V` cyclic of exponent two, hence of order `≤ 2 < 4 = |V|`.
-/

namespace Work.CORE2B

open Subgroup

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- A finite cyclic group has at most one element of order two. -/
private theorem uniq_orderOf_two {H : Type} [Group H] [Finite H] [IsCyclic H] {a b : H}
    (ha : orderOf a = 2) (hb : orderOf b = 2) : a = b := by
  classical
  have hfin : Fintype H := Fintype.ofFinite H
  have hd : 2 ∣ Fintype.card H := by
    rw [← Nat.card_eq_fintype_card, ← ha]
    exact orderOf_dvd_natCard a
  have hcard : Fintype.card {x : H // orderOf x = 2} = 1 := by
    rw [Fintype.card_subtype, IsCyclic.card_orderOf_eq_totient (α := H) hd, Nat.totient_two]
  exact Subtype.ext_iff.mp (Fintype.card_le_one_iff.mp (le_of_eq hcard) ⟨a, ha⟩ ⟨b, hb⟩)

/-- A finite cyclic group all of whose elements have order at most two has order at most two. -/
private theorem natCard_le_two_of_isCyclic {H : Type} [Group H] [Finite H] [IsCyclic H]
    (h : ∀ x : H, x * x = 1) : Nat.card H ≤ 2 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  have htop : Subgroup.zpowers g = (⊤ : Subgroup H) := eq_top_iff.mpr (fun x _ => hg x)
  have hord : orderOf g = Nat.card H := by
    rw [← Nat.card_zpowers g, htop, Subgroup.card_top]
  have hg2 : g ^ 2 = 1 := by rw [pow_two]; exact h g
  have hdvd : orderOf g ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hg2
  have hle : orderOf g ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem L29_case_ii {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    (N V : Subgroup G) (hSN : (B.S : Subgroup G) ≤ N) (hVN : V ≤ N)
    (hV : Work.GW2.IsFourGroup V) (hVS : V ≤ (B.S : Subgroup G)) (htV : B.t ∈ V)
    (z : G) (hz : ∀ n ∈ N, n * z = z * n) (hz2 : orderOf z = 2)
    (h1 : V ⊓ Work.GW2.pCoreIn 2 N = ⊥) : False := by
  classical
  haveI : IsCyclic ↥B.S0 := B.S0_cyclic
  -- ## Step 1: `z` lies in the Sylow 2-subgroup `S`.
  have hz_cent : z ∈ Subgroup.centralizer ((B.S : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact hz s (hSN hs)
  have hS_le_norm : (B.S : Subgroup G) ≤ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
    have h1' : Subgroup.zpowers z ≤ Subgroup.centralizer ((B.S : Subgroup G) : Set G) :=
      Subgroup.zpowers_le.mpr hz_cent
    have h2' : (B.S : Subgroup G) ≤
        Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) :=
      Subgroup.le_centralizer_iff.mp h1'
    exact h2'.trans (Subgroup.centralizer_le_normalizer _)
  have hzpgrp : IsPGroup 2 ↥(Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2]; norm_num)
  have hsup_pgrp : IsPGroup 2 ↥(Subgroup.zpowers z ⊔ (B.S : Subgroup G)) :=
    IsPGroup.to_sup_of_normal_left' hzpgrp (B.S).isPGroup' hS_le_norm
  have hsup_eq : Subgroup.zpowers z ⊔ (B.S : Subgroup G) = (B.S : Subgroup G) :=
    (B.S).is_maximal' hsup_pgrp le_sup_right
  have hzS : z ∈ (B.S : Subgroup G) := by
    rw [← hsup_eq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
  -- ## Step 2: there is `w ∈ V` with `w ∉ S₀` (else `V ≤ S₀` is cyclic of exponent two).
  have hV_not_le_S0 : ¬ V ≤ B.S0 := by
    intro hVS0
    haveI : IsCyclic ↥V := Subgroup.isCyclic_of_le hVS0
    have hsq : ∀ x : ↥V, x * x = 1 := fun x =>
      Subtype.ext (by simpa [pow_two] using hV.2 (x : G) x.2)
    have hvm : Nat.card ↥V = 4 := hV.1
    have hle := natCard_le_two_of_isCyclic hsq
    omega
  obtain ⟨w, hwV, hwS0⟩ : ∃ v ∈ V, v ∉ B.S0 := by
    by_contra h
    push Not at h
    exact hV_not_le_S0 fun v hv => h v hv
  have hwS : w ∈ (B.S : Subgroup G) := hVS hwV
  -- ## Step 3: `z ∈ V`.
  have hzV : z ∈ V := by
    by_cases hz0 : z ∈ B.S0
    · -- Case (a): `z ∈ S₀`, and `S₀` has a unique involution.
      have heq : z = B.t :=
        congrArg Subtype.val (uniq_orderOf_two (H := ↥B.S0)
          (a := (⟨z, hz0⟩ : ↥B.S0)) (b := (⟨B.t, B.t_mem⟩ : ↥B.S0))
          (by rw [Subgroup.orderOf_mk]; exact hz2)
          (by rw [Subgroup.orderOf_mk]; exact B.t_order))
      rw [heq]; exact htV
    · -- Case (b): `z ∉ S₀`.  `S₀` has index two, so `S ∖ S₀` is a single coset; use the
      -- "parity" description of `S₀ ≤ S` to get `z * w⁻¹ ∈ S₀`.
      obtain ⟨a, haS, ha⟩ :=
        (Subgroup.relIndex_eq_two_iff' (H := B.S0) (K := (B.S : Subgroup G))).mp B.S0_index
      have haux : ∀ b ∈ (B.S : Subgroup G), (b ∈ B.S0 ↔ a⁻¹ * b ∉ B.S0) := by
        intro b hb
        have h := ha (a⁻¹ * b)
          ((B.S : Subgroup G).mul_mem ((B.S : Subgroup G).inv_mem haS) hb)
        rw [show a * (a⁻¹ * b) = b by group] at h
        exact xor_iff_iff_not.mp h
      have haw : a⁻¹ * w ∈ B.S0 := by
        by_contra hc
        exact hwS0 ((haux w hwS).mpr hc)
      have haz : a⁻¹ * z ∈ B.S0 := by
        by_contra hc
        exact hz0 ((haux z hzS).mpr hc)
      set s : G := w⁻¹ * z with hs_def
      have hs0 : s ∈ B.S0 := by
        have hm := B.S0.mul_mem (B.S0.inv_mem haw) haz
        rwa [show (a⁻¹ * w)⁻¹ * (a⁻¹ * z) = s by rw [hs_def]; group] at hm
      have hz_eq : z = w * s := by rw [hs_def]; group
      have hww : w * w = 1 := by
        have := hV.2 w hwV; simpa [pow_two] using this
      have hzz : z * z = 1 := by
        have := pow_orderOf_eq_one z
        rw [hz2] at this; simpa [pow_two] using this
      have hzw : z * w = w * z := (hz w (hVN hwV)).symm
      have hsw : s * w = w * s := by
        have hEq : (w * s) * w = w * (w * s) := by rw [← hz_eq]; exact hzw
        rw [mul_assoc w s w] at hEq
        exact mul_left_cancel hEq
      have hss : s * s = 1 := by
        have hsplit : (w * s) * (w * s) = s * s := by
          rw [show (w * s) * (w * s) = w * (s * w) * s by group, hsw]
          rw [show w * (w * s) * s = (w * w) * (s * s) by group, hww, one_mul]
        rw [← hz_eq, hzz] at hsplit
        exact hsplit.symm
      have hs_cases : s = 1 ∨ s = B.t := by
        by_cases h1' : s = 1
        · exact Or.inl h1'
        · right
          have hord : orderOf s = 2 :=
            (orderOf_eq_prime_iff (p := 2)).mpr ⟨by simpa [pow_two] using hss, h1'⟩
          exact congrArg Subtype.val (uniq_orderOf_two (H := ↥B.S0)
            (a := (⟨s, hs0⟩ : ↥B.S0)) (b := (⟨B.t, B.t_mem⟩ : ↥B.S0))
            (by rw [Subgroup.orderOf_mk]; exact hord)
            (by rw [Subgroup.orderOf_mk]; exact B.t_order))
      rcases hs_cases with h1' | ht
      · rw [hz_eq, h1', mul_one]; exact hwV
      · rw [hz_eq, ht]; exact V.mul_mem hwV htV
  -- ## Step 4: `z ∈ O₂(N)`, contradicting `V ∩ O₂(N) = 1`.
  have hzN : z ∈ N := hVN hzV
  have hzcenter : (⟨z, hzN⟩ : ↥N) ∈ Subgroup.center ↥N := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hz g g.2)
  have hnorm : (Subgroup.zpowers (⟨z, hzN⟩ : ↥N)).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hzcenter)
  have hpgrp : IsPGroup 2 ↥(Subgroup.zpowers (⟨z, hzN⟩ : ↥N)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hz2]; norm_num)
  have hle : Subgroup.zpowers (⟨z, hzN⟩ : ↥N) ≤ Work.GW2.pCore 2 ↥N := by
    rw [Work.GW2.pCore]
    haveI := hnorm
    exact Subgroup.normal_le_normalCore.mpr (le_sSup ⟨hnorm, hpgrp⟩)
  have hzO2 : z ∈ Work.GW2.pCoreIn 2 N := by
    rw [Work.GW2.pCoreIn, Subgroup.mem_map]
    exact ⟨⟨z, hzN⟩, hle (Subgroup.mem_zpowers _), rfl⟩
  have hmem : z ∈ V ⊓ Work.GW2.pCoreIn 2 N := ⟨hzV, hzO2⟩
  rw [h1] at hmem
  have hz1 : z = 1 := Subgroup.mem_bot.mp hmem
  rw [hz1] at hz2
  exact absurd hz2 (by norm_num)

end Work.CORE2B
