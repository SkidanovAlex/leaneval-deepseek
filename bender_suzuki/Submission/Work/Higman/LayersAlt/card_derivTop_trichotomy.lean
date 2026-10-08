/-
Copyright (c) 2024. All rights reserved.

# The order of the derived subgroup of a Suzuki 2-group with a fixed-point-free `ξ`

`Work.Higman.LayersAlt.card_derivTop_trichotomy`: for a Suzuki 2-group `P` (Higman 1963) with a
fixed-point-free automorphism `ξ` of order `|Z(P)| - 1` (`Work.Higman.FpfXi ξ`), the derived
subgroup `P' = derivTop P` has order `|Z(P)|`, `|Z(P)|²` or `|Z(P)|³`.

The proof is an orbit count, and uses no classification theorem:

* `FpfXi` gives `|P| = q³`, `q = |Z(P)|`, and `orderOf ξ = q - 1`;
* `ξ` is fixed-point-free on `P ∖ {1}`, hence `⟨ξ⟩` acts *freely* on `P' ∖ {1}`
  (`P'` is characteristic, so `⟨ξ⟩`-invariant); therefore every `⟨ξ⟩`-orbit on `P' ∖ {1}` has
  exactly `q - 1` elements and `q - 1 ∣ |P'| - 1`
  (`card_dvd_card_sub_one_of_free`);
* writing `|P| = 2^M`, `q = 2^n`, `|P'| = 2^k` (all subgroups of a `2`-group have `2`-power
  order), the divisibility `2^n - 1 ∣ 2^k - 1` forces `n ∣ k`
  (`Work.Higman.Q3.pow_sub_one_dvd_pow_sub_one_iff`);
* finally `0 < k` (`P` is non-abelian, so `P' ≠ 1`) and `k < 3n` (a nontrivial finite `2`-group
  is not perfect, so `P' ≠ P`), whence `k ∈ {n, 2n}` and `|P'| = q` or `q²`.

The third alternative `q³` is therefore vacuous here; it is included because it is what the
consumer needs.
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.typeB
import Submission.Work.Higman.LayersAlt.fpf_defs
import Submission.Work.Higman.Q3.pow_sub_one_dvd_pow_sub_one_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

open scoped commutatorElement

namespace Work.Higman.LayersAlt

variable {P : Type} [Group P]

/-- **The natural action of the automorphism group on the derived subgroup.**

`derivTop P = P'` is a characteristic subgroup of `P`, so every automorphism of `P` restricts to
an automorphism of the set `P'`.  Recording it as a `MulAction` lets the `Subgroup`-action of
`Subgroup.zpowers ξ` on `↥(derivTop P)` be found by typeclass search. -/
instance instMulAutDerivTop : MulAction (MulAut P) ↥(derivTop P) where
  smul g x := ⟨g x.1, by
    have hiff : ∀ y : P, g y ∈ derivTop P ↔ y ∈ derivTop P := by
      intro y
      constructor
      · intro hy
        have hy' : g y ∈ (derivTop P).map g.toMonoidHom := by rwa [map_derivTop g]
        rw [Subgroup.mem_map] at hy'
        obtain ⟨z, hz, hzy⟩ := hy'
        rwa [g.injective hzy] at hz
      · intro hy
        have h1 : g y ∈ (derivTop P).map g.toMonoidHom := Subgroup.mem_map_of_mem _ hy
        rwa [map_derivTop g] at h1
    exact (hiff x.1).mpr x.2⟩
  one_smul x := by
    apply Subtype.ext
    exact MulAut.one_apply P x.1
  mul_smul g₁ g₂ x := by
    apply Subtype.ext
    exact MulAut.mul_apply P g₁ g₂ x.1

/-- **Orbit count for a group acting freely off a fixed point.**

If a finite group `K` acts on a finite type `X`, `o : X` is fixed by all of `K`, and every
`x ≠ o` is fixed only by `1`, then `|K|` divides `|X| - 1`: the complement of `o` is a disjoint
union of free `K`-orbits, each of cardinality `|K|`. -/
lemma card_dvd_card_sub_one_of_free {K X : Type*} [Group K] [Fintype K] [MulAction K X]
    [Fintype X] [DecidableEq X] (o : X) (hfix : ∀ k : K, k • o = o)
    (hfree : ∀ (k : K) (x : X), x ≠ o → k • x = x → k = 1) :
    Fintype.card K ∣ Fintype.card X - 1 := by
  classical
  set s : Finset X := Finset.univ.filter (fun x => x ≠ o) with hs
  have hs_card : s.card = Fintype.card X - 1 := by
    rw [hs]
    have h1 := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset X)) (p := fun x => x ≠ o)
    have h2 : (Finset.univ.filter (fun x : X => ¬ x ≠ o)).card = 1 := by
      have hset : (Finset.univ.filter (fun x : X => ¬ x ≠ o)) = {o} := by
        ext x; simp
      rw [hset]; simp
    rw [Finset.card_univ] at h1
    omega
  rw [← hs_card]
  rw [Finset.card_eq_sum_card_image (fun x : X => MulAction.orbit K x) s]
  apply Finset.dvd_sum
  intro b hb
  obtain ⟨x₀, hx₀s, hx₀⟩ := Finset.mem_image.mp hb
  have hx₀ne : x₀ ≠ o := by simpa [hs] using hx₀s
  rw [← hx₀]
  have hinj : Function.Injective (fun k : K => k • x₀) := by
    intro k₁ k₂ h'
    have h' : k₁ • x₀ = k₂ • x₀ := h'
    have h2 : (k₂⁻¹ * k₁) • x₀ = x₀ := by rw [mul_smul, h', inv_smul_smul]
    have h3 := hfree (k₂⁻¹ * k₁) x₀ hx₀ne h2
    rw [inv_mul_eq_one] at h3
    exact h3.symm
  have hset : s.filter (fun a => MulAction.orbit K a = MulAction.orbit K x₀)
      = Finset.image (fun k : K => k • x₀) Finset.univ := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, hs,
      MulAction.orbit_eq_iff, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨-, k, hk⟩; exact ⟨k, hk⟩
    · rintro ⟨k, hk⟩
      refine ⟨?_, ⟨k, hk⟩⟩
      intro hcon
      have hkx : k • x₀ = o := hk.trans hcon
      have : x₀ = o := by
        calc x₀ = k⁻¹ • (k • x₀) := by rw [inv_smul_smul]
          _ = k⁻¹ • o := by rw [hkx]
          _ = o := hfix k⁻¹
      exact hx₀ne this
  rw [hset, Finset.card_image_of_injective (Finset.univ : Finset K) hinj, Finset.card_univ]

theorem card_derivTop_trichotomy {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {ξ : MulAut P} (hξ : Work.Higman.FpfXi ξ) :
    Nat.card ↥(Work.Higman.LayersAlt.derivTop P) = Nat.card ↥(Subgroup.center P) ∨
    Nat.card ↥(Work.Higman.LayersAlt.derivTop P) = Nat.card ↥(Subgroup.center P) ^ 2 ∨
    Nat.card ↥(Work.Higman.LayersAlt.derivTop P) = Nat.card ↥(Subgroup.center P) ^ 3 := by
  classical
  set q := Nat.card ↥(Subgroup.center P) with hqdef
  haveI : Fintype ↥(derivTop P) := Fintype.ofFinite _
  haveI : Fintype ↥(Subgroup.zpowers ξ) := Fintype.ofFinite _
  haveI : Fintype ↥(Subgroup.center P) := Fintype.ofFinite _
  haveI : Nontrivial P := h.nontrivial
  -- `q = |Z(P)| ≥ 2`
  have hq2 : 2 ≤ q := by
    haveI : Nontrivial ↥(Subgroup.center P) := h.center_nontrivial
    have h1 : 1 < Fintype.card ↥(Subgroup.center P) := Fintype.one_lt_card
    have h2 : Fintype.card ↥(Subgroup.center P) = Nat.card ↥(Subgroup.center P) :=
      Nat.card_eq_fintype_card.symm
    rw [hqdef, ← h2]
    omega
  -- `|P| = 2 ^ M`
  obtain ⟨M, hM⟩ := h.isPGroup.exists_card_eq
  have hq3 : q ^ 3 = 2 ^ M := by rw [hqdef, ← hξ.card_cube, hM]
  -- `q = 2 ^ n`
  have hq_dvd : q ∣ 2 ^ M := by rw [← hq3]; exact dvd_pow_self q (by norm_num)
  obtain ⟨n, hnle, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hq_dvd
  have hM3 : M = 3 * n := by
    have h2M : 2 ^ M = 2 ^ (3 * n) := by
      rw [← hM, hξ.card_cube, ← hqdef, hn, ← pow_mul]
      congr 1
      ring
    exact Nat.pow_right_injective (by norm_num) h2M
  have hnpos : 0 < n := by
    by_contra hcon
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hcon
    rw [hn0, pow_zero] at hn
    omega
  -- `|P'| = 2 ^ k`
  have hdvd : Nat.card ↥(derivTop P) ∣ 2 ^ M := by
    rw [← hM]; exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨k, hkM, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  -- `⟨ξ⟩` acts freely on `P' ∖ {1}`, so `q - 1 ∣ |P'| - 1`
  have hfix : ∀ kk : ↥(Subgroup.zpowers ξ), kk • (1 : ↥(derivTop P)) = 1 := by
    intro kk
    apply Subtype.ext
    exact map_one (kk : MulAut P)
  have hfree : ∀ (kk : ↥(Subgroup.zpowers ξ)) (x : ↥(derivTop P)),
      x ≠ 1 → kk • x = x → kk = 1 := by
    intro kk x hx hmem
    have hx1 : (x : P) ≠ 1 := fun hx' => hx (Subtype.ext hx')
    have hkval : (kk : MulAut P) x.1 = x.1 := congrArg Subtype.val hmem
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp kk.2
    obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg j
    · rw [hm, zpow_natCast] at hj
      have hkj : (ξ ^ m) x.1 = x.1 := by rw [hj]; exact hkval
      have h1 : ξ ^ m = 1 := by
        by_contra hne
        exact hx1 (hξ.fpf m hne x.1 hkj)
      rw [h1] at hj
      exact Subtype.ext hj.symm
    · rw [hm, zpow_neg, zpow_natCast] at hj
      have hkj : ((ξ ^ m)⁻¹ : MulAut P) x.1 = x.1 := by rw [hj]; exact hkval
      have h2 : (ξ ^ m) x.1 = x.1 := by
        have h3 : (ξ ^ m : MulAut P) (((ξ ^ m)⁻¹ : MulAut P) x.1) = x.1 := by
          rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
        rw [hkj] at h3
        exact h3
      have h1 : ξ ^ m = 1 := by
        by_contra hne
        exact hx1 (hξ.fpf m hne x.1 h2)
      rw [h1, inv_one] at hj
      exact Subtype.ext hj.symm
  have horb := card_dvd_card_sub_one_of_free (K := ↥(Subgroup.zpowers ξ))
    (X := ↥(derivTop P)) (1 : ↥(derivTop P)) hfix hfree
  have hK : Fintype.card ↥(Subgroup.zpowers ξ) = q - 1 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_zpowers, hqdef]
    exact hξ.order
  have hX : Fintype.card ↥(derivTop P) = Nat.card ↥(derivTop P) :=
    Nat.card_eq_fintype_card.symm
  rw [hK, hX] at horb
  -- `2 ^ n - 1 ∣ 2 ^ k - 1`
  have hdiv : 2 ^ n - 1 ∣ 2 ^ k - 1 := by
    have h1 : q - 1 = 2 ^ n - 1 := by rw [hn]
    rw [h1, hk] at horb
    exact horb
  have hnk : n ∣ k :=
    (Work.Higman.Q3.pow_sub_one_dvd_pow_sub_one_iff (x := 2) (by norm_num) hnpos).mp hdiv
  -- `0 < k`
  have hP'ne : derivTop P ≠ ⊥ := by
    intro hbot
    obtain ⟨x, y, hxy⟩ := h.noncomm
    have hmem : ⁅x, y⁆ ∈ derivTop P :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    rw [hbot] at hmem
    exact hxy (commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem))
  have hkpos : 0 < k := by
    by_contra hcon
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hcon
    rw [hk0, pow_zero] at hk
    exact hP'ne (Subgroup.card_eq_one.mp hk)
  -- `k < 3 n`
  have hklt : k < 3 * n := by
    have hk3 : k ≤ 3 * n := by rw [← hM3]; exact hkM
    rcases lt_or_eq_of_le hk3 with hlt | heq
    · exact hlt
    · exfalso
      have hcard : Nat.card ↥(derivTop P) = Nat.card P := by
        rw [hk, heq, ← hM3, ← hM]
      exact (derivTop_ne_top h.isPGroup)
        (Subgroup.eq_top_of_card_eq (derivTop P) hcard)
  have hk_cases : k = n ∨ k = 2 * n := by
    obtain ⟨c, hc⟩ := hnk
    have hcpos : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h0 | hpos
      · exfalso; rw [h0, mul_zero] at hc; omega
      · exact hpos
    have hclt : c < 3 := by
      have h1 : n * c < n * 3 := by rw [← hc, Nat.mul_comm n 3]; exact hklt
      exact Nat.lt_of_mul_lt_mul_left h1
    rcases (show c = 1 ∨ c = 2 by omega) with h1 | h2
    · left; rw [hc, h1, mul_one]
    · right; rw [hc, h2, Nat.mul_comm]
  have hpk : Nat.card ↥(derivTop P) = q ^ (k / n) := by
    rw [hk, hn, ← pow_mul]
    congr 1
    exact (Nat.mul_div_cancel' hnk).symm
  rcases hk_cases with h1 | h2
  · left
    rw [hpk, h1, Nat.div_self hnpos, pow_one, hqdef]
  · right; left
    rw [hpk, h2, Nat.mul_comm 2 n, Nat.mul_div_cancel_left 2 hnpos, hqdef]

end Work.Higman.LayersAlt
