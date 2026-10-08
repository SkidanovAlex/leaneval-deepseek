import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.L27cf_helpers
import Submission.Work.CORE2B.isPGroup_pCoreIn_two

/-!
# CORE2B — `t` centralizes the odd part of `F_π(M)` (Bender 1981, Lemma 2.7, step 3)

Bender's Lemma 2.7 (p. 221) reads, in the notation of the area,

> "Our assumptions force every normal subgroup of `M` of order divisible by `4` to contain `t`.
> Hence `E(M) = 1` and `t` centralizes `O₂(M)`.  Then `t` centralizes `F_π(M)` and inverts
> `F_{π'}(M)`, by Lemma 2.3.i/ii and since `t ∈ O₂(Ĥ)`."

This module proves the sentence "`t` centralizes `F_π(M)`", in the sharp form needed by the
consumers (`L27_centralizes_fitting_crux`, `L27_centralizes_fittingIn`): the *odd* part
`F_{π ∩ {2}ᶜ}(M) = O_{π ∩ {2}ᶜ}(F(M))` of the `π`-part.  (The prime `2` lies in `π` because
`t ∈ O₂(Ĥ) ≠ 1`; the `2`-part of `F_π(M)` is `F₂(M)`, handled separately by
`L27_two_part_centralized`.)

    `F_{π ∩ {2}ᶜ}(M) ≤ C_G(t)`,  `π = π(F(Ĥ)) = B.pi`.

Two remarks on the shape of the statement:

* `t` centralizes the *odd* part of `F_π(M)`, not all of `F_π(M)`: the `2`-part needs the
  separate argument `L27_two_part_centralized` (Bender's step 1), and the statement here is the
  genuinely new piece.
* The fixed-point-freeness argument available for `F_{π'}(M)` (Lemma 2.3(ii) gives
  `F_{π'}(M) ⊓ Ĥ = 1`) is *not* applicable here: on the contrary, `F_π(M) ≤ Ĥ`.  What replaces it
  is that the commutators `⁅t,x⁆`, `x ∈ F_{π ∩ {2}ᶜ}(M)`, lie both in an odd-order group and in
  the `2`-group `O₂(Ĥ)`.

## The argument

Let `σ = π ∩ {2}ᶜ` and `P = O₂(Ĥ)`, a `2`-group normal in `Ĥ` with `t ∈ P` (Theorem 2.6,
`L27cf_t_mem_pCoreIn_two`).

* **Case `F*(Ĥ)` is a `p`-group.**  Then `π = {2}` (`L27cf_pi_eq_two_of_isPGroup_fstar`), so
  `σ = ∅` and `F_σ(M) = F_∅(M) = 1` (`L27cf_fittingPiIn_inter_compl_eq_bot`).
* **Otherwise** Lemma 2.3(i) (`h23`) gives `F_π(M) ≤ Ĥ`, and `F_σ(M) ≤ F_π(M)` because
  `σ ⊆ π`, so every `x ∈ F_σ(M)` lies in `Ĥ`.  Since `M` normalizes the characteristic subgroup
  `F_σ(M)` (`le_normalizer_fittingPiIn_local`) and `t ∈ M`, the commutator
  `y = ⁅t, x⁆ = t x t⁻¹ x⁻¹` lies in `F_σ(M)`; and since `t ∈ P ⊴ Ĥ` and `x ∈ Ĥ`, it also lies in
  `⁅P, Ĥ⁆ ≤ P` (`Subgroup.le_normalizer_iff_commutator_le_right`).  Thus `y` lies in a group of
  odd order (`L27cf_odd_card_fittingPiIn`) and in a `2`-group
  (`isPGroup_pCoreIn_two`), so `orderOf y = 1`, i.e. `⁅t,x⁆ = 1`, i.e. `t x = x t`.

The two elementary facts about the vocabulary used above are packaged as
`L27cf_isPiSubgroup_fittingPiIn` and `L27cf_odd_card_fittingPiIn` below.
-/

open scoped commutatorElement

namespace Work.CORE2B

open Subgroup

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## 1. `F_σ(K)` is a `σ`-group, of odd order when `2 ∉ σ` -/

/-- `F_σ(K) = O_σ(F(K))`, realized inside `G`, is a `σ`-group: it is the image of the characteristic
subgroup `O_σ(F(K))` of `↥K` under two injective inclusions, which preserve `Nat.card`. -/
theorem L27cf_isPiSubgroup_fittingPiIn {G : Type} [Group G] [Finite G] (σ : Set ℕ)
    (K : Subgroup G) : Subgroup.IsPiSubgroup σ (Work.GW2.fittingPiIn σ K) := by
  have hcard : Nat.card (Work.GW2.fittingPiIn σ K)
      = Nat.card (Work.GW2.piCore σ ↥(Work.GW2.fitting ↥K)) := by
    rw [Work.GW2.fittingPiIn, Work.GW2.fittingPi, Subgroup.map_map]
    exact Subgroup.card_map_of_injective
      (K.subtype_injective.comp (Work.GW2.fitting ↥K).subtype_injective)
  intro q hq
  rw [hcard] at hq
  exact isPiSubgroup_piCore_local σ q hq

/-- `F_σ(K)` has odd order as soon as `σ` contains no `2`. -/
theorem L27cf_odd_card_fittingPiIn {G : Type} [Group G] [Finite G] {σ : Set ℕ}
    (hσ : σ ⊆ ({2}ᶜ : Set ℕ)) (K : Subgroup G) :
    Odd (Nat.card (Work.GW2.fittingPiIn σ K)) :=
  L27cf_odd_card_of_isPiSubgroup hσ (L27cf_isPiSubgroup_fittingPiIn σ K)

/-! ## 2. The target -/

theorem L27cf_centralizes_odd_pi_part :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G), Work.CORE2B.L27Hyp B M →
      Work.GW2.Lemma23Prop → Work.GW2.Thm26Prop →
        Work.GW2.fittingPiIn (B.pi ∩ ({2}ᶜ : Set ℕ)) M ≤
          Subgroup.centralizer ({B.t} : Set G) := by
  intro G _ _ hFT hCtx B M hD h23 h26
  set σ : Set ℕ := B.pi ∩ ({2}ᶜ : Set ℕ) with hσdef
  have hsubπ : σ ⊆ B.pi := Set.inter_subset_left
  have hsub2 : σ ⊆ ({2}ᶜ : Set ℕ) := Set.inter_subset_right
  by_cases hpg : ∃ p : ℕ, p.Prime ∧ IsPGroup p (Work.GW2.fstarIn B.Hhat)
  · -- `F*(Ĥ)` is a `p`-group: then `π = {2}` and the odd part of `π` is empty
    have hbot : Work.GW2.fittingPiIn σ M = ⊥ := by
      rw [hσdef]
      exact L27cf_fittingPiIn_inter_compl_eq_bot h26 hFT hCtx B hpg M
    intro x hx
    rw [hbot] at hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    rw [Subgroup.mem_bot.mp hx, mul_one, one_mul]
  · -- otherwise Lemma 2.3(i) gives `F_π(M) ≤ Ĥ`
    have hleπ : Work.GW2.fittingPiIn B.pi M ≤ B.Hhat :=
      (h23 G hFT hCtx B M hD.M_ne_top hD.rel).1 hpg
    have hodd : Odd (Nat.card (Work.GW2.fittingPiIn σ M)) := L27cf_odd_card_fittingPiIn hsub2 M
    have h2pow : IsPGroup 2 (Work.GW2.pCoreIn 2 B.Hhat) := isPGroup_pCoreIn_two B.Hhat
    have htP : B.t ∈ Work.GW2.pCoreIn 2 B.Hhat := L27cf_t_mem_pCoreIn_two h26 hFT hCtx B
    have htN : B.t ∈ Subgroup.normalizer
        ((Work.GW2.fittingPiIn σ M : Subgroup G) : Set G) :=
      le_normalizer_fittingPiIn_local σ M hD.t_mem
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    -- `x ∈ F_σ(M) ≤ F_π(M) ≤ Ĥ`
    have hxH : x ∈ B.Hhat := hleπ (fittingPiIn_mono' hsubπ M hx)
    -- the commutator `⁅t,x⁆` lies in the odd-order group `F_σ(M)`
    have hcom_mem : ⁅B.t, x⁆ ∈ Work.GW2.fittingPiIn σ M := by
      have h1 : B.t * x * B.t⁻¹ ∈ Work.GW2.fittingPiIn σ M :=
        (Subgroup.mem_normalizer_iff.mp htN x).mp hx
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hx)
    -- and in the `2`-group `O₂(Ĥ)` (`t ∈ O₂(Ĥ) ⊴ Ĥ` and `x ∈ Ĥ`)
    have hcom_P : ⁅B.t, x⁆ ∈ Work.GW2.pCoreIn 2 B.Hhat := by
      have hle2 : ⁅(Work.GW2.pCoreIn 2 B.Hhat : Subgroup G), B.Hhat⁆ ≤
          Work.GW2.pCoreIn 2 B.Hhat := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.le_normalizer_iff_commutator_le_right.mp
          (L27cf_le_normalizer_pCoreIn_two B.Hhat)
      exact hle2 (Subgroup.commutator_mem_commutator htP hxH)
    -- a `2`-power which is odd is `1`
    have hcom_one : ⁅B.t, x⁆ = 1 := by
      have h1 : orderOf ⁅B.t, x⁆ ∣ Nat.card (Work.GW2.fittingPiIn σ M) := by
        have h := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hcom_mem)
        rwa [Nat.card_zpowers] at h
      have h2 : orderOf ⁅B.t, x⁆ ∣ Nat.card (Work.GW2.pCoreIn 2 B.Hhat) := by
        have h := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hcom_P)
        rwa [Nat.card_zpowers] at h
      have ho : Odd (orderOf ⁅B.t, x⁆) := Odd.of_dvd_nat hodd h1
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2pow
      have h2' : orderOf ⁅B.t, x⁆ ∣ 2 ^ k := by rw [← hk]; exact h2
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2'
      have hj0 : j = 0 := by
        by_contra hjn
        have h2j : 2 ∣ 2 ^ j := dvd_pow_self 2 hjn
        rw [← hj] at h2j
        exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr h2j)
      exact orderOf_eq_one_iff.mp (by rw [hj, hj0, pow_zero])
    -- conclude `t * x = x * t`
    rw [commutatorElement_def] at hcom_one
    have hx1 : B.t * x * B.t⁻¹ = x := by
      calc B.t * x * B.t⁻¹ = B.t * x * B.t⁻¹ * x⁻¹ * x := by group
        _ = 1 * x := by rw [hcom_one]
        _ = x := one_mul x
    calc B.t * x = B.t * x * B.t⁻¹ * B.t := by group
      _ = x * B.t := by rw [hx1]

end Work.CORE2B
