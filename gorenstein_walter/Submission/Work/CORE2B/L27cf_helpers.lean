import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.L27_two_part_centralized_proved
import Submission.Work.BMAX.InvolutionInverts
import Submission.Work.CORE2B.L27_solvable_base

/-!
# CORE2B — helpers for `t` centralizing `F(M)` (Bender 1981, Lemma 2.7, "`[M,t] ⊆ C_M(F(M))`")

Bender's Lemma 2.7 (p. 221) proves, in this order:

1. every normal subgroup of `M` of order divisible by `4` contains `t`; hence `E(M) = 1` and `t`
   centralizes `O₂(M)` (`L27_two_part_centralized_proved`);
2. `t` centralizes `F_π(M)` and inverts `F_{π'}(M)`, where `π = π(F(Ĥ))` (Lemma 2.3.i/ii and
   `t ∈ O₂(Ĥ)`);
3. `[M,t] ⊆ C_M(F(M)) ≤ F(M)`.

This module collects the small vocabulary bridges shared by the pieces of step 2 and 3:

* `L27cf_fitting_eq_isaacsFitting`, `L27cf_isNilpotent_fitting`: `Work.GW2.fitting` is the
  Feit–Thompson library's Fitting subgroup (hence nilpotent) — the input for the nilpotent
  `π`-decomposition of `F(M)`;
* `L27cf_t_mem_pCoreIn_two`, `L27cf_le_normalizer_pCoreIn_two`: Theorem 2.6's `t ∈ O₂(Ĥ)`,
  and `O₂(Ĥ) ⊴ Ĥ`;
* `L27cf_piCore_empty`, `L27cf_fittingPiIn_empty`, `L27cf_odd_card_of_isPiSubgroup`: the
  `π`-core vocabulary for a `π` that contains no prime `2`;
* `L27cf_pi_eq_two_of_isPGroup_fstar`, `L27cf_fittingPiIn_inter_compl_eq_bot`: if `F*(Ĥ)` is a
  `p`-group then `p = 2` and `π = {2}`, so that the "odd part of `π`" is empty;
* `L27cf_inverts_fittingPiIn_pi_compl`: `t` inverts `F_{π'}(M)` (Bender's step 2, second half).

(The `Work.CORE2B.L27_api` module containing some of these statements does not currently
compile; the lemmas here are self-contained reproofs, under distinct names.)
-/

open scoped MatrixGroups commutatorElement

namespace Work.CORE2B

open Subgroup

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## 1. `Work.GW2.fitting` is the Feit–Thompson library's Fitting subgroup -/

/-- `Work.GW2.fitting G` is `OddOrder.Isaacs.Ch01.fitting G`, i.e. the join of the normal
nilpotent subgroups. -/
theorem L27cf_fitting_eq_isaacsFitting {G : Type} [Group G] [Finite G] :
    Work.GW2.fitting G = OddOrder.Isaacs.Ch01.fitting G := by
  have hS : sSup {N : Subgroup G | N.Normal ∧ Group.IsNilpotent N}
      = OddOrder.Isaacs.Ch01.fitting G := by
    refine le_antisymm (sSup_le ?_) (le_sSup ?_)
    · rintro N ⟨hN, hnil⟩
      haveI : N.Normal := hN
      haveI : Group.IsNilpotent ↥N := hnil
      exact OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
    · exact ⟨OddOrder.Isaacs.Ch01.fitting.normal G,
        OddOrder.Isaacs.Ch01.fitting.isNilpotent⟩
  haveI : (OddOrder.Isaacs.Ch01.fitting G).Normal :=
    OddOrder.Isaacs.Ch01.fitting.normal G
  rw [Work.GW2.fitting, hS]
  exact Subgroup.normalCore_eq_self _

/-- The Fitting subgroup of a finite group is nilpotent. -/
theorem L27cf_isNilpotent_fitting {G : Type} [Group G] [Finite G] :
    Group.IsNilpotent ↥(Work.GW2.fitting G) := by
  haveI : Group.IsNilpotent ↥(OddOrder.Isaacs.Ch01.fitting G) :=
    OddOrder.Isaacs.Ch01.fitting.isNilpotent
  exact (Group.isNilpotent_congr
    (MulEquiv.subgroupCongr L27cf_fitting_eq_isaacsFitting)).mpr inferInstance

/-! ## 2. Theorem 2.6: `t ∈ O₂(Ĥ)` and `O₂(Ĥ) ⊴ Ĥ` -/

/-- Theorem 2.6: `O₂(Ĥ) = S ⊓ C(U)`, and `t` lies in both factors. -/
theorem L27cf_t_mem_pCoreIn_two {G : Type} [Group G] [Finite G] (h26 : Work.GW2.Thm26Prop)
    (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) : B.t ∈ Work.GW2.pCoreIn 2 B.Hhat := by
  obtain ⟨-, hSC, -⟩ := h26 G hFT hCtx B
  rw [← hSC]
  refine ⟨B.S0_le B.t_mem, ?_⟩
  show B.t ∈ Subgroup.centralizer (B.U : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have huH : u ∈ B.H := Subgroup.map_subtype_le _ hu
  exact (Subgroup.mem_centralizer_iff.mp huH B.t rfl).symm

/-- `O₂(Ĥ) = O₂(↥Ĥ)` is normal in `Ĥ`, so `Ĥ` normalizes it. -/
theorem L27cf_le_normalizer_pCoreIn_two {G : Type} [Group G] (K : Subgroup G) :
    K ≤ Subgroup.normalizer ((Work.GW2.pCoreIn 2 K : Subgroup G) : Set G) := by
  simpa only [Work.GW2.pCoreIn] using
    le_normalizer_map_subtype_local K (Work.GW2.pCore 2 ↥K) (Subgroup.normalCore_normal _)

/-! ## 3. `π`-cores for a `π` containing no `2` -/

/-- `O_∅(G) = 1`: a group all of whose prime divisors lie in the empty set is trivial. -/
theorem L27cf_piCore_empty {G : Type} [Group G] [Finite G] :
    Work.GW2.piCore (∅ : Set ℕ) G = ⊥ := by
  have hpi : Subgroup.IsPiSubgroup (∅ : Set ℕ) (Work.GW2.piCore (∅ : Set ℕ) G) :=
    isPiSubgroup_piCore_local (∅ : Set ℕ)
  have hempty : (Nat.card (Work.GW2.piCore (∅ : Set ℕ) G)).primeFactors = ∅ := by
    ext q
    simp only [Finset.notMem_empty, iff_false]
    intro hq
    simpa using hpi q hq
  have hne : Nat.card (Work.GW2.piCore (∅ : Set ℕ) G) ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨1, Subgroup.one_mem _⟩, inferInstance⟩
  have hcard : Nat.card (Work.GW2.piCore (∅ : Set ℕ) G) = 1 :=
    (Nat.primeFactors_eq_empty.mp hempty).resolve_left hne
  exact Subgroup.card_eq_one.mp hcard

/-- `F_∅(K) = O_∅(F(K)) = 1`. -/
theorem L27cf_fittingPiIn_empty {G : Type} [Group G] [Finite G] (K : Subgroup G) :
    Work.GW2.fittingPiIn (∅ : Set ℕ) K = ⊥ := by
  rw [Work.GW2.fittingPiIn, Work.GW2.fittingPi, L27cf_piCore_empty, Subgroup.map_bot,
    Subgroup.map_bot]

/-- A subgroup whose prime divisors all lie in a `π` avoiding `2` has odd order. -/
theorem L27cf_odd_card_of_isPiSubgroup {G : Type} [Group G] [Finite G] {σ : Set ℕ}
    (hσ : σ ⊆ ({2}ᶜ : Set ℕ)) {X : Subgroup G} (hX : Subgroup.IsPiSubgroup σ X) :
    Odd (Nat.card X) := by
  rw [← Nat.not_even_iff_odd]
  intro hev
  have hne : Nat.card X ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1, X.one_mem⟩, inferInstance⟩
  have h2 : 2 ∈ (Nat.card X).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, even_iff_two_dvd.mp hev, hne⟩
  have hmem : 2 ∈ σ := hX 2 h2
  have hnot : 2 ∈ ({2}ᶜ : Set ℕ) := hσ hmem
  simpa using hnot

/-- If `F*(Ĥ)` is a `p`-group then `p = 2` and `π = π(F(Ĥ)) = {2}` (`t ∈ O₂(Ĥ) ≠ 1` forces the
prime to be `2`). -/
theorem L27cf_pi_eq_two_of_isPGroup_fstar {G : Type} [Group G] [Finite G]
    (h26 : Work.GW2.Thm26Prop) (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G)
    (hpg : ∃ p : ℕ, p.Prime ∧ IsPGroup p (Work.GW2.fstarIn B.Hhat)) :
    B.pi = {2} := by
  obtain ⟨p, hpp, hpg⟩ := hpg
  haveI : Fact p.Prime := ⟨hpp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpg
  have hfl : Work.GW2.fittingIn B.Hhat ≤ Work.GW2.fstarIn B.Hhat := by
    rw [Work.GW2.fittingIn, Work.GW2.fstarIn, Work.GW2.fstar]
    exact Subgroup.map_mono le_sup_left
  have hdiv : Nat.card (Work.GW2.fittingIn B.Hhat) ∣ p ^ n := by
    rw [← hn]
    exact Subgroup.card_dvd_of_le hfl
  have ht : B.t ∈ Work.GW2.pCoreIn 2 B.Hhat := L27cf_t_mem_pCoreIn_two h26 hFT hCtx B
  have hle : Work.GW2.pCoreIn 2 B.Hhat ≤ Work.GW2.fittingIn B.Hhat := by
    rw [Work.GW2.pCoreIn, Work.GW2.fittingIn]
    exact Subgroup.map_mono (pCore_le_fitting_local 2)
  have h2dvd : 2 ∣ Nat.card (Work.GW2.fittingIn B.Hhat) := by
    have h := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr ht)
    rw [Nat.card_zpowers, B.t_order] at h
    exact h.trans (Subgroup.card_dvd_of_le hle)
  have hp2 : p = 2 := by
    have h : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow (h2dvd.trans hdiv)
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hpp).mp h).symm
  have hne : Nat.card (Work.GW2.fittingIn B.Hhat) ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨1, (Work.GW2.fittingIn B.Hhat).one_mem⟩, inferInstance⟩
  ext q
  rw [Work.GW2.BenderSetup.pi, Work.GW2.primesOf, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro hq
    obtain ⟨hqp, hqdvd, -⟩ := Nat.mem_primeFactors.mp hq
    have h1 : q ∣ p := hqp.dvd_of_dvd_pow (hqdvd.trans hdiv)
    rw [hp2] at h1
    exact (Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp h1
  · intro hq
    rw [hq]
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2dvd, hne⟩

/-- If `F*(Ĥ)` is a `p`-group then `π ∩ {2}ᶜ = ∅`, so `F_{π ∩ {2}ᶜ}(M) = 1`. -/
theorem L27cf_fittingPiIn_inter_compl_eq_bot {G : Type} [Group G] [Finite G]
    (h26 : Work.GW2.Thm26Prop) (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G)
    (hpg : ∃ p : ℕ, p.Prime ∧ IsPGroup p (Work.GW2.fstarIn B.Hhat)) (M : Subgroup G) :
    Work.GW2.fittingPiIn (B.pi ∩ ({2}ᶜ : Set ℕ)) M = ⊥ := by
  have hpi : B.pi = {2} := L27cf_pi_eq_two_of_isPGroup_fstar h26 hFT hCtx B hpg
  rw [hpi, Set.inter_compl_self]
  exact L27cf_fittingPiIn_empty M

/-! ## 4. `t` inverts `F_{π'}(M)` (Bender 2.7, step 2, second half) -/

/-- Bender 1981, Lemma 2.7: under `L27Hyp B M`, `t` inverts `F_{π'}(M) = O_{π'}(F(M))`.

`F_{π'}(M) ⊆ M` is characteristic in `F(M) ◁ ↥M`, so `t ∈ M` acts on it; by Lemma 2.3(ii),
`F_{π'}(M) ∩ Ĥ = 1` and the fixed points of `t` lie in `C_G(t) = H ≤ Ĥ`; so the involution `t`
acts fixed-point-freely, hence (Burnside) inverts it — `Work.BMAX.InvolutionInverts`. -/
theorem L27cf_inverts_fittingPiIn_pi_compl {G : Type} [Group G] [Finite G]
    (h23 : Work.GW2.Lemma23Prop) (h26 : Work.GW2.Thm26Prop) (hFT : Work.GW2.FeitThompsonProp)
    (hCtx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (M : Subgroup G)
    (hD : L27Hyp B M) :
    Work.GW2.Inverts B.t (Work.GW2.fittingPiIn B.piᶜ M) := by
  have hFixBot : Work.GW2.fittingPiIn B.piᶜ M ⊓ B.Hhat = ⊥ :=
    (h23 G hFT hCtx B M hD.M_ne_top hD.rel).2.1
  have ht2 : B.t * B.t = 1 := by
    have h := pow_orderOf_eq_one B.t
    rw [B.t_order] at h
    simpa [pow_two] using h
  have htN : B.t ∈ Subgroup.normalizer
      ((Work.GW2.fittingPiIn B.piᶜ M : Subgroup G) : Set G) :=
    le_normalizer_fittingPiIn_local B.piᶜ M hD.t_mem
  refine Work.BMAX.InvolutionInverts (Work.GW2.fittingPiIn B.piᶜ M) B.t ht2 htN ?_
  intro x hx hfix
  have hxH : x ∈ B.Hhat := by
    refine B.H_le_Hhat ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have h' : B.t * x = x * B.t := by
      have h2 := congrArg (· * B.t) hfix
      simpa [mul_assoc] using h2
    exact h'
  have hxbot : x ∈ (⊥ : Subgroup G) := by
    rw [← hFixBot]
    exact ⟨hx, hxH⟩
  exact Subgroup.mem_bot.mp hxbot

end Work.CORE2B
