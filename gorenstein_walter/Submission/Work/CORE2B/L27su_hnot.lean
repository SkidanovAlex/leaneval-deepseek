import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.UNeBotProp_of_h22_proved
import Submission.Work.CORE2B.isQuasisimple_four_dvd
import Submission.Work.CORE2B.isPGroup_pCoreIn_two
import Submission.Work.CORE2B.oddCore_odd
import Submission.Work.RED.DihOrCycSubgroup
import Submission.Work.RED.DihedralSubgroup
import Submission.Work.CORE2B.L27_solvable_base

/-!
# `Work.CORE2B.L27su_hnot` — `F*(Ĥ)` is never a `p`-group

Bender 1981, Lemma 2.3(i) is stated with the rider "*unless* `F*(Ĥ)` is a `p`-group", and its
consumers in Lemma 2.7 need to know that this exception never occurs (in the minimal
counterexample, with Bender 2.2 and Theorem 2.6 available).  This file proves exactly that:

  `¬ ∃ p, p.Prime ∧ IsPGroup p (F*(Ĥ))`.

## The argument

Write `X := ↥Ĥ`, `U = O(H) = O(Ĥ)` (Theorem 2.6(i)) and let `p` be a prime with `F*(Ĥ)` a
`p`-group, so that `F*(Ĥ)` has order `p ^ n` and, by `F* = F · E`, is also equal to `O_p(Ĥ)`.

* `t ∈ S` and `U ≤ H = C_G(t)`, so `t ∈ S ⊓ C(U) = O₂(Ĥ)` (Theorem 2.6(ii)).
* **`p` odd** is impossible: `O₂(Ĥ) ≤ F(Ĥ) ≤ F*(Ĥ)` contains the element `t` of order `2`, so
  `2` divides `|F*(Ĥ)| = p ^ n`, which is odd.
* **`p = 2`** is impossible: `U = O(Ĥ) ◁ Ĥ` has odd order and `F*(Ĥ)` is a `2`-group, so `U`
  and `F*(Ĥ)` are normal subgroups of `Ĥ` of coprime orders; they commute, i.e.
  `U ≤ C_Ĥ(F*(Ĥ))`.  `Ĥ ≠ ⊤` is a maximal subgroup of the minimal counterexample, hence a
  `D`-group (`BenderCtx.ih` + heredity of `DihOrCycSylow`), so Bender 1.6 gives
  `C_Ĥ(F*(Ĥ)) ≤ F*(Ĥ)` (`FStarProp`, the `fstar` field of the toolkit).  Thus `U ≤ F*(Ĥ)`,
  which is impossible for a nontrivial odd group inside a `2`-group; so `U = ⊥`, contradicting
  Bender 2.2 (`UNeBotProp_of_h22`).

The three `F*`/`O_p` facts used are proved inline below (the copies in the `CORE2A`/`BMAX`
areas live in a parallel — definitionally equal but not simultaneously importable — copy of the
`Work.GW2` vocabulary).
-/

open scoped MatrixGroups

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.CORE2B

open Subgroup

/-! ## 1. Elementary `F*`-vocabulary -/

/-- `F(K) ≤ F*(K)`. -/
theorem L27su_fittingIn_le_fstarIn {G : Type} [Group G] (K : Subgroup G) :
    Work.GW2.fittingIn K ≤ Work.GW2.fstarIn K := by
  rw [Work.GW2.fittingIn, Work.GW2.fstarIn, Work.GW2.fstar]
  exact Subgroup.map_mono le_sup_left

/-- `O₂(K) ≤ F(K)`: a normal `2`-subgroup is nilpotent. -/
theorem L27su_pCoreIn_le_fittingIn {G : Type} [Group G] [Finite G] (K : Subgroup G) :
    Work.GW2.pCoreIn 2 K ≤ Work.GW2.fittingIn K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Work.GW2.pCoreIn, Work.GW2.fittingIn]
  exact Subgroup.map_mono (pCore_le_fitting_local 2)

/-- The universal property of `O_p(X)`: a normal `p`-subgroup lies in `O_p(X)`. -/
theorem L27su_le_pCore_of_normal_isPGroup {X : Type} [Group X] {p : ℕ} {N : Subgroup X}
    [N.Normal] (hN : IsPGroup p N) : N ≤ Work.GW2.pCore p X := by
  rw [Work.GW2.pCore]
  exact Subgroup.normal_le_normalCore.mpr (le_sSup ⟨‹N.Normal›, hN⟩)

/-- If `F*(X)` is a `p`-group then `F*(X) = O_p(X)`: both pieces of `F*(X) = F(X) E(X)` are
normal subgroups of the `p`-group `F*(X)`, hence `p`-subgroups, hence lie in `O_p(X)`; and
conversely `O_p(X) ≤ F(X) ≤ F*(X)`. -/
theorem L27su_fstar_eq_pCore_of_isPGroup {X : Type} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (h : IsPGroup p (Work.GW2.fstar X)) :
    Work.GW2.fstar X = Work.GW2.pCore p X := by
  refine le_antisymm ?_ ?_
  · rw [Work.GW2.fstar]
    refine sup_le ?_ ?_
    · haveI : (Work.GW2.fitting X).Normal := Subgroup.normalCore_normal _
      exact L27su_le_pCore_of_normal_isPGroup (IsPGroup.to_le h le_sup_left)
    · rw [Work.GW2.layer]
      refine sSup_le ?_
      intro E hE
      haveI : E.Normal := hE.1
      exact L27su_le_pCore_of_normal_isPGroup
        (IsPGroup.to_le h ((le_sSup hE).trans le_sup_right))
  · rw [Work.GW2.fstar]
    exact (pCore_le_fitting_local p).trans le_sup_left

/-- Every subgroup of a group with cyclic or dihedral Sylow `2`-subgroups again has cyclic or
dihedral Sylow `2`-subgroups (area `RED`, `Work.RED.DihOrCycSubgroup`). -/
theorem L27su_dihOrCycSylow_subtype {G : Type} [Group G] [Finite G]
    (h : Work.GW2.DihOrCycSylow G) (N : Subgroup G) : Work.GW2.DihOrCycSylow ↥N :=
  Work.RED.DihOrCycSubgroup (fun n _ H => Work.RED.DihedralSubgroup n H) N h

/-! ## 2. The theorem -/

theorem L27su_hnot :
    ∀ (T : Work.GW2.LocalToolkit) (h22 : Work.GW2.Lemma22Prop) (h26 : Work.GW2.Thm26Prop)
      (G : Type) [Group G] [Finite G],
      Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ B : Work.GW2.BenderSetup G,
        ¬ ∃ p : ℕ, p.Prime ∧ IsPGroup p (Work.GW2.fstarIn B.Hhat) := by
  intro T h22 h26 G _ _ hFT hCtx B hpg
  obtain ⟨p, hpp, hpgp⟩ := hpg
  haveI : Fact p.Prime := ⟨hpp⟩
  -- Theorem 2.6: `O(Ĥ) = U` and `O₂(Ĥ) = S ⊓ C(U)`.
  obtain ⟨h26a, h26b, -⟩ := h26 G hFT hCtx B
  -- `t ∈ S` and `U ≤ H = C_G(t)`, hence `t ∈ S ⊓ C(U) = O₂(Ĥ)`.
  have htS : B.t ∈ (B.S : Subgroup G) := B.S0_le B.t_mem
  have htCU : B.t ∈ Subgroup.centralizer (B.U : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have huH : u ∈ B.H := Subgroup.map_subtype_le _ hu
    exact (Subgroup.mem_centralizer_iff.mp huH B.t (by simp)).symm
  have htO2 : B.t ∈ Work.GW2.pCoreIn 2 B.Hhat := by
    rw [← h26b]
    exact ⟨htS, htCU⟩
  -- `t ∈ O₂(Ĥ) ≤ F(Ĥ) ≤ F*(Ĥ)`
  have htF : B.t ∈ Work.GW2.fstarIn B.Hhat :=
    L27su_fittingIn_le_fstarIn B.Hhat (L27su_pCoreIn_le_fittingIn B.Hhat htO2)
  rcases eq_or_ne p 2 with hp2 | hp2
  · -- ## `p = 2`
    subst hp2
    have hpg2 : IsPGroup 2 (Work.GW2.fstarIn B.Hhat) := hpgp
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    -- `↥Ĥ` is a `D`-group, so `F*` is self-centralizing in it (`FStarProp`).
    have hdih : Work.GW2.DihOrCycSylow ↥B.Hhat :=
      L27su_dihOrCycSylow_subtype hCtx.sylow B.Hhat
    have hDG : Work.GW2.IsDGroup ↥B.Hhat :=
      hCtx.ih ↥B.Hhat (Subgroup.card_lt_card_of_ne_top B.Hhat_coatom.ne_top) hdih
    have hSC : Subgroup.centralizer (Work.GW2.fstar ↥B.Hhat : Set ↥B.Hhat) ≤
        Work.GW2.fstar ↥B.Hhat := T.fstar ↥B.Hhat hFT hdih hDG
    -- `F*(↥Ĥ)` is a `2`-group, hence equals `O₂(↥Ĥ)`.
    have hfX : IsPGroup 2 (Work.GW2.fstar ↥B.Hhat) :=
      IsPGroup.of_equiv hpg2 (Subgroup.equivMapOfInjective (Work.GW2.fstar ↥B.Hhat)
        B.Hhat.subtype B.Hhat.subtype_injective).symm
    have hfstar_eq : Work.GW2.fstar ↥B.Hhat = Work.GW2.pCore 2 ↥B.Hhat :=
      L27su_fstar_eq_pCore_of_isPGroup hfX
    -- `O(↥Ĥ)` has odd order, `O₂(↥Ĥ)` is a `2`-group: they are normal and disjoint.
    haveI hQn : (Work.GW2.oddCore ↥B.Hhat).Normal := Work.GW2.oddCore_normal _
    haveI hPn : (Work.GW2.pCore 2 ↥B.Hhat).Normal := Work.GW2.pCore_normal 2 _
    have hoddQ : Odd (Nat.card (Work.GW2.oddCore ↥B.Hhat)) := oddCore_odd
    have hP2 : IsPGroup 2 (Work.GW2.pCore 2 ↥B.Hhat) :=
      IsPGroup.of_equiv (isPGroup_pCoreIn_two B.Hhat)
        (Subgroup.equivMapOfInjective (Work.GW2.pCore 2 ↥B.Hhat) B.Hhat.subtype
          B.Hhat.subtype_injective).symm
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP2
    have hcop : Nat.Coprime (Nat.card (Work.GW2.oddCore ↥B.Hhat))
        (Nat.card (Work.GW2.pCore 2 ↥B.Hhat)) := by
      rw [hn]
      exact (Nat.coprime_two_right.mpr hoddQ).pow_right n
    have hdisj : Disjoint (Work.GW2.oddCore ↥B.Hhat) (Work.GW2.pCore 2 ↥B.Hhat) :=
      Subgroup.disjoint_of_coprime_natCard hcop
    -- Coprime normal subgroups commute, so `O(↥Ĥ) ≤ C(F*(↥Ĥ)) ≤ F*(↥Ĥ)`.
    have hcent : Work.GW2.oddCore ↥B.Hhat ≤
        Subgroup.centralizer (Work.GW2.fstar ↥B.Hhat : Set ↥B.Hhat) := by
      intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : y ∈ Work.GW2.pCore 2 ↥B.Hhat := by
        rwa [hfstar_eq] at hy
      exact (Subgroup.commute_of_normal_of_disjoint _ _ hQn hPn hdisj q y hq hy').symm
    have hQle : Work.GW2.oddCore ↥B.Hhat ≤ Work.GW2.pCore 2 ↥B.Hhat := by
      rw [← hfstar_eq]
      exact hcent.trans hSC
    have hQbot : Work.GW2.oddCore ↥B.Hhat = ⊥ := by
      refine le_bot_iff.mp ?_
      calc Work.GW2.oddCore ↥B.Hhat
          ≤ Work.GW2.oddCore ↥B.Hhat ⊓ Work.GW2.pCore 2 ↥B.Hhat := le_inf le_rfl hQle
        _ ≤ ⊥ := hdisj.le_bot
    -- Hence `U = O(Ĥ) = ⊥`, contradicting Bender 2.2.
    have hUbot : B.U = ⊥ := by
      rw [← h26a]
      show (Work.GW2.oddCore ↥B.Hhat).map B.Hhat.subtype = ⊥
      rw [hQbot, Subgroup.map_bot]
    exact (UNeBotProp_of_h22_proved h22 G hFT hCtx B) hUbot
  · -- ## `p` odd
    -- `t ∈ F*(Ĥ)` has order `2`, so `2 ∣ |F*(Ĥ)| = p ^ n` with `p ^ n` odd.
    have hodd : Odd (Nat.card (Work.GW2.fstarIn B.Hhat)) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpgp
      rw [hn]
      exact Odd.pow (hpp.odd_of_ne_two hp2)
    have h2dvd : 2 ∣ Nat.card (Work.GW2.fstarIn B.Hhat) := by
      have h := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr htF)
      rwa [Nat.card_zpowers, B.t_order] at h
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2dvd)

end Work.CORE2B
