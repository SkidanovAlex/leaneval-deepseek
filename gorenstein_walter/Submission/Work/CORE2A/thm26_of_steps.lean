/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.Extra
import Submission.Work.CORE2A.thm26_aux

/-!
# CORE2A: Bender's Theorem 2.6 assembled from its three steps

The statement of Bender 1981, Theorem 2.6, is `Work.GW2.Thm26Prop`.  Its proof is split into
the three steps `Work.GW2.Thm26aProp` (`O₂(Ĥ) ≠ 1` gives the whole conclusion), `Thm26bProp`
(`E(Ĥ) = 1`) and `Thm26cProp` (`t` centralizes every `H`-invariant odd `p`-subgroup).  This
file is the assembly.

**The mathematics of the assembly.**  Only the case `O₂(Ĥ) = 1` is not covered by
`Thm26aProp`, and it is *empty*:

* by `Thm26bProp`, `E(Ĥ) = 1`, so `F*(Ĥ) = F(Ĥ)`;
* `O₂(Ĥ) = 1` makes `F(Ĥ)` a group of odd order (`F(Ĥ)` is nilpotent, so its Sylow
  2-subgroup is characteristic in `F(Ĥ)` and hence normal in `Ĥ`, therefore contained in
  `O₂(Ĥ) = 1`);
* `F(Ĥ) ◁ Ĥ` and `H ≤ Ĥ`, so `H` normalizes every characteristic subgroup of `F(Ĥ)`, in
  particular each of its (odd) Sylow subgroups; `Thm26cProp` then gives `F(Ĥ) ≤ C_G(t) ⊆ Ĥ`,
  i.e. `t ∈ C_Ĥ(F*(Ĥ))`;
* `Ĥ` contains the Sylow 2-subgroup `S` of `G`, so `Ĥ` is a proper subgroup of `G` with a
  cyclic or dihedral Sylow 2-subgroup, hence a D-group by the induction hypothesis
  (`BenderCtx.ih`), and `FStarProp` (a field of `LocalToolkit`) gives
  `C_Ĥ(F*(Ĥ)) ≤ F*(Ĥ)`.  So `t ∈ F*(Ĥ) = F(Ĥ)`, contradicting the oddness of `F(Ĥ)`.

The contradiction is `thm26_contra` below; `thm26_of_steps` is then a two-line case split.
-/

open scoped MatrixGroups

namespace Work.CORE2A

open Subgroup

/-! ## 1. `DihOrCycSylow` is inherited by a subgroup containing a Sylow 2-subgroup -/

/-- If `S` is a Sylow 2-subgroup of `G` contained in `K`, then every Sylow 2-subgroup of `K`
is isomorphic to `S`, hence `DihOrCycSylow G` passes to `↥K`. -/
theorem dihOrCycSylow_of_sylow_le {G : Type} [Group G] [Finite G]
    (h : Work.GW2.DihOrCycSylow G) (K : Subgroup G) (S : Sylow 2 G)
    (hS : (S : Subgroup G) ≤ K) : Work.GW2.DihOrCycSylow ↥K := by
  intro Q
  have e : ↥(Q : Subgroup ↥K) ≃* ↥(S : Subgroup G) :=
    (Sylow.equiv Q (S.subtype hS)).trans (Subgroup.subgroupOfEquivOfLe hS)
  rcases h S with hcyc | ⟨n, ⟨e'⟩⟩
  · left
    haveI : IsCyclic ↥(S : Subgroup G) := hcyc
    exact (MulEquiv.isCyclic e).mpr inferInstance
  · exact Or.inr ⟨n, ⟨e.trans e'⟩⟩

/-! ## 2. `F(X)` contains no `p`-element when `O_p(X) = 1` -/

/-- `F(X)` is nilpotent, so its Sylow `p`-subgroup is normal in `X`; hence every element of
order dividing the prime `p` inside `F(X)` lies in `O_p(X)`. -/
theorem eq_one_of_mem_fitting_of_pCore_eq_bot {X : Type} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (h : Work.GW2.pCore p X = ⊥) {x : X}
    (hx : x ∈ Work.GW2.fitting X) (hxp : x ^ p = 1) : x = 1 := by
  rw [Work.CORE2A.pCore_eq_opCore] at h
  rw [Work.CORE2A.fitting_eq_isaacsFitting] at hx
  let N : Subgroup X := OddOrder.Isaacs.Ch01.fitting X
  haveI hNnorm : N.Normal := OddOrder.Isaacs.Ch01.fitting.normal X
  haveI hNnil : Group.IsNilpotent N := OddOrder.Isaacs.Ch01.fitting.isNilpotent
  have hxN : x ∈ N := hx
  let xN : N := ⟨x, hxN⟩
  have hxpow : xN ^ p = 1 := by
    apply Subtype.ext
    simpa using hxp
  have hdvd : orderOf xN ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hxpow
  have hpg : IsPGroup p ↥(Subgroup.zpowers xN) := by
    rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd (orderOf xN) hdvd with h1 | hp
    · refine IsPGroup.of_card (n := 0) ?_
      rw [pow_zero, ← h1, Nat.card_zpowers]
    · refine IsPGroup.of_card (n := 1) ?_
      rw [pow_one, ← hp, Nat.card_zpowers]
  obtain ⟨P, hxP⟩ := hpg.exists_le_sylow
  have hPnorm : (P : Subgroup N).Normal :=
    OddOrder.Isaacs.Ch01.Sylow.normal_of_isNilpotent P
  have hPchar : (P : Subgroup N).Characteristic := Sylow.characteristic_of_normal P hPnorm
  have hlem : (P : Subgroup N).map N.subtype ≤ OddOrder.Isaacs.Ch01.opCore p X := by
    haveI : ((P : Subgroup N).map N.subtype).Normal := inferInstance
    exact OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore ((P.2).map N.subtype)
  have hxmap : x ∈ (P : Subgroup N).map N.subtype :=
    ⟨xN, hxP (Subgroup.mem_zpowers xN), rfl⟩
  have hxoc : x ∈ OddOrder.Isaacs.Ch01.opCore p X := hlem hxmap
  rw [h] at hxoc
  simpa using hxoc

/-! ## 3. `26c` makes `t` centralize all of `F(Ĥ)` when `O₂(Ĥ) = 1` -/

/-- If every odd `p`-subgroup normalized by `K` is centralized by `t`, and `O₂(K) = 1`, then
`F(K)` is centralized by `t`: `F(K)` is the product of its Sylow subgroups, each of which is
characteristic in `F(K) ◁ K` and therefore normalized by `K`. -/
theorem fittingIn_le_centralizer_of_forall {G : Type} [Group G] [Finite G] (K : Subgroup G)
    (t : G) (h2 : Work.GW2.pCoreIn 2 K = ⊥)
    (hodd : ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ P : Subgroup G, IsPGroup p P →
        K ≤ Subgroup.normalizer (P : Set G) → P ≤ Subgroup.centralizer ({t} : Set G)) :
    Work.GW2.fittingIn K ≤ Subgroup.centralizer ({t} : Set G) := by
  rw [Work.GW2.fittingIn]
  have hfit : (Work.GW2.fitting ↥K : Subgroup ↥K)
      = ⨆ p : Nat.Primes, OddOrder.Isaacs.Ch01.opCore (p : ℕ) ↥K := by
    rw [Work.CORE2A.fitting_eq_isaacsFitting]
    rfl
  rw [hfit, Subgroup.map_iSup]
  refine iSup_le (fun p => ?_)
  by_cases hp2 : (p : ℕ) = 2
  · have hthis : (OddOrder.Isaacs.Ch01.opCore (p : ℕ) ↥K).map K.subtype
        = Work.GW2.pCoreIn 2 K := by
      rw [hp2, ← Work.CORE2A.pCore_eq_opCore]
      rfl
    rw [hthis, h2]
    exact bot_le
  · haveI : Fact (Nat.Prime (p : ℕ)) := ⟨p.2⟩
    refine hodd (p : ℕ) p.2 hp2 _ ?_ ?_
    · exact (OddOrder.Isaacs.Ch01.opCore_isPGroup (p : ℕ) ↥K).map K.subtype
    · rw [Subgroup.le_normalizer_iff]
      intro h hh y hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      have hz' : (⟨h, hh⟩ : ↥K) * z * (⟨h, hh⟩ : ↥K)⁻¹
          ∈ OddOrder.Isaacs.Ch01.opCore (p : ℕ) ↥K :=
        (OddOrder.Isaacs.Ch01.opCore.normal (p : ℕ) ↥K).conj_mem z hz ⟨h, hh⟩
      exact Subgroup.mem_map.mpr ⟨_, hz', by simp⟩

/-! ## 4. The case `O₂(Ĥ) = 1` is empty -/

/-- Under the hypotheses of `Work.GW2.Thm26Prop`, `O₂(Ĥ) ≠ 1`. -/
theorem thm26_contra {G : Type} [Group G] [Finite G] (T : Work.GW2.LocalToolkit)
    (h26b : Work.GW2.Thm26bProp) (h26c : Work.GW2.Thm26cProp)
    (hFT : Work.GW2.FeitThompsonProp) (hctx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h : Work.GW2.pCoreIn 2 B.Hhat = ⊥) : False := by
  have hlayer : Work.GW2.layerIn B.Hhat = ⊥ := h26b G hFT hctx B
  have hlayer' : Work.GW2.layer ↥B.Hhat = ⊥ := layer_eq_bot_of_layerIn_eq_bot hlayer
  have htop : B.Hhat ≠ ⊤ := ne_of_lt B.Hhat_coatom.lt_top
  have hcard : Nat.card ↥B.Hhat < Nat.card G := card_lt_card_of_ne_top htop
  have hdih : Work.GW2.DihOrCycSylow ↥B.Hhat :=
    dihOrCycSylow_of_sylow_le hctx.sylow B.Hhat B.S (bSetup_S_le_Hhat B)
  have hDG : Work.GW2.IsDGroup ↥B.Hhat := hctx.ih ↥B.Hhat hcard hdih
  have hSC : Subgroup.centralizer (Work.GW2.fstar ↥B.Hhat : Set ↥B.Hhat)
      ≤ Work.GW2.fstar ↥B.Hhat := T.fstar ↥B.Hhat hFT hdih hDG
  -- `26c`: `t` centralizes `F(Ĥ)`.
  have hcent : Work.GW2.fittingIn B.Hhat ≤ Subgroup.centralizer ({B.t} : Set G) :=
    fittingIn_le_centralizer_of_forall B.Hhat B.t h
      (fun p hp hp2 P hP hN => h26c G hFT hctx B p hp hp2 P hP (le_trans B.H_le_Hhat hN))
  have hfstar : Work.GW2.fstarIn B.Hhat = Work.GW2.fittingIn B.Hhat :=
    fstarIn_eq_fittingIn_of_layerIn_eq_bot hlayer
  -- the element `t` of `↥Ĥ` centralizes `F*(Ĥ)`
  have hmem : (⟨B.t, bSetup_t_mem_Hhat B⟩ : ↥B.Hhat)
      ∈ Subgroup.centralizer (Work.GW2.fstar ↥B.Hhat : Set ↥B.Hhat) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    show (y : G) * B.t = B.t * (y : G)
    have hyG : (y : G) ∈ Work.GW2.fstarIn B.Hhat := ⟨y, hy, rfl⟩
    have hyF : (y : G) ∈ Work.GW2.fittingIn B.Hhat := hfstar ▸ hyG
    have hcent' := hcent hyF
    rw [Subgroup.mem_centralizer_iff] at hcent'
    exact (hcent' B.t (by simp)).symm
  -- `F*` is self-centralizing in the D-group `↥Ĥ`, so `t ∈ F*(Ĥ) = F(Ĥ)`
  have ht' : (⟨B.t, bSetup_t_mem_Hhat B⟩ : ↥B.Hhat) ∈ Work.GW2.fstar ↥B.Hhat := hSC hmem
  have ht'fit : (⟨B.t, bSetup_t_mem_Hhat B⟩ : ↥B.Hhat) ∈ Work.GW2.fitting ↥B.Hhat := by
    have h' := ht'
    rwa [Work.GW2.fstar, hlayer', sup_bot_eq] at h'
  -- but `F(Ĥ)` contains no element of order `2`
  have hp2 : Work.GW2.pCore 2 ↥B.Hhat = ⊥ := pCore_eq_bot_of_pCoreIn_eq_bot h
  have hpow : (⟨B.t, bSetup_t_mem_Hhat B⟩ : ↥B.Hhat) ^ 2 = 1 := by
    apply Subtype.ext
    have hpowT : B.t ^ 2 = 1 := by
      have := pow_orderOf_eq_one B.t
      rwa [B.t_order] at this
    simpa using hpowT
  have hone : (⟨B.t, bSetup_t_mem_Hhat B⟩ : ↥B.Hhat) = 1 :=
    eq_one_of_mem_fitting_of_pCore_eq_bot hp2 ht'fit hpow
  have htone : B.t = 1 := by
    have := congrArg (fun z : ↥B.Hhat => (z : G)) hone
    simpa using this
  exact bSetup_t_ne_one B htone

/-! ## 5. The assembly -/

theorem thm26_of_steps (T : Work.GW2.LocalToolkit) (h26a : Work.GW2.Thm26aProp) (h26b : Work.GW2.Thm26bProp) (h26c : Work.GW2.Thm26cProp) : Work.GW2.Thm26Prop := by
  intro G _ _ hFT hctx B
  by_cases h : Work.GW2.pCoreIn 2 B.Hhat = ⊥
  · exact (thm26_contra T h26b h26c hFT hctx B h).elim
  · exact h26a G hFT hctx B h

end Work.CORE2A
