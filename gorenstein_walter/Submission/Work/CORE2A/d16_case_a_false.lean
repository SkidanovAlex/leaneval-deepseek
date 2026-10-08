/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.thm26_aux
import Submission.Work.CORE2A.fstar_eq_pCore_of_isPGroup
import Submission.Work.DSTR.map_fittingPiIn_le
import Submission.OddOrder.Isaacs.Ch01_Sylow.Basic

/-!
# CORE2A: Bender 1.6(a) is impossible for `X = Ĥ` when `O₂(Ĥ) ≠ 1`

The target theorem `Work.CORE2A.d16_case_a_false` says that in Bender's minimal-counterexample
setting the "case (a)" hypothesis on `Ĥ` — `C_Ĥ(F_{2'}(Ĥ)) ≤ F_{2'}(Ĥ)` — is incompatible with
`O₂(Ĥ) ≠ 1`.

The mathematics is entirely local to the finite group `Ĥ`:

* `O₂(Ĥ)` is a normal `2`-subgroup, hence nilpotent, hence inside the Fitting subgroup `F(Ĥ)`
  (`pCore_le_fitting`); viewed inside `F(Ĥ)` it is a normal `2`-subgroup, so it lies in
  `O₂(F(Ĥ))` (universal property of the `p`-core, `le_pCore_of_normal_isPGroup`);
* `F(Ĥ)` is nilpotent, so its Sylow subgroups are normal and distinct ones commute; in particular
  the `2`-core of `F(Ĥ)` centralizes every prime `q`-core for odd `q`
  (`pCore_le_centralizer_pCore`), and `F_{2'}(Ĥ) = O_{2'}(F(Ĥ))` is the join of those odd
  `q`-cores (`le_iSup_pCore_of_isPiSubgroup`, applied to the `2'`-subgroup `O_{2'}(F(Ĥ))`).
  Hence `O₂(Ĥ) ≤ C_Ĥ(F_{2'}(Ĥ))`;
* the case (a) hypothesis then gives `O₂(Ĥ) ≤ F_{2'}(Ĥ)`, which is a `2'`-group: a `2`-group inside
  a group of odd order is trivial (`eq_bot_of_le_of_isPGroup_two_of_isPiSubgroup_compl`).

The proof of the three group-theoretic inputs is included below; the only imported API is the
`OddOrder.Isaacs.Ch01` development of the Fitting subgroup and Sylow theory of nilpotent groups
(`fitting.isNilpotent`, `iSup_default_sylow_eq_top_of_nilpotent`, `Sylow.normal_of_isNilpotent`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.CORE2A

open scoped MatrixGroups

/-! ## 1. Elementary auxiliary lemmas -/

/-- Pushing subgroups along a homomorphism preserves "is contained in the centralizer of": if
`X ≤ C_H(Y)` then `X.map f ≤ C_K(Y.map f)`. -/
theorem map_le_centralizer_map {H K : Type*} [Group H] [Group K] (f : H →* K)
    {X Y : Subgroup H} (h : X ≤ Subgroup.centralizer (Y : Set H)) :
    X.map f ≤ Subgroup.centralizer ((Y.map f : Subgroup K) : Set K) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  rintro y hy
  obtain ⟨z₀, hz₀, rfl⟩ := Subgroup.mem_map.mp hz
  obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.mp hy
  rw [← map_mul, ← map_mul]
  exact congrArg f ((Subgroup.mem_centralizer_iff.mp (h hz₀)) y₀ hy₀)

/-- `O_p(H)` is a `p`-group (for `H` finite, so that `O_p(H)` agrees with Isaacs' intersection of
the Sylow subgroups). -/
theorem pCore_isPGroup_of_finite {H : Type} [Group H] [Finite H] {p : ℕ} [Fact p.Prime] :
    IsPGroup p ↥(Work.GW2.pCore p H) := by
  rw [Work.CORE2A.pCore_eq_opCore (G := H) (p := p)]
  exact OddOrder.Isaacs.Ch01.opCore_isPGroup p H

/-- Every `p`-subgroup of a finite nilpotent group lies in its `p`-core `O_p`: it is contained in
some Sylow `p`-subgroup, which is normal by nilpotency. -/
theorem le_pCore_of_isPGroup_of_isNilpotent {H : Type} [Group H] [Finite H]
    [Group.IsNilpotent H] {p : ℕ} [Fact p.Prime] {X : Subgroup H} (hX : IsPGroup p X) :
    X ≤ Work.GW2.pCore p H := by
  obtain ⟨Q, hXQ⟩ := hX.exists_le_sylow
  haveI : (Q : Subgroup H).Normal := OddOrder.Isaacs.Ch01.Sylow.normal_of_isNilpotent Q
  exact hXQ.trans (Work.CORE2A.le_pCore_of_normal_isPGroup Q.isPGroup')

/-- Every `π`-subgroup of a finite nilpotent group lies in the join of the prime `q`-cores for
`q ∈ π`.

`N` is nilpotent (a subgroup of the nilpotent `H`), hence the join of its own Sylow subgroups
(`iSup_default_sylow_eq_top_of_nilpotent`); each of these maps into `H` as a `p`-subgroup, so lies
in `O_p(H)` (`le_pCore_of_isPGroup_of_isNilpotent`), and its prime `p` lies in `π`. -/
theorem le_iSup_pCore_of_isPiSubgroup {H : Type} [Group H] [Finite H] [Group.IsNilpotent H]
    (π : Set ℕ) (N : Subgroup H) (hNπ : ∀ q ∈ (Nat.card ↥N).primeFactors, q ∈ π) :
    N ≤ ⨆ (q : ℕ) (_ : q ∈ π) (_ : q.Prime), Work.GW2.pCore q H := by
  have htop : (⊤ : Subgroup ↥N).map N.subtype = N := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← htop, ← OddOrder.Isaacs.Ch01.iSup_default_sylow_eq_top_of_nilpotent ↥N,
    Subgroup.map_iSup]
  refine iSup_le ?_
  rintro ⟨p, hp⟩
  have hpP : p.Prime := Nat.prime_of_mem_primeFactors hp
  haveI : Fact p.Prime := ⟨hpP⟩
  have hpπ : p ∈ π := hNπ p hp
  have hpg : IsPGroup p ↥(((default : Sylow p ↥N) : Subgroup ↥N).map N.subtype) :=
    IsPGroup.map (default : Sylow p ↥N).isPGroup' N.subtype
  refine (le_pCore_of_isPGroup_of_isNilpotent hpg).trans ?_
  exact le_iSup_of_le p (le_iSup_of_le hpπ (le_iSup_of_le hpP le_rfl))

/-- In a finite group, the `p`-core and the `q`-core for distinct primes `p ≠ q` centralize each
other: both are normal, one is a `p`-group and the other a `q`-group, so they are disjoint and
disjoint normal subgroups commute (`Subgroup.commute_of_normal_of_disjoint`). -/
theorem pCore_le_centralizer_pCore {H : Type} [Group H] [Finite H]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q) :
    Work.GW2.pCore p H ≤ Subgroup.centralizer ((Work.GW2.pCore q H : Subgroup H) : Set H) := by
  haveI hpn : (Work.GW2.pCore p H).Normal := Work.GW2.pCore_normal p H
  haveI hqn : (Work.GW2.pCore q H).Normal := Work.GW2.pCore_normal q H
  have hdisj : Disjoint (Work.GW2.pCore p H) (Work.GW2.pCore q H) :=
    IsPGroup.disjoint_of_ne p q hpq _ _
      (pCore_isPGroup_of_finite (H := H) (p := p))
      (pCore_isPGroup_of_finite (H := H) (p := q))
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (Subgroup.commute_of_normal_of_disjoint _ _ hpn hqn hdisj x y hx hy).eq.symm

/-- A `2`-group contained in a `2'`-group is trivial. -/
theorem eq_bot_of_le_of_isPGroup_two_of_isPiSubgroup_compl {L : Type} [Group L] [Finite L]
    {P E : Subgroup L} (hP : IsPGroup 2 ↥P)
    (hE : Subgroup.IsPiSubgroup ({2}ᶜ : Set ℕ) E) (h : P ≤ E) : P = ⊥ := by
  rw [← Subgroup.card_eq_one]
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hdvd : 2 ^ n ∣ Nat.card ↥E := by
    rw [← hn]
    exact Subgroup.card_dvd_of_le h
  have hodd : Odd (Nat.card ↥E) := by
    refine Nat.not_even_iff_odd.mp fun hev => ?_
    have h2 : 2 ∣ Nat.card ↥E := even_iff_two_dvd.mp hev
    have hmem : 2 ∈ (Nat.card ↥E).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, Nat.card_pos.ne'⟩
    exact absurd (hE 2 hmem) (by simp)
  have hodd2 : Odd (2 ^ n) := Odd.of_dvd_nat hodd hdvd
  have hn0 : n = 0 := by
    by_contra hnne
    have hge : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hnne
    have h2dvd : 2 ∣ 2 ^ n := ⟨2 ^ (n - 1), by rw [← pow_succ', Nat.sub_add_cancel hge]⟩
    exact absurd (even_iff_two_dvd.mpr h2dvd) (Nat.not_even_iff_odd.mpr hodd2)
  rw [hn, hn0, pow_zero]

/-! ## 2. The local statement: `O₂(G) ≤ C_G(O_{2'}(F(G)))` -/

/-- `O₂(G)` centralizes `F_{2'}(G) = O_{2'}(F(G))`: `O₂(G) ≤ O₂(F(G))` because `F(G)` carries a
normal `2`-subgroup isomorphic to `O₂(G)`, and `O_{2'}(F(G))` is the join of the `O_q(F(G))` for
odd primes `q`, each of which centralizes `O₂(F(G))` by nilpotency of `F(G)`. -/
theorem pCore_two_le_centralizer_fittingPi_two_compl (L : Type) [Group L] [Finite L] :
    Work.GW2.pCore 2 L ≤ Subgroup.centralizer
      ((Work.GW2.fittingPi ({2}ᶜ : Set ℕ) L : Subgroup L) : Set L) := by
  haveI hFnil : Group.IsNilpotent ↥(Work.GW2.fitting L) := by
    rw [Work.CORE2A.fitting_eq_isaacsFitting]
    infer_instance
  have hPF : Work.GW2.pCore 2 L ≤ Work.GW2.fitting L :=
    Work.CORE2A.pCore_le_fitting (G := L) (p := 2)
  -- Step 1: `O₂(L)` lies in `O₂(F(L))` (pushed into `L`)
  have hA : Work.GW2.pCore 2 L ≤
      (Work.GW2.pCore 2 ↥(Work.GW2.fitting L)).map (Work.GW2.fitting L).subtype := by
    haveI : ((Work.GW2.pCore 2 L).subgroupOf (Work.GW2.fitting L)).Normal :=
      (Work.GW2.pCore_normal 2 L).subgroupOf (Work.GW2.fitting L)
    have hpg : IsPGroup 2 ↥((Work.GW2.pCore 2 L).subgroupOf (Work.GW2.fitting L)) :=
      (pCore_isPGroup_of_finite (H := L) (p := 2)).of_equiv
        (Subgroup.subgroupOfEquivOfLe hPF).symm
    have hle : (Work.GW2.pCore 2 L).subgroupOf (Work.GW2.fitting L) ≤
        Work.GW2.pCore 2 ↥(Work.GW2.fitting L) :=
      Work.CORE2A.le_pCore_of_normal_isPGroup hpg
    have hmap := Subgroup.map_mono (f := (Work.GW2.fitting L).subtype) hle
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPF] at hmap
  -- Step 2: the odd prime cores of `F(L)` centralize `O₂(F(L))`
  have hsup : (⨆ (q : ℕ) (_ : q ∈ ({2}ᶜ : Set ℕ)) (_ : q.Prime),
        (Work.GW2.pCore q ↥(Work.GW2.fitting L)).map (Work.GW2.fitting L).subtype) ≤
      Subgroup.centralizer
        (((Work.GW2.pCore 2 ↥(Work.GW2.fitting L)).map
          (Work.GW2.fitting L).subtype) : Set L) := by
    refine iSup_le fun q => iSup_le fun hq => iSup_le fun hqp => ?_
    haveI : Fact q.Prime := ⟨hqp⟩
    have hq2 : q ≠ 2 := by simpa using hq
    exact Subgroup.le_centralizer_iff.mpr
      (map_le_centralizer_map (Work.GW2.fitting L).subtype
        (pCore_le_centralizer_pCore (H := ↥(Work.GW2.fitting L)) (p := 2) (q := q)
          (Ne.symm hq2)))
  -- Step 3: `F_{2'}(L) = O_{2'}(F(L))` lies in that join
  have hE : Work.GW2.fittingPi ({2}ᶜ : Set ℕ) L ≤
      ⨆ (q : ℕ) (_ : q ∈ ({2}ᶜ : Set ℕ)) (_ : q.Prime),
        (Work.GW2.pCore q ↥(Work.GW2.fitting L)).map (Work.GW2.fitting L).subtype := by
    have h2 : (Work.GW2.piCore ({2}ᶜ : Set ℕ) ↥(Work.GW2.fitting L)).map
        (Work.GW2.fitting L).subtype ≤
        ⨆ (q : ℕ) (_ : q ∈ ({2}ᶜ : Set ℕ)) (_ : q.Prime),
          (Work.GW2.pCore q ↥(Work.GW2.fitting L)).map (Work.GW2.fitting L).subtype := by
      simpa only [Subgroup.map_iSup] using
        Subgroup.map_mono (f := (Work.GW2.fitting L).subtype)
          (le_iSup_pCore_of_isPiSubgroup ({2}ᶜ : Set ℕ)
            (Work.GW2.piCore ({2}ᶜ : Set ℕ) ↥(Work.GW2.fitting L))
            (Work.DSTR.FittingPiImg.isPiSubgroup_piCore ({2}ᶜ : Set ℕ)))
    exact h2
  have hsup' : (Work.GW2.pCore 2 ↥(Work.GW2.fitting L)).map (Work.GW2.fitting L).subtype ≤
      Subgroup.centralizer ((⨆ (q : ℕ) (_ : q ∈ ({2}ᶜ : Set ℕ)) (_ : q.Prime),
        (Work.GW2.pCore q ↥(Work.GW2.fitting L)).map (Work.GW2.fitting L).subtype :
          Subgroup L) : Set L) :=
    Subgroup.le_centralizer_iff.mp hsup
  refine hA.trans (hsup'.trans ?_)
  exact Subgroup.centralizer_le fun _ hx => hE hx

/-! ## 3. The target theorem -/

/-- Bender 1.6(a) cannot occur for `X = Ĥ` when `O₂(Ĥ) ≠ 1`.

`O₂(Ĥ)` is a normal `2`-subgroup of `Ĥ`, hence nilpotent, hence contained in the Fitting subgroup
`F(Ĥ)`, and it commutes with `F_{2'}(Ĥ) = O_{2'}(F(Ĥ))` because `F(Ĥ)` is nilpotent.  So
`O₂(Ĥ) ≤ C_Ĥ(F_{2'}(Ĥ))`; case (a) would put it inside the odd group `F_{2'}(Ĥ)`, forcing
`O₂(Ĥ) = 1`.

Useful inputs: `Work.CORE2A.pCoreIn_isPGroup`, `Submission.Work.CORE2A.thm26_aux`
(`fitting_eq_isaacsFitting`) with `OddOrder.Isaacs.Ch01.fitting.isNilpotent`, and the fact that
in a nilpotent group the `p`-Sylow subgroups are normal, so `[O₂(F), O_{2'}(F)] = 1`. -/
theorem d16_case_a_false (T : Work.GW2.LocalToolkit) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ B : Work.GW2.BenderSetup G, Work.GW2.pCoreIn 2 B.Hhat ≠ ⊥ →
        (Subgroup.centralizer ((Work.GW2.fittingPi {2}ᶜ ↥B.Hhat : Subgroup ↥B.Hhat) : Set ↥B.Hhat) ≤
          Work.GW2.fittingPi {2}ᶜ ↥B.Hhat) → False := by
  intro G _ _ _ _ B hne hcent
  -- `O₂(Ĥ) ≠ 1` as a subgroup of `Ĥ`
  have hPne : Work.GW2.pCore 2 ↥B.Hhat ≠ ⊥ := fun h =>
    hne ((Subgroup.map_eq_bot_iff_of_injective (Work.GW2.pCore 2 ↥B.Hhat)
      B.Hhat.subtype_injective).mpr h)
  refine hPne (eq_bot_of_le_of_isPGroup_two_of_isPiSubgroup_compl
    (P := Work.GW2.pCore 2 ↥B.Hhat) (E := Work.GW2.fittingPi ({2}ᶜ : Set ℕ) ↥B.Hhat) ?_ ?_ ?_)
  · rw [Work.CORE2A.pCore_eq_opCore (G := ↥B.Hhat) (p := 2)]
    exact OddOrder.Isaacs.Ch01.opCore_isPGroup 2 ↥B.Hhat
  · show Subgroup.IsPiSubgroup ({2}ᶜ : Set ℕ)
      ((Work.GW2.piCore ({2}ᶜ : Set ℕ) ↥(Work.GW2.fitting ↥B.Hhat)).map
        (Work.GW2.fitting ↥B.Hhat).subtype)
    exact Work.DSTR.FittingPiImg.isPiSubgroup_map (f := (Work.GW2.fitting ↥B.Hhat).subtype)
      (Work.DSTR.FittingPiImg.isPiSubgroup_piCore ({2}ᶜ : Set ℕ))
  · exact (pCore_two_le_centralizer_fittingPi_two_compl ↥B.Hhat).trans hcent

end Work.CORE2A
