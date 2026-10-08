import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.PSU3.BenderST
import Submission.Work.PSU3.StageB.Frame
import Submission.Work.PSU3.StageA.centD_eq_centralizer_s
import Submission.Work.PSU3.StageA.centD_ne_bot
import Submission.Work.PSU3.StageA.distinguished_exists
import Submission.Work.PSU3.RankOne.H16
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ThmF.ChV12.corProp2
import Submission.Work.ThmF.ChV12.prop3
import Submission.Work.ThmF.Bender.DTransitiveInv
import Submission.Work.ThmF.Bender.cardKsetEqInv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-- A nontrivial subgroup contains a nontrivial element. -/
private lemma exists_ne_one_of_ne_bot {G : Type} [Group G] {W : Subgroup G} (h : W ≠ ⊥) :
    ∃ w ∈ W, w ≠ 1 := by
  by_contra hcon
  push Not at hcon
  exact h (eq_bot_iff.mpr (fun x hx => Subgroup.mem_bot.mpr (hcon x hx)))

/-- **`K = J(D,t)` is cyclic as soon as `W = C_V(K) ≠ 1`.**

This is Peterfalvi II Ch. V §1 Prop. 2 in the case `W ≠ 1`, and it needs *no* Appendix X /
Feit–Thompson input: take `w ∈ W#` and `X = ⟨w⟩`.  Every element of `Kset H t` commutes with `w`
(as `w ∈ W = C_V(K)`), so all of `Kset H t` normalises `X`, and the cyclic subgroup `N` produced
by Ch. II §4 Prop. 3 (d) (`ChIIFourProp` P3 with `Y = X`) equals `Kset H t`.  Hence `Kset H t`
is a subgroup, and it is cyclic. -/
theorem Ksub_eq_Kset_of_W_ne_bot {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hW : Work.ThmF.W H t ≠ ⊥) :
    (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t ∧ IsCyclic ↥(Work.ThmF.Ksub H t) := by
  classical
  obtain ⟨w, hwW, hw1⟩ := exists_ne_one_of_ne_bot hW
  have hsplit : IsSplitRankOne H Q t := hS.split
  have hwV : w ∈ Submission.Blueprint.centD H t := Work.ThmF.W_le_centD H t hwW
  have hwcent : w ∈ Subgroup.centralizer (Work.ThmF.Kset H t : Set G) :=
    (Subgroup.mem_inf.mp hwW).2
  have hcomm : ∀ k ∈ Work.ThmF.Kset H t, k * w = w * k := by
    intro k hk
    exact Subgroup.mem_centralizer_iff.mp hwcent k hk
  set X : Subgroup G := Subgroup.zpowers w with hX
  have hXne : X ≠ ⊥ := by
    intro hbot
    have hmem : w ∈ (⊥ : Subgroup G) := by
      rw [← hbot]; exact Subgroup.mem_zpowers w
    exact hw1 (Subgroup.mem_bot.mp hmem)
  have hXV : X ≤ Submission.Blueprint.centD H t := by
    intro x hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← hn]
    exact (Submission.Blueprint.centD H t).zpow_mem hwV n
  have hnorm : ∀ k ∈ Work.ThmF.Kset H t, k ∈ Subgroup.normalizer (X : Set G) := by
    intro k hk
    have hpow : ∀ n : ℤ, k * w ^ n * k⁻¹ = w ^ n := by
      intro n
      have hkw : MulAut.conj k w = w := by
        show k * w * k⁻¹ = w
        rw [hcomm k hk]; group
      have := map_zpow (MulAut.conj k) w n
      simpa only [MulAut.conj_apply, hkw] using this
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, by rw [← hn]; exact (hpow n).symm⟩
    · intro hx
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx
      refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
      have hck : k * w ^ m * k⁻¹ = w ^ m := hpow m
      have hcomm' : k * w ^ m = w ^ m * k := by
        have h := congrArg (· * k) hck
        simpa [mul_assoc] using h
      have h4 : k⁻¹ * w ^ m = w ^ m * k⁻¹ := (show Commute k (w ^ m) from hcomm').inv_left.eq
      have hx_eq : x = k⁻¹ * w ^ m * k := by rw [hm]; group
      rw [hx_eq, h4, mul_assoc, inv_mul_cancel, mul_one]
  obtain ⟨k0, hk0, hk01⟩ := Work.ThmF.L5.exists_mem_Kset_ne_one hS.situation hsplit
  have hP3 := (hC4 G hS.situation H hsplit.stronglyEmbedded t hsplit.invol
    hsplit.not_mem).2.2.2.1
  obtain ⟨-, -, -, hN⟩ := hP3 X hXne hXV ⟨k0, hk0, hk01, hnorm k0 hk0⟩
  obtain ⟨N, hNset, -, hNcyc⟩ := hN
  have hKsetN : Work.ThmF.Kset H t ⊆ (Subgroup.normalizer (X : Set G) : Set G) := hnorm
  have hNset' : (N : Set G) = Work.ThmF.Kset H t := by
    rw [hNset]
    exact Set.Subset.antisymm (Set.inter_subset_left) (fun x hx => ⟨hx, hKsetN hx⟩)
  have hKsub_eq : Work.ThmF.Ksub H t = N := by
    refine le_antisymm ?_ ?_
    · show Subgroup.closure (Work.ThmF.Kset H t) ≤ N
      refine (Subgroup.closure_le N).mpr ?_
      intro x hx
      rw [hNset']
      exact hx
    · intro x hx
      have hx' : x ∈ (N : Set G) := hx
      rw [hNset'] at hx'
      exact Work.ThmF.Kset_le_Ksub H t hx'
  refine ⟨?_, ?_⟩
  · rw [hKsub_eq]; exact hNset'
  · rw [hKsub_eq]; exact hNcyc

-- Superseded (2026): the hole-carrying `chVI_prop` was removed by the hole sweep; its proved
-- replacement is `Work.PSU3.StageA.chVI_prop_of_FT` (in `StageA/chVI_prop_of_FT.lean`), which
-- adds `FeitThompsonProp`.

end Work.PSU3.StageA
