import Mathlib
import Submission.Work.ThmF.ChV12.L6basic
import Submission.Work.ThmF.ChV12.L6faith
import Submission.Work.ThmF.ChV12.prop1a

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.L6setup` — `Hyp5`-level setup for Ch. V §2 Lemma 6

Ports to `Hyp5` (i.e. `Situation` + `IsSplitRankOne`, without `PSU3Hyp`) the elementary facts
about `K = Kset H t` and `Q0sub H` that `Submission/Work/PSU3/StageA/chVI_prop.lean` and
`Submission/Work/PSU3/StageA/caseC_W_semireg.lean` prove under `PSU3Hyp`:

* `Ksub H t = Kset H t` is a cyclic subgroup as soon as `W = C_V(K) ≠ ⊥`
  (Peterfalvi II Ch. V §1 Prop. 2 in the `W ≠ 1` case);
* `Q0sub H = {x ∈ Q | x² = 1}`;
* `|Q0sub H| = |Inv H| + 1`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open LeanEval.GroupTheory.Defs
open scoped commutatorElement

namespace Work.ThmF.ChV12

open Submission.Blueprint Work.ThmF

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}

/-- A non-trivial subgroup contains a non-identity element. -/
theorem exists_ne_one_of_ne_bot {W : Subgroup G} (h : W ≠ ⊥) : ∃ w ∈ W, w ≠ 1 := by
  by_contra hcon
  push_neg at hcon
  exact h (eq_bot_iff.mpr (fun x hx => Subgroup.mem_bot.mpr (hcon x hx)))

/-- **`K = J(D,t)` is cyclic as soon as `W = C_V(K) ≠ 1`** (Peterfalvi II Ch. V §1 Prop. 2
in the case `W ≠ 1`, which needs no Feit–Thompson input): take `w ∈ W#` and `X = ⟨w⟩`; every
element of `Kset H t` commutes with `w`, so `Kset H t` normalises `X`, and the cyclic subgroup
`N` produced by Ch. II §4 Prop. 3 (d) equals `Kset H t`. -/
theorem Ksub_eq_Kset_and_cyclic_of_W_ne_bot (hS : Situation G) (hsplit : IsSplitRankOne H Q t)
    (hC4 : ChIIFourProp) (hW : W H t ≠ ⊥) :
    (Ksub H t : Set G) = Kset H t ∧ IsCyclic ↥(Ksub H t) := by
  classical
  obtain ⟨w, hwW, hw1⟩ := exists_ne_one_of_ne_bot hW
  have hwV : w ∈ centD H t := W_le_centD H t hwW
  have hwcent : w ∈ Subgroup.centralizer (Kset H t : Set G) :=
    (Subgroup.mem_inf.mp hwW).2
  have hcomm : ∀ k ∈ Kset H t, k * w = w * k := by
    intro k hk
    exact Subgroup.mem_centralizer_iff.mp hwcent k hk
  set X : Subgroup G := Subgroup.zpowers w with hX
  have hXne : X ≠ ⊥ := by
    intro hbot
    have hmem : w ∈ (⊥ : Subgroup G) := by
      rw [← hbot]; exact Subgroup.mem_zpowers w
    exact hw1 (Subgroup.mem_bot.mp hmem)
  have hXV : X ≤ centD H t := by
    intro x hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← hn]
    exact (centD H t).zpow_mem hwV n
  have hnorm : ∀ k ∈ Kset H t, k ∈ Subgroup.normalizer (X : Set G) := by
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
  obtain ⟨k0, hk0, hk01⟩ := Work.ThmF.L5.exists_mem_Kset_ne_one hS hsplit
  have hP3 := (hC4 G hS H hsplit.stronglyEmbedded t hsplit.invol
    hsplit.not_mem).2.2.2.1
  obtain ⟨-, -, -, hN⟩ := hP3 X hXne hXV ⟨k0, hk0, hk01, hnorm k0 hk0⟩
  obtain ⟨N, hNset, -, hNcyc⟩ := hN
  have hKsetN : Kset H t ⊆ (Subgroup.normalizer (X : Set G) : Set G) := hnorm
  have hNset' : (N : Set G) = Kset H t := by
    rw [hNset]
    exact Set.Subset.antisymm (Set.inter_subset_left) (fun x hx => ⟨hx, hKsetN hx⟩)
  have hKsub_eq : Ksub H t = N := by
    refine le_antisymm ?_ ?_
    · show Subgroup.closure (Kset H t) ≤ N
      refine (Subgroup.closure_le N).mpr ?_
      intro x hx
      rw [hNset']
      exact hx
    · intro x hx
      have hx' : x ∈ (N : Set G) := hx
      rw [hNset'] at hx'
      exact Kset_le_Ksub H t hx'
  refine ⟨?_, ?_⟩
  · rw [hKsub_eq]; exact hNset'
  · rw [hKsub_eq]; exact hNcyc

/-- `Q0sub H = {x ∈ Q | x² = 1}`. -/
theorem mem_Q0sub_iff_sq_eq_one (hC4 : ChIIFourProp) (h : Lemma5.Hyp5 H Q t s)
    (hHig : HigmanProp) (hSuz : IsSuzukiTwoGroup ↥Q) :
    ∀ x : ↥Q, (x : G) ∈ Q0sub H ↔ x * x = 1 := by
  intro x
  rw [← Subgroup.mem_subgroupOf, ← center_eq_subgroupOf hC4 h hHig hSuz, ← pow_two]
  exact (hHig ↥Q hSuz).1 x

/-- `|Q0sub H| = |Inv H| + 1`; in particular `(|Q0sub H| - 1) ∣ |Q0sub H| - 1` and
`Inv H` has `q - 1` elements. -/
theorem card_Q0sub_eq (hC4 : ChIIFourProp) (h : Lemma5.Hyp5 H Q t s) :
    Nat.card ↥(Q0sub H) = (involutions (H : Set G)).ncard + 1 := by
  have hcomm := involutions_of_H_commute h.sit hC4 H Q t h.split
  have hQ0 := Q0sub_elementary H hcomm
  have hset : (Q0sub H : Set G) = Q0 H := by
    apply Set.Subset.antisymm
    · intro x hx
      rcases eq_or_ne x 1 with rfl | hx1
      · exact one_mem_Q0 H
      · exact Or.inl (hQ0.2.2.2 x hx hx1)
    · intro x hx
      exact Q0_le_Q0sub H hx
  have hnot : (1 : G) ∉ involutions (H : Set G) := by
    rintro ⟨-, ho⟩; simp at ho
  have h1 : Nat.card ↥(Q0sub H) = (Q0sub H : Set G).ncard := Nat.card_coe_set_eq _
  rw [h1, hset, Q0]
  rw [show (involutions (H : Set G) ∪ {1} : Set G) = insert 1 (involutions (H : Set G)) by
    rw [Set.union_comm]; rfl]
  rw [Set.ncard_insert_of_notMem hnot]

end Work.ThmF.ChV12
