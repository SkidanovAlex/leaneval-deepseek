/-
# Peterfalvi I Ch. I §3 Lemma 2 and §3 Prop. 1, Case 1

The source's Ch. I §3 studies `p`-subgroups maximal among those fixing three points of
`Ω = G ⧸ H` (`H` strongly embedded).  Its Lemma 2 is the "2-rank `≥ 2`" half of §3 Prop. 1:

> Let `X` be a subgroup of odd order of `G` such that `N_G(X)` has `2`-rank `≥ 2`.  Then
> `X ⊆ H(t)` for all `t ∈ Inv(N_G(X))`.

(`H(t)` = the point stabiliser of `Ω` containing the involution `t`; by §1 (10)(a) it is
unique, so it is harmless to state the conclusion for any point stabiliser containing `t`.)
Proof (§1 (6), (9)): `H(t) ∩ N_G(X)` is a strongly embedded subgroup of `N_G(X)`, and
`X ⊆ O_{2'}(N_G(X)) ⊆ H(t) ∩ N_G(X)` because `X` is normal of odd order in `N_G(X)` and
`N_G(X)` has 2-rank `≥ 2`.

Everything used here is already in the workspace:

* `Work.ThreePoints.IsStronglyEmbedded.subgroupOf_inf` — Ch. I §1 (6);
* `Work.ThreePoints.oddCore_le_of_stronglyEmbedded` — Ch. I §1 (9) for `p = 2`;
* `Work.BrauerSuzuki.OddCore.le_of_normal_odd` — a normal odd-order subgroup lies in `O_{2'}`.
-/
import Mathlib
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.oddCore_le_of_stronglyEmbedded
import Submission.Work.BrauerSuzuki.OddCore.le_of_normal_odd

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints

open Submission.Blueprint

variable {G : Type} [Group G]

/-- Intersecting with a subgroup commutes with `subgroupOf`. -/
theorem subgroupOf_inf_eq (X M N : Subgroup G) :
    (X ⊓ M).subgroupOf N = X.subgroupOf N ⊓ M.subgroupOf N := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]

/-- **Peterfalvi I Ch. I §3 Lemma 2.**  An odd-order subgroup `X` of `G` whose normaliser has
`2`-rank `≥ 2` is contained in every point stabiliser of `Ω = G ⧸ H` containing an involution of
`N_G(X)`. -/
theorem le_stabilizer_of_involution_mem_normalizer {H : Subgroup G} [Finite G]
    (hH : IsStronglyEmbedded H) {X : Subgroup G} (hodd : Odd (Nat.card X))
    (h4 : HasFourGroup (Subgroup.normalizer (X : Set G)))
    {t : G} (ht : t ∈ involutions (Subgroup.normalizer (X : Set G) : Set G))
    {ω : G ⧸ H} (hω : t • ω = ω) :
    X ≤ MulAction.stabilizer G ω := by
  classical
  set N : Subgroup G := Subgroup.normalizer (X : Set G) with hN
  set M : Subgroup G := MulAction.stabilizer G ω with hM
  have htN : t ∈ N := ht.1
  have ht2 : orderOf t = 2 := ht.2
  have htM : t ∈ M := by rw [hM, MulAction.mem_stabilizer_iff]; exact hω
  -- `X ≤ N` and `X.subgroupOf N` is normal in `N`
  have hXleN : X ≤ N := fun x hx => by
    rw [hN, Subgroup.mem_normalizer_iff_map_conj_eq]; exact conj_eq_self_of_mem hx
  have hXN : (X.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXleN).mpr le_rfl
  -- `X.subgroupOf N ≤ O_{2'}(N)`
  have hXO : X.subgroupOf N ≤ Submission.Blueprint.oddCore N := by
    refine Work.BrauerSuzuki.OddCore.le_of_normal_odd hXN ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXleN).toEquiv]
    exact hodd
  -- if `N ≤ M` there is nothing to prove
  by_cases hNM : N ≤ M
  · exact le_trans hXleN hNM
  · -- otherwise `N ⊓ M` is a strongly embedded subgroup of `N`
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective ω
    have hMg : M = conj g H := by rw [hM, ← hg, stabilizer_mk]
    have hMstrong : IsStronglyEmbedded M := by
      rw [hMg]; exact conj_stronglyEmbedded hH g
    have hev : Even (Nat.card (N ⊓ M : Subgroup G)) := by
      have hdvd : Nat.card (Subgroup.zpowers t) ∣ Nat.card (N ⊓ M : Subgroup G) :=
        Subgroup.card_dvd_of_le (le_inf (Subgroup.zpowers_le.mpr htN)
          (Subgroup.zpowers_le.mpr htM))
      rw [Nat.card_zpowers, ht2] at hdvd
      exact even_iff_two_dvd.mpr hdvd
    have hproper : (N ⊓ M).subgroupOf N ≠ ⊤ := by
      intro htop
      apply hNM
      intro n hn
      have : (⟨n, hn⟩ : N) ∈ (N ⊓ M).subgroupOf N := by rw [htop]; trivial
      exact (Subgroup.mem_subgroupOf.mp this).2
    have hstrong : IsStronglyEmbedded ((N ⊓ M).subgroupOf N) :=
      IsStronglyEmbedded.subgroupOf_inf hMstrong hproper hev
    have hcore : Submission.Blueprint.oddCore N ≤ (N ⊓ M).subgroupOf N :=
      oddCore_le_of_stronglyEmbedded hstrong h4
    intro x hx
    have : (⟨x, hXleN hx⟩ : N) ∈ (N ⊓ M).subgroupOf N := hcore (hXO hx)
    exact (Subgroup.mem_subgroupOf.mp this).2

end Work.ThreePoints
