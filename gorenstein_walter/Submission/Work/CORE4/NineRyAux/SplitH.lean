/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4.NineRyAux`)
-/

import Mathlib
import Submission.Work.CORE4.Case2CountSetup

/-!
# `Work.CORE4.NineRyAux.SplitH` — Bender p. 219: `H = C_G(t) = U · S`

Bender 1981, p. 219: for `t` the involution of the cyclic subgroup `S₀` of index two of the
Sylow `2`-subgroup `S`, the centralizer `H = C_G(t)` is the product of its odd core `U = O(H)`
and `S`, i.e. `H = U ⊔ S`; equivalently `H/O(H)` is a `2`-group.

The statement to hand is `SplitH`: it is given an extra subgroup `E ∋ t` and an involution
`r ∈ S ∖ E`, and asks for `H = U ⊔ S`.  Those two hypotheses are exactly what is needed to see
that `S` is **not cyclic**: `t` and `r` are two distinct elements of order two inside `S`, and a
cyclic group has at most one element of order two.  With `BenderCtx.sylow` (`DihOrCycSylow`) this
makes `S` dihedral, `S ≃* DihedralGroup n`; `|S| = 2·|S₀| ≥ 4` (because `t ∈ S₀` has order `2`)
gives `n ≥ 2`.  Finally `I.toolkit.split` (`CentralizerSplitProp`, the FUS-area input of the
project, Bender 1981 p. 219) applies, since `t` is central in `S`.

The two helper lemmas below isolate the two steps that do not use the toolkit at all:

* `not_isCyclic_of_two_involutions` — a subgroup containing two distinct involutions is not
  cyclic (`S` is a `2`-group of order `≥ 4` here);
* `sylow_dihedral_of_distinct_involutions` — in Bender's minimal-counterexample context
  (`BenderCtx`) a Sylow `2`-subgroup containing two distinct involutions is dihedral of order
  `2n` with `n ≥ 2`.

They are stated for arbitrary subgroups/groups so that the sibling files of `NineRyAux` can use
them directly.
-/

namespace Work.CORE4.NineRyAux

/-- **A cyclic group has at most one element of order two.**  Hence a subgroup containing two
distinct involutions `x ≠ y` (of order two) cannot be cyclic. -/
theorem not_isCyclic_of_two_involutions {G : Type} [Group G] [Finite G] {S : Subgroup G}
    {x y : G} (hx : x ∈ S) (hy : y ∈ S) (hx2 : orderOf x = 2) (hy2 : orderOf y = 2)
    (hxy : x ≠ y) : ¬ IsCyclic ↥S := by
  intro hcyc
  have hcycI : IsCyclic ↥S := hcyc
  have h1 : (⟨x, hx⟩ : ↥S) = ⟨y, hy⟩ :=
    Work.GW2.eq_orderOf_eq_two_of_isCyclic (a := (⟨x, hx⟩ : ↥S)) (b := ⟨y, hy⟩)
      (by rw [Subgroup.orderOf_mk]; exact hx2) (by rw [Subgroup.orderOf_mk]; exact hy2)
  exact hxy (congrArg Subtype.val h1)

/-- **`S` is dihedral of order `2n`, `n ≥ 2`, once it contains two distinct involutions.**

`BenderCtx.sylow` (`DihOrCycSylow`) leaves two possibilities for `B.S`; the cyclic one is
excluded by `not_isCyclic_of_two_involutions`, and in the dihedral case `|B.S| = 2n` while
`|B.S| = 2·|B.S₀|` (`B.S0_index`) and `2 ≤ |B.S₀|` (because `B.t ∈ B.S₀` has order two) force
`n ≥ 2`.  The bound `2 ≤ n` is what `CentralizerSplitProp` requires (`DihedralGroup 2` is the
Klein four-group; `DihedralGroup 1` is cyclic). -/
theorem sylow_dihedral_of_distinct_involutions {G : Type} [Group G] [Finite G]
    (hbc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) {x y : G}
    (hx : x ∈ (B.S : Subgroup G)) (hy : y ∈ (B.S : Subgroup G)) (hx2 : orderOf x = 2)
    (hy2 : orderOf y = 2) (hxy : x ≠ y) :
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty ((B.S : Subgroup G) ≃* DihedralGroup n) := by
  have hnc : ¬ IsCyclic ↥(B.S : Subgroup G) :=
    not_isCyclic_of_two_involutions hx hy hx2 hy2 hxy
  obtain ⟨n, ⟨e⟩⟩ : ∃ n : ℕ, Nonempty ((B.S : Subgroup G) ≃* DihedralGroup n) := by
    rcases hbc.sylow B.S with hcyc | ⟨n, hn⟩
    · exact absurd hcyc hnc
    · exact ⟨n, hn⟩
  refine ⟨n, ?_, ⟨e⟩⟩
  have hcard : Nat.card ↥(B.S : Subgroup G) = 2 * n := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hS0 : Nat.card ↥(B.S : Subgroup G) = 2 * Nat.card ↥B.S0 := by
    have h := Subgroup.relIndex_mul_card B.S0 (B.S : Subgroup G)
    rw [B.S0_index, inf_eq_left.mpr B.S0_le] at h
    exact h.symm
  have hne0 : Nonempty ↥B.S0 := ⟨⟨1, B.S0.one_mem⟩⟩
  have hge : 2 ≤ Nat.card ↥B.S0 := by
    have hdvd : 2 ∣ Nat.card ↥B.S0 := by
      rw [← B.t_order]
      exact Subgroup.orderOf_dvd_natCard B.S0 B.t_mem
    exact Nat.le_of_dvd Nat.card_pos hdvd
  omega

/-- **Bender p. 219**: `H = C_G(t) = U · S`.

The hypotheses `B.t ∈ E` and `r ∈ S ∖ E` (with `orderOf r = 2`) make `t ≠ r` two distinct
involutions of `S`, so `S` is dihedral `≃* DihedralGroup n` with `n ≥ 2`; `t` is central in `S`
(`BenderSetup.t_central`), and the toolkit's centralizer-splitting theorem `I.toolkit.split`
(`CentralizerSplitProp`) yields `O(C(t)) ⊔ S = C(t)`. -/
theorem SplitH (I : Work.GW2.C4Inputs) {G : Type} [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) (hbc : Work.GW2.BenderCtx G) (E : Subgroup G)
    (htE : B.t ∈ E) (r : G) (hrS : r ∈ (B.S : Subgroup G)) (hr2 : orderOf r = 2)
    (hrE : r ∉ E) : B.H = B.U ⊔ (B.S : Subgroup G) := by
  have htS : B.t ∈ (B.S : Subgroup G) := Work.GW2.BenderSetup.t_mem_S B
  have htr : B.t ≠ r := fun h => hrE (h ▸ htE)
  obtain ⟨n, hn2, ⟨e⟩⟩ :=
    sylow_dihedral_of_distinct_involutions hbc B htS hrS B.t_order hr2 htr
  exact (I.toolkit.split G B.S n hn2 ⟨e⟩ B.t htS B.t_order
    (Work.GW2.BenderSetup.t_central B)).symm

end Work.CORE4.NineRyAux
