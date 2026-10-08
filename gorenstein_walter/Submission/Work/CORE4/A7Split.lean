/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# `Work.CORE4.A7Split`: `H = C_G(t) = U · S`

Bender 1981, p. 219: for `t` the central involution of the Sylow `2`-subgroup `S`, the
centralizer `H = C_G(t)` is the product of its odd core `U = O(H)` and `S`, i.e.
`H = U ⊔ S`.  Equivalently `H/U ≅ S/(S ⊓ U)` is a `2`-group: `H` has a normal `2`-complement.

The mathematical route used here (all inputs are fields of `C4Inputs`, so the lemma adds no
hypothesis beyond the ones already in the statement):

* the `A₇` hypothesis `A7Facts2` gives that `V := O₂(Ĥ) = O₂(H ⊓ M)` is a four-group
  (`IsFourGroup`), and Theorem 2.6 (`I.thm26`) gives `O₂(Ĥ) = S ⊓ C_G(U) ≤ S`;
* hence `S` contains a four-group, so `S` is **not** cyclic (a cyclic `2`-group has a unique
  involution, a four-group has three);
* by `BenderCtx.sylow` (`DihOrCycSylow`) it is therefore dihedral: `S ≃* DihedralGroup n` with
  `2n = |S| = 8` (`A7Facts2`), so `n = 4 ≥ 2`;
* `t` is central in `S` (the unique involution of the cyclic `S₀`, which is normal of index `2`
  in `S`), so the toolkit's centralizer-splitting theorem `I.toolkit.split`
  (`CentralizerSplitProp`, Bender 1981 p. 219) applies:
  `O(H) ⊔ S = C_G(t)`.
-/
import Mathlib
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.CountSetup
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.A7VnotCyclicAux

namespace Work.CORE4

open Work.GW2 Subgroup

/-- `O₂(Ĥ) ≤ S` (`I.thm26`: `O₂(Ĥ) = S ⊓ C_G(U)`). -/
theorem A7Split_pCoreIn_Hhat_le_S (I : Work.GW2.C4Inputs) {G : Type} [Group G] [Finite G]
    {B : Work.GW2.BenderSetup G} (hbc : Work.GW2.BenderCtx G) :
    Work.GW2.pCoreIn 2 B.Hhat ≤ (B.S : Subgroup G) := by
  have h26 := I.thm26 G I.toolkit.ft hbc B
  rw [← h26.2.1]
  exact inf_le_left

/-- `S` is dihedral, `S ≃* DihedralGroup n` with `n ≥ 2`, in the `A₇` case of §4.

`S` contains the four-group `O₂(Ĥ) = S ⊓ C_G(U)` (`I.thm26`, `A7Facts2`), hence is not cyclic;
`BenderCtx.sylow` then makes it dihedral, and `|S| = 8` (`A7Facts2`) gives `n = 4`. -/
theorem A7Split_sylow_dihedral (I : Work.GW2.C4Inputs) {G : Type} [Group G] [Finite G]
    {B : Work.GW2.BenderSetup G} {C : Work.GW2.Case2Ctx6 B}
    (hbc : Work.GW2.BenderCtx G) (h2 : Work.GW2.A7Facts2 B C.D) :
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty ((B.S : Subgroup G) ≃* DihedralGroup n) := by
  -- `O₂(Ĥ) = O₂(H ⊓ M)` is a four-group (`A7Facts2`) and lies in `S` (`I.thm26`)
  have h4 : IsFourGroup (Work.GW2.pCoreIn 2 B.Hhat) := by
    rw [h2.2.1]
    exact h2.1
  have h4leS : Work.GW2.pCoreIn 2 B.Hhat ≤ (B.S : Subgroup G) :=
    A7Split_pCoreIn_Hhat_le_S I hbc
  -- a four-group is not cyclic, so `S` is not cyclic
  have hnc : ¬ IsCyclic ↥(B.S : Subgroup G) := fun hcyc =>
    not_isCyclic_of_isFourGroup h4 (isCyclic_of_le_cyclic hcyc h4leS)
  -- `DihOrCycSylow` then makes `S` dihedral of order `2n`; `|S| = 8` forces `n = 4`
  have hcard : Nat.card ↥(B.S : Subgroup G) = 8 := h2.2.2.2.1
  rcases hbc.sylow B.S with hcyc | ⟨n, hn⟩
  · exact absurd hcyc hnc
  · obtain ⟨e⟩ := hn
    refine ⟨n, ?_, ⟨e⟩⟩
    have hc : Nat.card ↥(B.S : Subgroup G) = 2 * n := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    omega

theorem A7Split (I : Work.GW2.C4Inputs) {G : Type} [Group G] [Finite G]
    {B : Work.GW2.BenderSetup G} {C : Work.GW2.Case2Ctx6 B}
    (hbc : Work.GW2.BenderCtx G) (h2 : Work.GW2.A7Facts2 B C.D) :
    B.H = B.U ⊔ (B.S : Subgroup G) := by
  obtain ⟨n, hn2, hdih⟩ := A7Split_sylow_dihedral I hbc h2
  exact (I.toolkit.split G B.S n hn2 hdih B.t (Work.GW2.BenderSetup.t_mem_S B) B.t_order
    (Work.GW2.BenderSetup.t_central B)).symm

end Work.CORE4
