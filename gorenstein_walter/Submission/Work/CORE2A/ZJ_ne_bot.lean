/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.OddOrder.GroupTheory.ThompsonSubgroupAbelian

/-!
# CORE2A: `Z(J(P)) ≠ 1` for a nontrivial `p`-group `P`

For a nontrivial finite `p`-subgroup `P` of a finite group `G`, Thompson's subgroup
`J(P) = ⟨A(P)⟩` (the join of the abelian subgroups of `P` of maximal order, Gorenstein 8.2)
is nontrivial, because `J(P)` contains the centre `Z(P) = C_G(P) ∩ P` of `P`, and a nontrivial
finite `p`-group has a nontrivial centre.  `J(P)` is again a `p`-group, so its own centre
`Z(J(P)) = J(P) ∩ C_G(J(P)) = ZJ P` is nontrivial as well.  This is the statement proved here.

The bridge to the odd-order library: our `Work.GW2.thompsonJ` is *by definition* the
`sSup` of Gorenstein's `A(P) = Subgroup.maxAbelianIn P`, so the maximality lemmas of
`Submission.OddOrder.GroupTheory.ThompsonSubgroupAbelian`
(`centralizer_inf_le_of_mem_maxAbelianIn`) apply verbatim.
-/

open scoped MatrixGroups

namespace Work.CORE2A

open Subgroup

variable {G : Type*} [Group G]

/-! ## 1. `J(P)` and `A(P)`: the bridge to the odd-order library -/

/-- `Work.GW2.thompsonJ P` is the supremum of Gorenstein's `A(P) = Subgroup.maxAbelianIn P`:
the two index sets are the same set-builder by definition. -/
theorem thompsonJ_eq_sSup_maxAbelianIn (P : Subgroup G) :
    Work.GW2.thompsonJ P = sSup (Subgroup.maxAbelianIn P) := rfl

/-- `J(P) ≤ P`. -/
theorem thompsonJ_le (P : Subgroup G) : Work.GW2.thompsonJ P ≤ P := by
  rw [thompsonJ_eq_sSup_maxAbelianIn]
  exact sSup_le fun A hA => hA.1

/-- Every maximal-order abelian subgroup of `P` lies in `J(P)`. -/
theorem le_thompsonJ_of_mem_maxAbelianIn {P A : Subgroup G}
    (hA : A ∈ Subgroup.maxAbelianIn P) : A ≤ Work.GW2.thompsonJ P := by
  rw [thompsonJ_eq_sSup_maxAbelianIn]
  exact le_sSup hA

/-! ## 2. The centre of a nontrivial `p`-group is nontrivial

`Z(P) = C_G(P) ∩ P` is the centre of `P` viewed as a subgroup of `G`; it is nontrivial for a
nontrivial finite `p`-group (`IsPGroup.center_nontrivial`, applied to the group `↥P`). -/

theorem centralizer_inf_ne_bot_of_isPGroup {p : ℕ} [Fact p.Prime] {P : Subgroup G} [Finite G]
    (hP : IsPGroup p P) (hPbot : P ≠ ⊥) :
    Subgroup.centralizer (P : Set G) ⊓ P ≠ ⊥ := by
  intro hbot
  haveI hntP : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr hPbot
  haveI hfinP : Finite ↥P := Finite.of_injective (Subtype.val : ↥P → G) Subtype.val_injective
  haveI hntZ : Nontrivial ↥(Subgroup.center ↥P) := IsPGroup.center_nontrivial hP
  obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center ↥P)
  have hcomm : ∀ g : ↥P, g * (z : ↥P) = (z : ↥P) * g := Subgroup.mem_center_iff.mp z.2
  have hzcent : ((z : ↥P) : G) ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := congrArg (fun w : ↥P => (w : G)) (hcomm ⟨y, hy⟩)
    simpa using h
  have hzP : ((z : ↥P) : G) ∈ P := (z : ↥P).2
  have hmem : ((z : ↥P) : G) ∈ Subgroup.centralizer (P : Set G) ⊓ P := ⟨hzcent, hzP⟩
  rw [hbot] at hmem
  have hone : ((z : ↥P) : G) = 1 := Subgroup.mem_bot.mp hmem
  exact hz1 (Subtype.ext (Subtype.ext (by simpa using hone)))

/-! ## 3. `J(P) ≠ 1` -/

theorem thompsonJ_ne_bot [Finite G] {p : ℕ} [Fact p.Prime] {P : Subgroup G}
    (hP : IsPGroup p P) (hPbot : P ≠ ⊥) : Work.GW2.thompsonJ P ≠ ⊥ := by
  have hZne : Subgroup.centralizer (P : Set G) ⊓ P ≠ ⊥ :=
    centralizer_inf_ne_bot_of_isPGroup hP hPbot
  obtain ⟨A, hA⟩ := Subgroup.maxAbelianIn_nonempty P
  have hle : Subgroup.centralizer (P : Set G) ⊓ P ≤ Work.GW2.thompsonJ P :=
    (Subgroup.centralizer_inf_le_of_mem_maxAbelianIn hA).trans
      (le_thompsonJ_of_mem_maxAbelianIn hA)
  intro hbot
  rw [hbot] at hle
  exact hZne (le_bot_iff.mp hle)

/-! ## 4. `Z(J(P)) ≠ 1` -/

theorem ZJ_ne_bot {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P : Subgroup G} (hP : IsPGroup p P) (hPbot : P ≠ ⊥) : Work.GW2.ZJ P ≠ ⊥ := by
  have hJne : Work.GW2.thompsonJ P ≠ ⊥ := thompsonJ_ne_bot hP hPbot
  have hJP : IsPGroup p (Work.GW2.thompsonJ P) := hP.to_le (thompsonJ_le P)
  have hZne : Subgroup.centralizer ((Work.GW2.thompsonJ P : Subgroup G) : Set G)
      ⊓ Work.GW2.thompsonJ P ≠ ⊥ := centralizer_inf_ne_bot_of_isPGroup hJP hJne
  simpa [Work.GW2.ZJ, inf_comm] using hZne

end Work.CORE2A
