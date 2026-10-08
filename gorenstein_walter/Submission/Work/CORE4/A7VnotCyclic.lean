/-
Area CORE4 of the Gorenstein--Walter project.

# `O₂(Ĥ) ⊄ S₀` in the `A₇` case of Bender 1981, §4

The auxiliary lemmas used in the proof live in `Submission/Work/CORE4/A7VnotCyclicAux.lean`; the
construction of the four-group of `C_M(t)` is `Work.CORE4.A7CMtFourGroupAlt`.

Route.  Assume `O₂(Ĥ) ≤ S₀`.  By the dichotomy of Bender's Theorem 2.6 (first paragraph) and the
fact that a four-group is not a subgroup of the cyclic group `S₀`, this forces `Ĥ = H = C_G(t)`,
so `O₂(Ĥ) = O₂(H) = O₂(H ∩ M)` by §4 (7).  But in the `A₇` case `H ∩ M = C_M(t)` has a normal
four-subgroup `V` (`A7CMtFourGroupAlt`), which therefore lies in `O₂(H ∩ M)`: the `2`-group `O₂(Ĥ)`
contains a Klein four-group, hence is not contained in the cyclic group `S₀`.
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.A7VnotCyclicAux
import Submission.Work.CORE4.A7CMtFourGroupAlt

namespace Work.CORE4

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem A7VnotCyclic (I : Work.GW2.C4Inputs) (G : Type) [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B)
    (h : Work.GW2.Hyp9 G B C) (hA : Work.GW2.IsA7Case C.D) (hf : Work.GW2.A7Facts1 C.D) :
    ¬ (Work.GW2.pCoreIn 2 B.Hhat ≤ B.S0) := by
  intro hle
  have hkeep : Work.GW2.Hyp9 G B C := h
  obtain ⟨hbc, hcase2, hplus, hseven, height⟩ := h
  -- Bender's Theorem 2.6 (first paragraph), the dichotomy
  have hdich := (I.thm26 G I.toolkit.ft hbc B).2.2
  have hnot4 : ¬ Work.GW2.IsFourGroup (Work.GW2.pCoreIn 2 B.Hhat) :=
    fun h4 => not_isFourGroup_of_le_cyclic B.S0_cyclic hle h4
  have hHhatH : B.Hhat = B.H := by
    rcases hdich with ⟨-, hH⟩ | ⟨h4, -, -⟩
    · exact hH
    · exact absurd h4 hnot4
  -- the four-group of `C_M(t) = H ∩ M`
  obtain ⟨V, hVH, hV4, hVnorm⟩ := A7CMtFourGroupAlt I G B C hkeep hA hf
  have hVcard : Nat.card ↥(V.subgroupOf (B.H ⊓ C.D.M)) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVH).toEquiv]
    exact hV4.1
  have hVpg : IsPGroup 2 (V.subgroupOf (B.H ⊓ C.D.M)) :=
    IsPGroup.of_card (n := 2) (by rw [hVcard]; norm_num)
  have hVle : V ≤ Work.GW2.pCoreIn 2 (B.H ⊓ C.D.M) :=
    le_pCoreIn_of_normal_isPGroup 2 (B.H ⊓ C.D.M) hVH hVnorm hVpg
  -- §4 (7): `O₂(H ∩ M) = O₂(H)`, and `Ĥ = H`
  have hO2 : Work.GW2.pCoreIn 2 B.Hhat = Work.GW2.pCoreIn 2 (B.H ⊓ C.D.M) := by
    rw [hHhatH, hseven.1]
  have hVle' : V ≤ Work.GW2.pCoreIn 2 B.Hhat := hO2.symm ▸ hVle
  -- a four-group is not cyclic, but `O₂(Ĥ) ≤ S₀` is cyclic
  exact not_isCyclic_of_isFourGroup hV4
    (isCyclic_of_le_cyclic (isCyclic_of_le_cyclic B.S0_cyclic hle) hVle')

end Work.CORE4
