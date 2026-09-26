/-
# Definitions for the cusp-`0` half tile `{1/2 ≤ Im(S•w) ≤ 2}`

This module exists so that `Submission/Work/Asymptotics/seminormK_cusp0_half.lean` (the target)
and the auxiliary modules about it can share `Tregion`/`Kcomp` without an import cycle.
-/
import Mathlib
import Submission.Work.Kernels.All
import Submission.Work.Asymptotics.DomainD

namespace Work.Asymptotics

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane Topology

noncomputable section

/-- **The cusp-`0` half tile**: `w ∈ 𝒟` with `1/2 ≤ Im(S·w) ≤ 2`. -/
def Tregion : Set ℍ :=
  {w : ℍ | w ∈ DomainD ∧ (1 : ℝ) / 2 ≤ (ModularGroup.S • w).im
    ∧ (ModularGroup.S • w).im ≤ 2}

lemma mem_Tregion {w : ℍ} :
    w ∈ Tregion ↔ w ∈ DomainD ∧ (1 : ℝ) / 2 ≤ (ModularGroup.S • w).im
      ∧ (ModularGroup.S • w).im ≤ 2 := Iff.rfl

lemma Tregion_subset_DomainD : Tregion ⊆ DomainD := fun _ h => h.1

/-- The compact piece of `Tregion`: the tile with the two grazing neighbourhoods removed. -/
def Kcomp : Set ℍ :=
  closure {w : ℍ | w ∈ Tregion ∧ (1 : ℝ) / 10 ≤ ‖(w : ℂ) - ((1 : ℂ) + Complex.I)‖
    ∧ (1 : ℝ) / 10 ≤ ‖(w : ℂ) - ((-1 : ℂ) + Complex.I)‖
    ∧ (1 : ℝ) / 2 + 1 / 10 ≤ ‖(w : ℂ) - (1 / 2 : ℂ)‖
    ∧ (1 : ℝ) / 2 + 1 / 10 ≤ ‖(w : ℂ) + (1 / 2 : ℂ)‖}

end

end Work.Asymptotics
