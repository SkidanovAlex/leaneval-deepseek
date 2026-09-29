import Submission.Work.TMComp.RedC7T.pbj_dioph
import Submission.Work.TMComp.prove_OpBasics
import Submission.Work.TMComp.prove_LEBasics
import Submission.Work.TMComp.prove_Schnol
import Submission.Work.TMComp.C7Aux.Fresh.RTLv3

/-!
# `D_BJ_dioph` from the finite rational tower

This assembles `RedC7T.D_BJ_dioph_of_tower'` with the three elementary components
(`prove_OpBasics`, `prove_LEBasics`, `prove_Schnol`), both proved and axiom-clean in the tree.
The result is the Diophantine case of C7 in the *frozen* `Work.TMContract` vocabulary — exactly
the hypothesis of `RedC7T.mAnalytic_dioph`, hence of component C11 (`P_Reducibility`).

The single remaining input `hS1 : RedC7T.RatTowerLower` is the finite rational tower (S1 of the
lead's C7 design), whose statement coincides verbatim with
`Work.TMC7Core.Scale.rat_tower_lower`, `..._v2` and `Work.TMComp.C7Aux.rat_tower_lower`
(checked by `RedC7T/_shapetest.lean`).
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp.RedC7T

open Work.TMC7Core

/-- **The Diophantine case of C7**, from the rational tower `S1` and the three elementary
components. -/
theorem D_BJ_dioph (hS1 : RatTowerLower) :
    ∀ (α lam b₀ : ℝ), Irrational α → 0 < b₀ → Work.TMContract.DiophBelow α b₀ → lam ≠ 0 →
      ∀ E : ℝ, E ∈ Work.TMContract.amoSpec α lam →
        Work.TMContract.lyap α lam (E : ℂ) = max 0 (Real.log |lam|) :=
  D_BJ_dioph_of_tower'
    (Work.TMC7Core.Bridge.P_OpBasics_transfer Work.TMComp.prove_OpBasics)
    (Work.TMC7Core.Bridge.P_LEBasics_transfer Work.TMComp.prove_LEBasics)
    (Work.TMC7Core.Bridge.P_Schnol_transfer Work.TMComp.prove_Schnol)
    hS1

/-- The finite rational tower `S1`, from its proved instance
`Work.TMComp.C7Aux.TowerV3.rat_tower_lower_v3` (whose statement is verbatim `RatTowerLower`,
checked in `RedC7T/_shapetest.lean`). -/
theorem ratTowerLower : RatTowerLower :=
  fun lam K c C C₀ hLDT hLEB hc1 κ hκ hκ1 b hb =>
    Work.TMComp.C7Aux.TowerV3.rat_tower_lower_v3 lam K c C C₀ hLDT hLEB hc1 κ hκ hκ1 b hb

/-- **The Diophantine case of C7, unconditional.** -/
theorem D_BJ_dioph_uncond :
    ∀ (α lam b₀ : ℝ), Irrational α → 0 < b₀ → Work.TMContract.DiophBelow α b₀ → lam ≠ 0 →
      ∀ E : ℝ, E ∈ Work.TMContract.amoSpec α lam →
        Work.TMContract.lyap α lam (E : ℂ) = max 0 (Real.log |lam|) :=
  D_BJ_dioph ratTowerLower

end Work.TMComp.RedC7T
