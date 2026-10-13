/-
# `Work.FTS_RegExport.THL.Defs` — the three O1 definitions, factored out of `THL/Leaves.lean`

`THL/Leaves.lean` is the *leaf plan* of the THL chapter; it carries 16 `sorry` statements plus the
three definitions below.  Every one of the 16 statements is proved in `THL/*` or `THL/L/*`, and
`Leaves.lean` is no longer imported by anything on the entry point's path — its definitions live
here instead, so that `import Submission.Work.FTS_RegExport.RegExportFinal` does not drag the leaf
plan into the environment.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.RegExportIface.Defs
import Submission.Work.FTS.RegExportIface.RXT.Leaves

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.THL

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Regularity (pExp)
open Work.FTS.RegPkgGal (extG)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)
open Work.FTS.RegExportIface

set_option autoImplicit false

/-- The Γ-weighted system (output of `RXT.weighted_system`, input of `RXT.st1_angle`). -/
def WSys (α S K : ℝ) (g : Fam) : Prop :=
  ∀ k : Fin 6, ∀ τ ∈ Icc (0:ℝ) S, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
    |Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
      (Work.FTS.RegExportIface.RXT.idx k).2 (slice g τ) z θ| ≤ K * ω α z θ

/-- The two O1 families. -/
abbrev DzG (α : ℝ) (g : Fam) : ℝ → ℝ → ℝ → ℝ := fun z θ τ =>
  Work.Spaces.Dz (fun z θ => gS α (tauExt g) z θ τ) z θ
abbrev DthG (α : ℝ) (g : Fam) : ℝ → ℝ → ℝ → ℝ := fun z θ τ =>
  Work.Spaces.Dth (fun z θ => gS α (tauExt g) z θ τ) z θ

end Work.FTS_RegExport.THL
