/-
# `Work.FQCInputs.principal_muQC_zero` — the deformation is the identity at `t = 0`

`θ_0 = principal (muQC d fl P 0) = id`: the base point of the continuation argument of the lead's
design (`Submission/Work/NOTES_LEAD_mandelbar_simple.md` §3.2/§3.7).  `muQC d fl P 0 = 0`
(`Work.FQCInputs.muQC_zero`) and M6 (`Work.MRMT.Found.principal_tendsto`) with the constant sequence
`μs = 0` gives `principal 0 = id`.
-/
import Mathlib
import Submission.Work.FQCInputs.muQC_zero
import Submission.Work.MRMT.Found.M

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology ComplexConjugate
open MeasureTheory Filter Set Function
open Classical

set_option linter.unusedVariables false

noncomputable section

namespace Work.FQCInputs

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.EL (RootParabolic F K)

/-- The zero coefficient is admissible. -/
theorem admissible_zero : Work.MRMT.Found.Admissible (0 : ℂ → ℂ) :=
  ⟨aestronglyMeasurable_zero, ⟨0, by norm_num, by filter_upwards with z; simp⟩,
    by rw [Function.support_zero]; exact Bornology.isBounded_empty⟩

/-- **M6 at the zero coefficient**: `principal 0 = id`. -/
theorem principal_zero : (Work.MRMT.Found.principal (0 : ℂ → ℂ) : ℂ → ℂ) = id := by
  have h := Work.MRMT.Found.principal_tendsto (μs := fun _ : ℕ => (0 : ℂ → ℂ))
    (fun _ => admissible_zero) (R := 0) (k := 0) (by norm_num)
    (fun _ => by rw [Function.support_zero]; exact Set.empty_subset _)
    (fun _ => by filter_upwards with z; simp)
    (by simpa using tendsto_const_nhds)
  funext z
  have hz := (h.tendstoLocallyUniformlyOn (s := Set.univ)).tendsto_at (Set.mem_univ z)
  exact tendsto_nhds_unique tendsto_const_nhds hz

/-- **The deformation is the identity at `t = 0`.** -/
theorem principal_muQC_zero {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁) (P : Set ℂ) :
    (Work.MRMT.Found.principal (Work.FQC.muQC d fl P 0) : ℂ → ℂ) = id := by
  rw [muQC_zero d fl P]
  exact principal_zero

end Work.FQCInputs

end
