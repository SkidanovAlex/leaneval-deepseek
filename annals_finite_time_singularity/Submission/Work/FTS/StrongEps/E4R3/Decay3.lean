import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.E4R3.Chapters
import Submission.Work.FTS.StrongEps.E4R3.Decay3_leaf

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `StrongEps/E4R3/Decay3.lean` — the chapter `DecayChapter3` (PROVED)

Statement from `cbc/fts_e5swap_e4chapters_B.lean` §2 (corrected chapter), on the in-place
bounded-block `EpsDecay`.  The proof is the sibling `Work.FTS.StrongEps.E4R3.Decay3_leaf`
(module `…E4R3.Decay3_leaf`), whose statement is byte-identical; the explicit majorant is
`Maj z = min 1 (√Ct · C₀α'² · z√z/(1+z)²)`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R3

set_option autoImplicit false

/-- The corrected chapter `DecayChapter3` above a `C₀`-threshold (PROVED). -/
theorem decayChapter3_leaf {Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ C : ℝ, ∀ C₀ : ℝ, C ≤ C₀ → DecayChapter3 Ce Cs C₀ ρ :=
  Work.FTS.StrongEps.E4R3.Decay3_leaf hρ

end Work.FTS.StrongEps.EpsE4Thr.E4R3
