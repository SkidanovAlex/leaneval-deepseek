/-
Copyright: subproject `Submission/Work/FBif/` of `mandelbar_not_path_connected`.

# `Work.FBif` — the local estimate, discharged (FBif, part 2b)

`Submission/Work/FBif/hsLocal_bound.lean` proves the real-analysis estimate
`Work.FBif.hsLocal_bound` (Hubbard–Schleicher's case analysis).  This module repackages it as
`Work.FBif.LocalBound` and derives `HSEstimate` from the normalised expansion.
-/
import Submission.Work.FBif.Expansion
import Submission.Work.FBif.hsLocal_bound

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Function
open scoped Topology

noncomputable section

namespace Work.FBif

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- `LocalBound A` holds for every `A` with positive real part: this is the real-analysis
estimate `Work.FBif.hsLocal_bound`. -/
theorem localBound_of_pos {A : ℂ} (hA : 0 < A.re) : LocalBound A := hsLocal_bound hA

/-- **HS's estimate from the normalised expansion**, with the real-analysis input discharged. -/
theorem HSEstimate.of_expansion' {c z₁ : ℂ} {q : ℂ → ℂ} {A : ℂ} (hA : 0 < A.re)
    (h : HSExpansion c z₁ q A) : HSEstimate c z₁ q :=
  HSEstimate.of_expansion (localBound_of_pos hA) h

end Work.FBif

end
