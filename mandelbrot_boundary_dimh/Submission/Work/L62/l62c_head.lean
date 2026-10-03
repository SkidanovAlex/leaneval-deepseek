import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.l62c_basic
import Submission.Work.L62.l62c_end

/-!
# L62 (c) — the head of the chain of Lemma 6.2: definitions

This file holds the definitions used by the head estimates of Lemma 6.2 (see `NOTES_L62f.md`
§1 (F1)–(F5) and `NOTES_L62_head_up.md`):

* `epsDesc` is the `1`-periodic correction `d.E - id` descended to the cylinder.  It is *not*
  `pushdown (d.E - id)` (that is `π (d.E w - w)`, not `d.E w - w`): the descent is taken by
  evaluating at an explicit lift (`ζ ↦ log ζ / (2πi)`, which lies in the `T`-invariant `hd.Bu`
  whenever `ζ ∈ π '' Bu`).

Everything here is a definition; the properties are proved in
`Submission/Work/L62/epsDesc.lean`.
-/

namespace Work.L62

open MandelDim Complex Set Metric Filter Topology
open scoped Topology

noncomputable section

variable {g₀ : ℂ → ℂ} {D : Set ℂ}

/-- The `1`-periodic correction `d.E - id`, descended to the cylinder and extended by `0` at the
upper end.  On `π '' hd.Bu` (and away from `0`) it is `d.E w - w` for any lift `w ∈ hd.Bu` of `ζ`;
the value does not depend on the lift because `d.E - id` is `1`-periodic on the `T`-invariant
`hd.Bu`. -/
noncomputable def epsDesc (d : MandelDim.ParabData g₀ D) (hd : MandelDim.HornData d) (ζ : ℂ) : ℂ :=
  if ζ = 0 then 0
  else d.E (Complex.log ζ / (2 * Real.pi * I)) - Complex.log ζ / (2 * Real.pi * I)

end

end Work.L62
