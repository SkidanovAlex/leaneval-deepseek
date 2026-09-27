import Mathlib
import Submission.Work.Drive.N2.saddleWindowBlock
import Submission.Work.Drive.N2Lead.twistDefs

/-!
# Tier D (`D2d.4`): the explicit curves of the Möbius saddle certificate

The geometry of §1–§2 of `Submission/Work/Drive/N2Lead/NOTES_LEAD_mobiusSaddle.md`:

* `mobiusRho η δ s w = √(σ (s, w) + i w)` — the model arc in `ζ = Z²` coordinates (the right arc of
  the level `Re ζ = s`), read through the principal branch;
* `mobiusAlpha`, `mobiusBeta` — the two model arcs of the *upper* level, untwisted by the slab twists
  `twistY a' (-1)` and `twistX ε (-1)` of `twistDefs.lean` (`α` is the `-ρ` branch, `β` the `+ρ`
  branch; after the untwist `α` lies in `{y > 0}` and `β` in `{y < 0}`, and both have strictly
  increasing `x`).
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

/-- The model right arc of the level `Re ζ = s` in `ζ = Z²` coordinates. -/
noncomputable def mobiusRho (η δ s : ℝ) (w : ℝ) : ℂ :=
  Complex.sqrt ((Work.Drive.N2.saddleSigma η δ (s, w) : ℂ) + (w : ℂ) * Complex.I)

/-- The untwisted left model arc of the upper level. -/
noncomputable def mobiusAlpha (η δ s a' ε : ℝ) (w : ℝ) : E3 :=
  twistX ε (-1) (twistY a' (-1) (Work.Drive.N2.cE3 (-(mobiusRho η δ s w))))

/-- The untwisted right model arc of the upper level. -/
noncomputable def mobiusBeta (η δ s a' ε : ℝ) (w : ℝ) : E3 :=
  twistX ε (-1) (twistY a' (-1) (Work.Drive.N2.cE3 (mobiusRho η δ s w)))

end

end Work.Drive.N2Lead
