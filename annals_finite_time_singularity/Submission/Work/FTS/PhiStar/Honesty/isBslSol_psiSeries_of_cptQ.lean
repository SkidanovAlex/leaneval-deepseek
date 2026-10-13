/-
# `FTS/PhiStar/Honesty/isBslSol_psiSeries_of_cptQ` — the modal series of a compact-source datum
is a `bslOp`-solution

For a source `G` which is `C^∞` on `ℝ²` and compactly supported in the open quadrant
(`SmoothCptQ G`, see `Honesty/CptDefs`), the mode series `psiSeries α G` is a `bslOp`-solution in
the sense of `Work.Elliptic.IsBslSol`:

* the equation `bslOp α (psiSeries α G) = G` on the open quadrant —
  `Honesty.psiSeries_bslOp_of_cptQ` (via the truncated identity `Series.psiTrunc_solves` and the
  pointwise eigen-expansion `Honesty.cmode_expansion_of_cptQ`);
* the two Dirichlet traces `psiSeries α G z 0 = 0`, `psiSeries α G z (π/2) = 0` —
  `Honesty.psiSeries_zero_theta_zero`, `Honesty.psiSeries_zero_theta_pi_half`;
* the decay at `z → ∞` — `Honesty.psiSeries_atTop_zero_of_cptQ`.

This is the `IsBslSol` half of the "honest-for-free" statement
(`ellWeakPos_psiSeries_of_cptQ`); the other half, `TT.EllWeakPos`, additionally needs the two slot
families `hσ`/`hV` of `Honesty.slots_psiSeries_of_cptQ` (and the source's vanishing moment).
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.Honesty.CptDefs
import Submission.Work.FTS.PhiStar.Honesty.psiSeries_smooth_of_cptQ
import Submission.Work.FTS.PhiStar.Honesty.psiSeries_bslOp_of_cptQ
import Submission.Work.FTS.PhiStar.Honesty.psiSeries_atTop_zero_of_cptQ
import Submission.Work.FTS.PhiStar.Honesty.ellWeakPos_seven_of_slots

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

/-- **`psiSeries α G` is a `bslOp`-solution of a compact-source datum.** -/
theorem isBslSol_psiSeries_of_cptQ {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {G : ℝ → ℝ → ℝ}
    (hG : SmoothCptQ G) (hFs : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar G z = 0) :
    Work.Elliptic.IsBslSol α G (Work.FTS.PhiStar.Series.psiSeries α G) :=
  ⟨psiSeries_bslOp_of_cptQ hα hα4 hG hFs,
    fun z => psiSeries_zero_theta_zero α G z,
    fun z => psiSeries_zero_theta_pi_half α G z,
    fun θ hθ => psiSeries_atTop_zero_of_cptQ hα hα4 hG θ hθ⟩

end Work.FTS.PhiStar.Honesty
