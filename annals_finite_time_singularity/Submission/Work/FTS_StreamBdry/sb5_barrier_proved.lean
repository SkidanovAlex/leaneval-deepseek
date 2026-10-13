import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs
import Submission.Work.FTS_StreamBdry.SB25.phiB_barrier

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `sb5_barrier_proved` — the frozen SB5 sub-leaf `StreamBdryIface.sb5_barrier`

The FIX-SB5 barrier exists: the explicit `phiB θ = 1/(4 sin θ) + 1/(16(1-sin θ)) + 3/(16(1+sin θ))
- (3/16)log(1-sin θ) - (9/16)log(1+sin θ) + 1` is `C²` on `(0,π/2)`, nonnegative there, blows up at
both ends, and satisfies `𝓐 phiB = -15/4` exactly, where `𝓐φ = -φ'' - (4cot 2θ - tan θ)φ'`.
Hence `SB5Barrier` holds with `Cφ = 15/4` (see `SB25/phiB_barrier`).
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_StreamBdry

open Work.FTS.StreamBdryIface (SB5Barrier)

set_option autoImplicit false

/-- **SB5 sub-leaf, proved**: the barrier of FIX-SB5 exists (frozen type `SB5Barrier`). -/
theorem sb5_barrier_proved : SB5Barrier := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := Work.FTS_StreamBdry.SB25.phiB_barrier
  exact ⟨Work.FTS_StreamBdry.SB25.phiB, 15 / 4, h1, h2, h3, h4,
    fun θ hθ => by rw [h5 θ hθ]⟩

end Work.FTS_StreamBdry
