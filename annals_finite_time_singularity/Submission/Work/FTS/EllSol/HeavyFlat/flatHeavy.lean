import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.HeavyFlat.Defs
import Submission.Work.FTS.EllSol.Shift2Flat.mixedSlotFiniteness

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.HeavyFlat

/-- **The flat shifted heavy-weight mixed-slot finiteness** (`b`-general form).  For every shift
`b : ℝ` and every `u` of class `C²` on the open strip `ℝ × (0,π/2)` whose end-point *values*
vanish, if the three `σ_η`-weighted diagonal slots — `((∂_t-b)u)²σ_η`, `((∂_t-b)²u)²σ_η`,
`(∂_θ²u)²σ_η`, `σ_η = sin(2θ)^{-η}` — are integrable on the strip, then the `σ_η`-weighted
`(1,1)`-slot `(∂_θ(∂_t-b)u)²σ_η` has finite `∫⁻` on the strip.  This is the workspace's recorded
node `Work.FTS.EllSol.Shift2Flat.mixedSlotFiniteness` (its file `Shift2Flat/mixedSlotFiniteness.lean`
still carries a `sorry`; `Shift2Flat/mixedSlotLtTop.lean` too, so there is nothing to cite).  Its
route is documented, hand-verified and ingredient-complete in
`Submission/Work/FTS/EllSol/Shift2Flat/NOTES_mixedSlot_route.md`: truncate `u` in `t` by
`Work.FTS.EllSol.Trunc.chi`; apply the *proved* complex angular Agmon
`Work.FTS.EllSol.Trunc.curlAgmon` to the `θ`-slices of the `t`-Fourier transform at each
frequency; identify the four integrated slots with `Work.FTS.EllSol.ShiftFT.plancherelShift`
(and its second-order companion) so that the frequency multiplier `μ(ξ) = (2πξ)²+b²` reproduces
the shifted slots; Cauchy–Schwarz in `ξ`; then Fatou in the truncation scale, the truncation
errors being paid by `(M1)–(M3)` of that note (`u` and `∂_θu` are bounded by
`∫_0^{π/2}|∂_θ²u|`, the latter being the `hQ`-slot). -/
theorem flatHeavy : Work.FTS.EllSol.HeavyFlat.FlatHeavy := by
  -- `FlatHeavy` is the `Shift2Flat.mixedSlotFiniteness` statement with `sEta` written as `sigE`
  -- (`sigE` and `sEta` are the same function by definition).
  intro b u hu h0 hπ hV hZ hQ
  exact Work.FTS.EllSol.Shift2Flat.mixedSlotFiniteness (b := b) u hu h0 hπ hV hZ hQ

end Work.FTS.EllSol.HeavyFlat
