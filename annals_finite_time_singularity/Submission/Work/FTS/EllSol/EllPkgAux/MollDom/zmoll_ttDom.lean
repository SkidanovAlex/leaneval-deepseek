import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.KernelDefs
import Submission.Work.FTS.EllSol.PkgK5.K5c.MollDefs
import Submission.Work.FTS.EllSol.EllPkgAux.kernelJensen
import Submission.Work.FTS.EllSol.EllPkgAux.thMollSliceL2
import Submission.Work.FTS.EllSol.EllPkgAux.mollSliceBound
import Submission.Work.FTS.EllSol.EllPkgAux.mollHdom
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.ZmollTTB3
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_continuousOn
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_deriv_bdd
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_deriv2_integrableOn
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_deriv2_weighted_integrableOn
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.localIntegrable_sqrtE2s

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ

open Work.FTS.EllSol.PkgK5.K5c (sKer Qext)

/-- **Pointwise domination of the `∂_θ²`-slot of the log-mollified datum.**

For `G` in the trace class with honest functionals, `δ, ε ∈ (0,1/2]`, `Φ := zmoll G δ ε`:
for a.e. `z > 0` and every `θ ∈ Iθ`,

  `|∂_θ²Φ(z,θ)| ≤ ∫_t sKer δ (log z - t) (∫_s KJ ε θ s |∂_θ²G (e^t) s| ds) dt`.

Intended route.  (i) *θ-identity* (holds for EVERY `w > 0`): starting from the fold
`thMoll G ε w θ = ∫_{Iθ} km ε θ s · G w s ds` (`km ε θ s = sKer ε (θ-s) - sKer ε (θ+s) - sKer ε (θ+s-π)`),
differentiate twice in `θ` under the `s`-integral and integrate by parts twice in `s`:
`∂_θ²(km ε θ s) = ∂_s²(km ε θ s)`, and the boundary terms at `s = 0, π/2` vanish because
`km ε θ 0 = -sKer ε (θ-π) = 0` and `km ε θ (π/2) = -sKer ε (θ+π/2) = 0` (for `ε ≤ 1/2`,
`θ ∈ Iθ`) and because `G w 0 = G w (π/2) = 0` (these are *values* in `TraceClass`).  Hence
`∂_θ²(thMoll G ε) w θ = ∫_{Iθ} km ε θ s ∂_θ²G w s ds`; this needs only
`∫_{Iθ}|∂_θ²G w s| ds < ∞`, which follows from `SliceHonestOpen G` by Cauchy–Schwarz in `θ`
against `σ^{-1} = sin(2·)^{2η} ∈ L¹(Iθ)`.
(ii) *log-mollification commutation*, a.e. in `z` (substitution + two θ-differentiations under the
`t`-integral, the kernel having compact support):
`∂_θ²Φ(z,θ) = ∫_t sKer δ (log z - t) ∂_θ²(thMoll G ε) (e^t) θ dt`.
(iii) glue as in `zmoll_ddDom`, using `|km| ≤ KJ`.

Sources to reuse: `thMoll_abs_le` (the fold machinery and the odd-extension identities
`Qext_of_mem`, `Qext_neg_of_pos`, `Qext_pihalf_odd`), `KJ`, `KJ_nonneg`, `KJ_le`,
`intervalIntegral`-style integration by parts. -/
theorem zmoll_ttDom (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) (δ ε : ℝ)
    (hP : Work.FTS.EllSol.EllPkgAux.Params δ ε) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.pth (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε)) z θ|
          ≤ ∫ t : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t) *
              (∫ s in Work.Spaces.Iθ,
                Work.FTS.EllSol.EllPkgAux.KJ ε θ s *
                |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|) := by
  have hsl : SliceData G :=
    { sm := hT.1
      val0 := hT.2.1
      valpi := hT.2.2.1
      tr0 := hT.2.2.2.1
      trpi := hT.2.2.2.2.1
      cont := fun w hw => slice_continuousOn G hT hw
      deriv_bdd := fun w hw => slice_deriv_bdd G hT hw
      deriv2_int := fun w hw => slice_deriv2_integrableOn G hT hw
      deriv2_weighted := fun w hw => slice_deriv2_weighted_integrableOn G hT hw }
  have hdom : LocallyIntegrable (fun t : ℝ => ∫ s in Iθ, |Hxyc G t s|) volume := by
    obtain ⟨C, hC, hslB⟩ := Work.FTS.EllSol.EllPkgAux.mollSliceBound
    obtain ⟨hslG, hintMGG⟩ := hslB G hT hF
    exact Work.FTS.EllSol.EllPkgAux.mollHdom G hT.1 C hC hslG hintMGG
  have hsqrt : LocallyIntegrable (fun t : ℝ => Real.sqrt (E2s G (Real.exp t))) volume :=
    localIntegrable_sqrtE2s G hT hF
  exact zmoll_ttDom_core G hF hsl hdom hsqrt δ ε hP

end Work.FTS.EllSol.EllPkgAux.MollDom
