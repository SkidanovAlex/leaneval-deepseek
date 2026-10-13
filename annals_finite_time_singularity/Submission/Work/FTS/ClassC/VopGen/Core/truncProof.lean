import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassC.VopGen.CoreSplit
import Submission.Work.FTS.ClassC.VopGen.Core.truncSetup
import Submission.Work.FTS.ClassC.VopGen.Core.truncBound
import Submission.Work.FTS.ClassC.VopGen.Core.cutoffTendsto
import Submission.Work.FTS.EllipticEst.Mine.Auxiliary.cutoffFamilyMonoSmooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.ClassC.VopGen.Core.truncProof` — the truncation half of the level-`2` core inequality

`TruncStmt` (`VopGen/CoreSplit.lean`) is `SliceAgmonStmt → CoreASlot11Hyp`: from the
a.e.-slicewise angular Agmon inequality for the slice `X = D_z(z²∂_z²Ψ)` one deduces the
level-`2` light-weight core inequality with a universal constant.

The chain: multiply the a.e.-`z` slice inequality by `(χ N z)²(w z)² ≥ 0` and integrate in `z`;
rewrite the resulting pairing as a product integral over `Iz ×ˢ Iθ` (Fubini); integrate by parts
radially with `Prop.zIbpTwoD` for `φ = (χ N)²Xσ`, `ψ = Y` (flux vanishing by compact support
of `χ N`); bound the integrand pointwise by AM–GM against
`(C₀+2)·w²σ·((D_zX)² + X² + Y²)` and drop `(χ N)² ≤ 1`; then pass to the limit `N → ∞` by
dominated convergence (`Core.cutoffTendsto`).

The per-cut-off inequality is `Core.perNBound` (`Core/truncBound.lean`), the pointwise AM–GM
bound `Core.pointwiseBound` (`Core/truncPoint.lean`), and the limit `Core.cutoffTendsto`.
The auxiliary facts (the Clairaut transfer, the Agmon slice inequality in the `D_z∂_θ²` form,
the pairing/majorant integrabilities and the two product rules) are in `Core/truncSetup.lean`.
-/

namespace Work.FTS.ClassC.VopGen.Core

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Work.Spaces (HkSq HkMem HkIntegrand HkIntegrand_nonneg w Iz Iθ Dz DzIter pth pz)

/-- **The truncation half** of the level-`2` core inequality. -/
theorem truncProof : Work.FTS.ClassC.VopGen.TruncStmt := by
  intro hSlice
  obtain ⟨χ, C₀, hC₀pos, hχcd, hχnn, hχle, hχ0, hχsmall, hχbig, hχmono, hχone, hχbd⟩ :=
    Work.FTS.EllipticEst.Mine.cutoffFamilyMono_smooth
  refine ⟨C₀ + 2, by linarith, ?_⟩
  intro α F Ψ hα hα4 h
  have hα1 : α ≤ 1 := by linarith
  have hχm : ∀ N : ℕ, Measurable (χ N) := fun N => (hχcd N).continuous.measurable
  have hsl := agmonSlice hSlice hα hα4 h
  have hmain := perNBound hα hα4 h hsl hC₀pos hχcd hχnn hχle hχsmall hχbig hχbd
  have hg : MeasureTheory.Integrable (fun z => ∫ θ in Iθ,
      (pth (XX Ψ) z θ) ^ 2 * (w z) ^ 2 * sgm α θ) (volume.restrict Iz) :=
    (slotFacts_mixed11 hα1 hα hα4 h).2.1
  have hlim := cutoffTendsto hχm hχnn hχle hχone hg
  have hfin := le_of_tendsto_of_tendsto' hlim tendsto_const_nhds hmain
  simpa only [XX, YY, sgm] using hfin

end

end Work.FTS.ClassC.VopGen.Core
