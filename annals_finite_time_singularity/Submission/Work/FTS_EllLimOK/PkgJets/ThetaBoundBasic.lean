import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.LocDataExt.Monotone
import Submission.Work.FTS.LocData.HkMem_of_majorant

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Small monotonicity tools for the `ℋ^k`-integrand and the `ℋ^k`-norm

The target `Work.FTS_EllLimOK.PkgJets.thetaBound` needs the level-`0` and level-`4` memberships
`HkMem α 0 g`, `HkMem α 4 g` out of the class field `HkMem α 7 g`, together with the comparison
`HkSq α 0 g ≤ HkSq α 6 g` (so that the `ℋ⁶`-norm `Xn6` of the class can pay for everything).

All three are instances of the *pointwise* monotonicity of the `ℋ^k`-integrand in the order `k`
(every summand is a square and the index sets grow), which is
`Work.FTS.LocDataExt.HkIntegrand_mono`.  `HkMem_mono_le` re-exports the `HkMem`-monotonicity for
the open-quadrant class (`SmoothOpen`, not the analytic `SmoothQuad`), and `HkSq_mono_le` the
corresponding monotonicity of the integral.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.PkgJets

set_option autoImplicit false

/-- The `ℋ`-integrand is monotone in the order `k` (pointwise, no regularity needed). -/
theorem HkIntegrand_le {α : ℝ} {m k : ℕ} (hmk : m ≤ k) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α m f z θ ≤ Work.Spaces.HkIntegrand α k f z θ :=
  Work.FTS.LocDataExt.HkIntegrand_mono hmk f z θ

/-- `HkMem` is monotone in the order, for `SmoothOpen` data (open-quadrant version of
`Work.FTS.LocDataExt.HkMem_mono`, which asks for the analytic `SmoothQuad`). -/
theorem HkMem_mono_le {α : ℝ} {m k : ℕ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmk : m ≤ k) (h : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α m f :=
  Work.FTS.LocData.HkMem_of_majorant α m (hf.continuousOn_HkIntegrand α m) h.1 h.2
    (fun z _ θ _ => HkIntegrand_le hmk f z θ)

/-- `HkSq` is monotone in the order: the level-`k` integrand dominates the level-`m` one, and it
is the integrable one. -/
theorem HkSq_mono_le {α : ℝ} {m k : ℕ} {f : ℝ → ℝ → ℝ} (hmk : m ≤ k)
    (h : Work.Spaces.HkMem α k f) : Work.Spaces.HkSq α m f ≤ Work.Spaces.HkSq α k f := by
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  refine MeasureTheory.integral_mono_of_nonneg ?_ h.2 ?_
  · exact Filter.Eventually.of_forall
      (fun z => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α m f z θ)
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    exact MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α m f z θ)
      (h.1 z hz)
      (Filter.Eventually.of_forall fun θ => HkIntegrand_le hmk f z θ)

end Work.FTS_EllLimOK.PkgJets
