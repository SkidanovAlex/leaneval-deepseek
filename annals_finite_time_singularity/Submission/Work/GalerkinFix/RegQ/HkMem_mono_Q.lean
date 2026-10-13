import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.LocData.Defs
import Submission.Work.Spaces.Linf_H2
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.Coercivity.HkSq_mono

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-
# `HkMem` is monotone in the order `k`, in the *interior* smoothness class

`Work.Spaces.HkMem α k f` says that the `ℋ^k`-integrand of `f` has honest iterated integrals
over the domain `Iz ×ˢ Iθ = [0,∞) × [0,π/2]` with the measure `dz dθ`:

* every angular slice `θ ↦ HkIntegrand α k f z θ` is integrable on `Iθ` (for `z ∈ Iz`), and
* `z ↦ ∫_θ HkIntegrand α k f z θ` is integrable on `Iz`.

`HkIntegrand α (k+1) f` is obtained from `HkIntegrand α k f` by *adding* finitely many further
summands, each of them a square of a weighted derivative of `f`
(`Work.Spaces.HkIntegrand_mono`).  Hence the `(k+1)`-integrand *dominates* the `k`-integrand
pointwise and admits as its own `θ`-slices and slice-integral exactly the two integrability
certificates contained in `Work.Spaces.HkMem α (k+1) f`.

The only extra input needed is the a.e. strong measurability of the *smaller* integrand (a
function dominated by an integrable function need not be integrable without it).  This is where
smoothness enters: for `f` of class `Work.FTS.LocData.SmoothQuad` (genuine `C^∞` on the open
quadrant `z > -1`, `0 < θ < π/2` — the class preserved by the cut-off of the route, *not* the
analytic class `Work.Spaces.SmoothNbhd`), the integrand is `ContinuousOn` on the open quadrant
(`Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad`); the closed quadrant differs from the
open one by null sets, and on the single slice `z = 0` the integrand vanishes identically since
the radial weight `w 0 = 0`.  So the domination machinery
`Work.FTS.LocData.HkMem_of_majorant` applies verbatim, with the majorant `M` being the
`(k+1)`-integrand itself.

This is the `SmoothQuad` replacement of `Work.Coercivity.HkMem_mono`, whose measurability input
is stated for the (strictly stronger, cut-off-incompatible) analytic class `Spaces.SmoothNbhd`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.GalerkinFix.RegQ

/-- **`HkMem` is monotone in the order, in the interior class.**  If `f` is `C^∞` on the open
quadrant and its `ℋ^{k+1}`-integrand has honest iterated integrals, then so does its
`ℋ^k`-integrand. -/
theorem HkMem_mono_Q {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.LocData.SmoothQuad f) (h : Work.Spaces.HkMem α (k + 1) f) :
    Work.Spaces.HkMem α k f :=
  Work.FTS.LocData.HkMem_of_majorant α k
    (Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α k f hf)
    h.1 h.2
    (fun z _ θ _ => Work.Spaces.HkIntegrand_mono α k f z θ)

end Work.GalerkinFix.RegQ
