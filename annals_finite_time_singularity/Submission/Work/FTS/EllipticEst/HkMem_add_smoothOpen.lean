import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.EllipticEst.HkIntegrand_add_le_open
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.Galerkin.Hilbert.HkMem_const_mul
import Submission.Work.Coercivity.E2Mixed.E2model_mixed_split

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

/-- **`ℋ^k` is closed under addition for data smooth on the open quadrant.**

If `f` and `g` are `C^∞` on the open quadrant `(0,∞) × (0,π/2)` (`SmoothOpen`) and both lie in
the weighted space `ℋ^k` (`Work.Spaces.HkMem`), then so does `f + g`.

Proof.  `f + g` is again `C^∞` on the open quadrant (`smoothOpen_add`), so its `ℋ^k`-integrand is
continuous there (`SmoothOpen.continuousOn_HkIntegrand`) — which is the only regularity needed
for the two iterated integrals.  The weighted derivatives are additive on the open quadrant
(`SmoothOpen.DzIter_add`, `SmoothOpen.mixed_add`), so termwise `(a+b)² ≤ 2a² + 2b²` gives the
pointwise domination

`HkIntegrand α k (f+g) z θ ≤ 2 · HkIntegrand α k f z θ + 2 · HkIntegrand α k g z θ`

on `Iz ×ˢ Iθ` (`HkIntegrand_add_le_open`; the two boundary lines are trivial).  Since the
integrand is a sum of squares, it is nonnegative, so the domination of the values is a
domination of the absolutely-integrable majorant, and `HkMem α k f`, `HkMem α k g` supply the
integrability of its two pieces.  This is exactly the shape of
`Work.FTS.LocData.HkMem_of_majorant`, which assembles the two `HkMem` clauses (on each angular
slice and after integration in `z`) from the continuity and the pointwise domination. -/
theorem HkMem_add_smoothOpen (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (fun z θ => f z θ + g z θ) := by
  have hsum : SmoothOpen (fun z θ => f z θ + g z θ) := smoothOpen_add hf hg
  refine Work.FTS.LocData.HkMem_of_majorant α k
    (f := fun z θ => f z θ + g z θ)
    (M := fun z θ => 2 * Work.Spaces.HkIntegrand α k f z θ
      + 2 * Work.Spaces.HkIntegrand α k g z θ)
    (hsum.continuousOn_HkIntegrand α k) ?_ ?_ ?_
  · -- the `θ`-slices of the majorant are integrable: those of `f` and of `g` are
    intro z hz
    exact ((hmf.1 z hz).const_mul 2).add ((hmg.1 z hz).const_mul 2)
  · -- the `z`-integral of the `θ`-slices: split it into the two known integrals
    have hknown : MeasureTheory.IntegrableOn
        (fun z => 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ))
        Work.Spaces.Iz :=
      (hmf.2.const_mul 2).add (hmg.2.const_mul 2)
    refine hknown.congr_fun ?_ measurableSet_Ici
    intro z hz
    simp only []
    rw [integral_add ((hmf.1 z hz).const_mul 2) ((hmg.1 z hz).const_mul 2),
      integral_const_mul, integral_const_mul]
  · -- the pointwise domination on the closed quadrant
    intro z hz θ hθ
    exact HkIntegrand_add_le_open α k hf hg hz hθ

end Work.FTS.EllipticEst
