import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Coercivity.HkSq_mono

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

/-! ## `HkMem` descends in the order, on the open-quadrant regularity class

`Work.Spaces.HkMem α k f` says that the `ℋ^k`-integrand of `f` has honest iterated
integrals over `Iz × Iθ` (`dz dθ`).  Since `HkIntegrand α (k+1) f` is obtained from
`HkIntegrand α k f` by adding the squares of the finitely many new weighted derivatives,
the integrand is pointwise monotone in the index (`Work.Spaces.HkIntegrand_mono`, iterated
to `k ≤ l` below).  Hence honesty at order `l` implies honesty at every lower order `k ≤ l`,
provided the smaller integrand is a.e. strongly measurable — and that is available as soon
as `f` is `C^∞` on the open quadrant `(0,∞) × (0,π/2)`, because the integrand is then
continuous there (`Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand`, the open
quadrant being all of `Iz × Iθ` up to the null boundary segments).

The whole descent is an instance of the general domination lemma
`Work.FTS.LocData.HkMem_of_majorant`, with the majorant `M = HkIntegrand α l f` supplied by
the hypothesis `hm : HkMem α l f`.  This is the weak-class replacement for
`Work.FTS.CoercivityStep.Norm.HkMem_descend`, which requires the (much stronger)
`SmoothNbhd` hypothesis. -/

/-- The `ℋ^k`-integrand is monotone in the exponent: for `k ≤ l` every summand of
`HkIntegrand α k f` occurs in `HkIntegrand α l f` with the same value, and all summands are
squares, hence nonnegative.  This is `Work.Spaces.HkIntegrand_mono` iterated. -/
private theorem HkIntegrand_mono_le (α : ℝ) {k l : ℕ} (hkl : k ≤ l) (f : ℝ → ℝ → ℝ)
    (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k f z θ ≤ Work.Spaces.HkIntegrand α l f z θ :=
  Nat.le_induction (le_refl _)
    (fun n _ ih => le_trans ih (Work.Spaces.HkIntegrand_mono α n f z θ)) l hkl

/-- **`HkMem` descends in the order, on the open-quadrant regularity class.**  If `f` is `C^∞`
on the open quadrant `(0,∞) × (0,π/2)` and its `ℋ^l`-integrand is honest, then its
`ℋ^k`-integrand is honest for every `k ≤ l`: the integrand is monotone in the index
(`Work.Spaces.HkIntegrand_mono`) and dominated by the honest one, while smoothness on the open
quadrant (whose complement in `Iz × Iθ` is null) supplies a.e. strong measurability.  This is the
weak-class replacement for `Work.FTS.CoercivityStep.Norm.HkMem_descend`, which requires
`SmoothNbhd`. -/
theorem HkMem_descend_open {α : ℝ} {k l : ℕ} {f : ℝ → ℝ → ℝ} (hkl : k ≤ l)
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hm : Work.Spaces.HkMem α l f) : Work.Spaces.HkMem α k f :=
  Work.FTS.LocData.HkMem_of_majorant α k
    ((Work.FTS.EllipticEst.smoothOpen_of_forall hf).continuousOn_HkIntegrand α k)
    hm.1 hm.2
    (fun z _ θ _ => HkIntegrand_mono_le α hkl f z θ)

end Work.FTS.EllipticEst.TT
