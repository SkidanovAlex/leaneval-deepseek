import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Coercivity.slice_ibp_eta
import Submission.Work.Coercivity.wip_L_self
import Submission.Work.FTS_EllLimOK.BoxDataH.BoxUniform
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.H2.HardSlotABound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false


end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.H2.HardSlotBCRBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

/-! ## Elementary `rpow` bookkeeping on `sin (2θ)`

The three pointwise bounds of `HardSlotBCRBounds` are all of the shape
`|sin(2θ)^e · (stuff)| ≤ const · sin(2θ)^{2p-q}`, and the exponent algebra needs the two
identities below (valid on the open interval, where `sin (2θ) > 0`).  At the endpoints of
`Iθ` both sides are handled separately, since `Real.rpow_add` requires a positive base. -/



private lemma rpow_shift2 (s : ℝ) (hs : 0 < s) (q p : ℝ) :
    s ^ (-q) * s ^ (2 * p) = s ^ (2 * p - q) := by
  rw [← Real.rpow_add hs]
  ring_nf


end Work.FTS.H2
end
-- ===== merged: Submission.Work.FTS.H2.IbpHardEta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Continuity of the angular slices at the endpoints of `Iθ` -/

/-- The angular slice `θ ↦ g z θ` of a function smooth on a neighbourhood of the closed
quadrant is continuous at every point of the open interval `(-1, π/2+1)` — in particular at
the endpoints `0` and `π/2` of `Iθ`, which is what the boundary terms of the integration by
parts need. -/
theorem slice_continuousAt (g : ℝ → ℝ → ℝ) (hg : Spaces.SmoothNbhd g) {z : ℝ}
    (hz : 0 < z) {θ : ℝ} (hθ : θ ∈ Set.Ioo (-1) (π / 2 + 1)) :
    ContinuousAt (fun θ' => g z θ') θ := by
  have hmem : (z, θ) ∈ (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1) : Set (ℝ × ℝ)) :=
    ⟨by simp only [Set.mem_Ioi]; linarith, hθ⟩
  have hopen : IsOpen (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1) : Set (ℝ × ℝ)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hcd : ContDiffAt ℝ ⊤ (Function.uncurry g) (z, θ) := hg.contDiffAt (hopen.mem_nhds hmem)
  have hcur : ContinuousAt (fun θ' : ℝ => (z, θ')) θ :=
    continuousAt_const.prodMk continuousAt_id
  have hcomp : ContinuousAt (Function.uncurry g ∘ fun θ' : ℝ => (z, θ')) θ :=
    hcd.continuousAt.comp hcur
  have heq : (Function.uncurry g ∘ fun θ' : ℝ => (z, θ')) = fun θ' : ℝ => g z θ' := rfl
  rw [heq] at hcomp
  exact hcomp



/-! ## Vanishing of the boundary terms -/



/-! ## The two integrability hypotheses -/







end Work.FTS.H2
end
end
