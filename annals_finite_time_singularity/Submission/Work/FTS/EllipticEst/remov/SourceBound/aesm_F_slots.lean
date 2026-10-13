import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.remov.SourceBound.sliceAesmSq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.SourceBound

theorem aesm_F_slots {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ z, 0 < z →
      MeasureTheory.AEStronglyMeasurable
        (fun θ => (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) ∧
      MeasureTheory.AEStronglyMeasurable
        (fun θ => (Work.Spaces.Dz F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  -- `Ψ` is `C^∞` on the open quadrant
  have hso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  -- hence so is `bslOp α Ψ`, which agrees with the source `F` on the open quadrant
  have hbsl : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Ψ) :=
    Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hso
  have hcont1 : ContinuousOn (Function.uncurry (Work.Elliptic.bslOp α Ψ))
      Work.FTS.EllipticEst.Q0 := hbsl.continuousOn
  have hcont2 : ContinuousOn (Function.uncurry (Work.Spaces.Dz (Work.Elliptic.bslOp α Ψ)))
      Work.FTS.EllipticEst.Q0 := hbsl.Dz.continuousOn
  -- almost every `θ ∈ Iθ` lies in the open interval, where the equation holds
  have haeθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (π / 2) := ae_mem_Ioo_of_mem_Iθ
  intro z hz
  constructor
  · -- the first slot: replace `F` by `bslOp α Ψ` a.e.
    refine (aesm_slice_sq_mul_sEta hcont1 hz).congr ?_
    filter_upwards [haeθ] with θ hθ
    rw [h.eq z hz θ hθ.1 hθ.2]
  · -- the second slot: `D_z` also only sees the values on the open quadrant
    refine (aesm_slice_sq_mul_sEta hcont2 hz).congr ?_
    filter_upwards [haeθ] with θ hθ
    have hslice : (fun z' : ℝ => F z' θ)
        =ᶠ[𝓝 z] (fun z' : ℝ => Work.Elliptic.bslOp α Ψ z' θ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      exact (h.eq z' hz' θ hθ.1 hθ.2).symm
    have hpz : Work.Spaces.Dz F z θ = Work.Spaces.Dz (Work.Elliptic.bslOp α Ψ) z θ := by
      show z * Work.Spaces.pz F z θ = z * Work.Spaces.pz (Work.Elliptic.bslOp α Ψ) z θ
      rw [show Work.Spaces.pz F z θ = Work.Spaces.pz (Work.Elliptic.bslOp α Ψ) z θ from
        hslice.deriv_eq]
    rw [← hpz]

end Work.FTS.EllipticEst.remov.SourceBound
