import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.TT.aeDzDefs
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.Dispatch.aeJointIntegrableF
import Submission.Work.FTS.EllipticEst.TT.truncAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## The measurability engine

Every one of the six `z`-functions in the statement is the `θ`-marginal of a function which is
*continuous on the open quadrant* `Q0 = (0,∞) × (0,π/2)`, against the product measure
`volume|_{(0,∞)} × volume|_{Iθ}`.  Such a function is a.e. strongly measurable for `nuFts`
(it is continuous, hence Borel measurable, on an open set of full `nuFts`-measure), and Fubini's
measurability theorem for the partial integral then gives the claim for the marginal, on the
first factor `volume|_{(0,∞)}`. -/

/-- A.e. strong measurability of the `θ`-marginal `z ↦ ∫_θ F (z,θ)` for a function continuous
on the open quadrant. -/
theorem aeSliceAesm_sliceIntegral_of_continuousOn {F : ℝ × ℝ → ℝ} (hF : ContinuousOn F Q0) :
    MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ, F (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
  (Work.FTS.EllipticEst.Dispatch.aesm_prod_of_continuousOn_Q0 hF).integral_prod_right'

/-- The squared weight `w(z)²` is continuous on `(0,∞)`. -/
private theorem continuousOn_w_sq :
    ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := by
    funext z; simp only [Work.Spaces.w]
  rw [hfun]
  refine (ContinuousOn.div ?_ ?_ ?_).pow 2
  · fun_prop
  · fun_prop
  · intro z hz; exact pow_ne_zero 2 (ne_of_gt hz)

/-- `φ z = w(z)²` is continuous on `(0,∞)`. -/
private theorem continuousOn_phi :
    ContinuousOn (fun z : ℝ => AeDz.phi z) (Set.Ioi 0) :=
  continuousOn_w_sq

/-- `φ z · z² = w(z)² z²` is continuous on `(0,∞)`. -/
private theorem continuousOn_phi_mul_sq :
    ContinuousOn (fun z : ℝ => AeDz.phi z * z ^ 2) (Set.Ioi 0) :=
  continuousOn_w_sq.mul (continuousOn_id.pow 2)

theorem aeSliceAesm {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    MeasureTheory.AEStronglyMeasurable (fun z => Work.FTS.EllipticEst.TT.AeDz.mass u z) (MeasureTheory.volume.restrict (Set.Ioi 0)) ∧
      MeasureTheory.AEStronglyMeasurable (fun z => Work.FTS.EllipticEst.TT.AeDz.srcMass G u z) (MeasureTheory.volume.restrict (Set.Ioi 0)) ∧
      MeasureTheory.AEStronglyMeasurable (fun z => Work.FTS.EllipticEst.TT.AeDz.lzMass u z) (MeasureTheory.volume.restrict (Set.Ioi 0)) ∧
      MeasureTheory.AEStronglyMeasurable (fun z => Work.FTS.EllipticEst.TT.AeDz.dzMass u z) (MeasureTheory.volume.restrict (Set.Ioi 0)) ∧
      MeasureTheory.AEStronglyMeasurable (fun z => Work.FTS.EllipticEst.TT.AeDz.phi z * z ^ 2 * Work.FTS.EllipticEst.TT.AeDz.dzMass u z) (MeasureTheory.volume.restrict (Set.Ioi 0)) ∧
      MeasureTheory.AEStronglyMeasurable (fun z => Work.FTS.EllipticEst.TT.AeDz.phi z * Work.FTS.EllipticEst.TT.AeDz.mass u z) (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  -- ## the smoothness of the datum and of the source on the open quadrant
  have hU : SmoothOpen u := smoothOpen_of_forall h.smooth
  have hGs : SmoothOpen G :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hU)
      (fun z θ hz hθ hθ' => h.eq z hz θ hθ hθ')
  -- ## continuity on the open quadrant of the four integrands
  have hUc : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) Q0 := hU.continuousOn
  have hGc : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) Q0 := hGs.continuousOn
  have hPzc : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2) Q0 :=
    (hU.pz).continuousOn
  have hLzc : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Lzero u p.1 p.2) Q0 :=
    (smoothOpen_Lzero hU).continuousOn
  have hσc : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2) Q0 :=
    aesm_prod_sEta_snd
  -- ## the four slice masses
  have h1 : MeasureTheory.AEStronglyMeasurable (fun z => AeDz.mass u z)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    aeSliceAesm_sliceIntegral_of_continuousOn (F := fun p : ℝ × ℝ => u p.1 p.2 ^ 2 * sEta p.2)
      ((hUc.pow 2).mul hσc)
  have h2 : MeasureTheory.AEStronglyMeasurable (fun z => AeDz.dzMass u z)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    aeSliceAesm_sliceIntegral_of_continuousOn
      (F := fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2 ^ 2 * sEta p.2)
      ((hPzc.pow 2).mul hσc)
  have h3 : MeasureTheory.AEStronglyMeasurable (fun z => AeDz.lzMass u z)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    have hclean : MeasureTheory.AEStronglyMeasurable
        (fun z => ∫ θ, Work.Elliptic.Lzero u z θ * u z θ * sEta θ
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
      aeSliceAesm_sliceIntegral_of_continuousOn
        (F := fun p : ℝ × ℝ => Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2 * sEta p.2)
        ((hLzc.mul hUc).mul hσc)
    simpa only [AeDz.lzMass, AeDz.sig, AeDz.Lzero1_slice_eq] using hclean
  have h4 : MeasureTheory.AEStronglyMeasurable (fun z => AeDz.srcMass G u z)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    aeSliceAesm_sliceIntegral_of_continuousOn
      (F := fun p : ℝ × ℝ => G p.1 p.2 * u p.1 p.2 * sEta p.2) ((hGc.mul hUc).mul hσc)
  -- ## the two `φ`-weighted ones
  have h5 : MeasureTheory.AEStronglyMeasurable (fun z => AeDz.phi z * z ^ 2 * AeDz.dzMass u z)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    ((continuousOn_phi_mul_sq).aestronglyMeasurable measurableSet_Ioi).mul h2
  have h6 : MeasureTheory.AEStronglyMeasurable (fun z => AeDz.phi z * AeDz.mass u z)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    ((continuousOn_phi).aestronglyMeasurable measurableSet_Ioi).mul h1
  exact ⟨h1, h4, h3, h2, h5, h6⟩

end

end Work.FTS.EllipticEst.TT
