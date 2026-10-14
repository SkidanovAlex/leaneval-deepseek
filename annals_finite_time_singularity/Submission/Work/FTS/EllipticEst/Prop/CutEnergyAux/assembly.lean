import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Prop.CutEnergyAux.realMain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop.CutEnergyAux

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 3200000

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "sg" => Work.FTS.EllipticEst.sEta

/-- The open quadrant. -/
abbrev Q0 : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

/-- The smooth-open class of `u` coming from `AeData`. -/
theorem smoothOpen_u (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    Work.FTS.EllipticEst.SmoothOpen u :=
  Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth

/-- `bslOp α u` is smooth on the open quadrant. -/
theorem smoothOpen_bslOp (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α u) :=
  Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen (smoothOpen_u α u G h)

/-- Joint continuity of `G` on the open quadrant (it agrees there with the smooth `bslOp α u`). -/
theorem continuousOn_G (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    ContinuousOn (Function.uncurry G) Q0 :=
  ((smoothOpen_bslOp α u G h).forall 1).continuousOn |>.congr
    (fun p hp => (h.eq p.1 hp.1 p.2 hp.2.1 hp.2.2).symm)

/-- Joint continuity of `Lzero u · u` on the open quadrant. -/
theorem continuousOn_Lzero_mul (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    ContinuousOn (Function.uncurry (fun z θ => Work.Elliptic.Lzero u z θ * u z θ)) Q0 := by
  have hsu := smoothOpen_u α u G h
  have hGc : ContinuousOn (Function.uncurry (Work.Elliptic.bslOp α u)) Q0 :=
    ((smoothOpen_bslOp α u G h).forall 1).continuousOn
  have hpz2 : ContinuousOn (Function.uncurry (Work.Spaces.pzIter 2 u)) Q0 :=
    ((hsu.pzIter 2).forall 1).continuousOn
  have hpz : ContinuousOn (Function.uncurry (Work.Spaces.pz u)) Q0 :=
    (hsu.pz.forall 1).continuousOn
  have hu : ContinuousOn (Function.uncurry u) Q0 := (hsu.forall 1).continuousOn
  have hLc : ContinuousOn (Function.uncurry (Work.Elliptic.Lzero u)) Q0 := by
    have hfun : Function.uncurry (Work.Elliptic.Lzero u) = fun p : ℝ × ℝ =>
        Function.uncurry (Work.Elliptic.bslOp α u) p
          + (α ^ 2 * p.1 ^ 2) * Function.uncurry (Work.Spaces.pzIter 2 u) p
          + (α * (5 + α) * p.1) * Function.uncurry (Work.Spaces.pz u) p := by
      funext p
      simp only [Function.uncurry, Work.Elliptic.bslOp_apply]
      ring
    rw [hfun]
    exact (hGc.add (((continuousOn_fst.pow 2).const_mul (α ^ 2)).mul hpz2)).add
      (((continuousOn_fst.const_mul (α * (5 + α))).mul hpz))
  exact (hLc.mul hu).congr (fun p _ => rfl)


/-- Fibrewise domination: `∫_θ f² ≤ ∫_θ f²σ` (from `σ ≥ 1` a.e. on `Iθ`). -/
theorem slice_sq_le_sigma {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 0 f) {z : ℝ} (hz : 0 < z)
    (hfaesm : AEStronglyMeasurable (fun θ => (f z θ) ^ 2)
      (MeasureTheory.volume.restrict Iθ)) :
    (∫ θ in Iθ, (f z θ) ^ 2) ≤ ∫ θ in Iθ, (f z θ) ^ 2 * sg θ := by
  have h2 : MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2 * sg θ) Iθ :=
    Work.FTS.EllipticEst.Honest.HkMemSliceSqSigma hmem hz
  have h2' : MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2) Iθ :=
    h2.mono' hfaesm (by
      filter_upwards [ae_Ioo_Iθ] with θ hθ
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      simpa using mul_le_mul_of_nonneg_left (Work.FTS.EllipticEst.Honest.one_le_sEta hθ)
        (sq_nonneg (f z θ)))
  exact integral_mono_ae h2' h2 (by
    filter_upwards [ae_Ioo_Iθ] with θ hθ
    simpa using mul_le_mul_of_nonneg_left (Work.FTS.EllipticEst.Honest.one_le_sEta hθ)
      (sq_nonneg (f z θ)))

end Work.FTS.EllipticEst.Prop.CutEnergyAux
