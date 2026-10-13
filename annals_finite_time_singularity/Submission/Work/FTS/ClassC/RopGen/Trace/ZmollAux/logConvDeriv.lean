import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC.RopGen.Trace.ZmollAux

open scoped Real Topology
open MeasureTheory

set_option autoImplicit false

/-- `sKer δ` has compact support (contained in `[-δ, δ]`) when `δ > 0`. -/
private theorem sKer_hasCompactSupport {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (Work.FTS.EllSol.PkgK5.K5c.sKer δ) := by
  refine HasCompactSupport.intro (K := Set.Icc (-δ) δ) isCompact_Icc ?_
  intro t ht
  refine Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ ?_
  rw [Set.mem_Icc, not_and_or] at ht
  rcases ht with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-- The logarithmic convolution `s ↦ ∫ t, sKer δ (s - t) * F t` is differentiable at every
point with derivative `∫ t, sKerd δ (s - t) * F t`, the derivative having been moved onto the
(compactly supported, smooth) kernel.  This is
`HasCompactSupport.hasDerivAt_convolution_right` for the convolution
`F ⋆[mul, volume] sKer δ`, rewritten as the iterated integral appearing in `zmoll`. -/
private theorem hasDerivAt_logConv (F : ℝ → ℝ)
    (hF : MeasureTheory.LocallyIntegrable F MeasureTheory.volume) {δ : ℝ} (hδ : 0 < δ) :
    ∀ s : ℝ, HasDerivAt (fun x : ℝ => ∫ t : ℝ,
        Work.FTS.EllSol.PkgK5.K5c.sKer δ (x - t) * F t)
      (∫ t : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ (s - t) * F t) s := by
  have hcs : HasCompactSupport (Work.FTS.EllSol.PkgK5.K5c.sKer δ) :=
    sKer_hasCompactSupport hδ
  have hcd : ContDiff ℝ 1 (Work.FTS.EllSol.PkgK5.K5c.sKer δ) :=
    Work.FTS.EllSol.EllPkgAux.contDiff_sKer δ (n := 1)
  -- the convolution is the iterated integral
  have hconv : ∀ (k : ℝ → ℝ) (x : ℝ),
      MeasureTheory.convolution F k (ContinuousLinearMap.mul ℝ ℝ) MeasureTheory.volume x
        = ∫ t : ℝ, k (x - t) * F t := by
    intro k x
    rw [MeasureTheory.convolution_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)
  intro s
  have hbase : HasDerivAt
      (MeasureTheory.convolution F (fun u : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ u)
        (ContinuousLinearMap.mul ℝ ℝ) MeasureTheory.volume)
      (MeasureTheory.convolution F (fun u : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd δ u)
        (ContinuousLinearMap.mul ℝ ℝ) MeasureTheory.volume s) s := by
    have h := hcs.hasDerivAt_convolution_right (L := ContinuousLinearMap.mul ℝ ℝ)
      (μ := MeasureTheory.volume) hF hcd s
    have hfun : (fun u : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd δ u)
        = deriv (fun u : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ u) := by
      funext u
      rw [Work.FTS.EllSol.EllPkgAux.sKerd]
    rw [hfun]
    exact h
  simpa only [← hconv] using hbase

theorem logConvDeriv (F : ℝ → ℝ)
    (hF : MeasureTheory.LocallyIntegrable F MeasureTheory.volume) {δ : ℝ} (hδ0 : 0 < δ) :
    ∀ z : ℝ, 0 < z → z * deriv (fun z' : ℝ => ∫ t : ℝ,
        Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z' - t) * F t) z
      = ∫ t : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) * F t := by
  intro z hz
  have hz' : z ≠ 0 := ne_of_gt hz
  have hchain : HasDerivAt
      (fun z' : ℝ => ∫ t : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z' - t) * F t)
      ((∫ t : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) * F t) * z⁻¹) z :=
    (hasDerivAt_logConv F hF hδ0 (Real.log z)).comp z (Real.hasDerivAt_log hz')
  rw [hchain.deriv]
  field_simp

end Work.FTS.ClassC.RopGen.Trace.ZmollAux
