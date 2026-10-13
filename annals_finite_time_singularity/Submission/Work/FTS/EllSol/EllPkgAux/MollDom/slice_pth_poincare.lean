/-
# `Work.FTS.EllSol.EllPkgAux.MollDom.slice_pth_poincare`

**Slice Poincaré inequality for the angular derivative of a trace-class datum.**

For `G` in the trace class (`TraceClass G`) and a radius `w > 0`, the weighted `L²`-norm of the
angular derivative of the slice `s ↦ ∂_θG(w,s)` against the singular weight
`thEta s = sin(2s)^{-η}` is controlled by the *unweighted* `L²`-norm of the second angular
derivative of the slice:

  `∫_{Iθ} thEta s · (∂_θG(w,s))² ≤ C ∫_{Iθ} (∂_θ²G(w,s))²`.

There is no radial weight (`w(z)²`) on either side, so this is *not* the `SliceHonestOpen`
component of `TraceClass`; the estimate is the purely angular statement needed to turn the
weighted honesty of `∂_θ²` into the unweighted one.

**Proof.**  The function `f := ∂_θG(w,·)` has the three structural properties of the angular
Poincaré estimate `MollDom.thetaPoincare`:

* it is differentiable on the open interval with derivative `f' = ∂_θ²G(w,·)`
  (`SmoothOpen` of `pth (pth G)`);
* `f` and `f'²` are integrable on `Iθ` (`intervalIntegrable_pth_slice`, respectively the
  honesty of the `∂_θ²`-slot `SliceHonestOpen.1` of `TraceClass`, which dominates `f'²` a.e.
  because `thEta ≥ 1` on the open interval);
* `f` has vanishing mean: the slice `s ↦ G w s` is continuous on `[0, π/2]`
  (`slice_continuousOn`) with equal endpoint values `G w 0 = G w (π/2) = 0`, so the
  fundamental theorem of calculus gives `∫_{0}^{π/2} ∂_θG(w,s) ds = 0`.

`thetaPoincare` then yields the bound. -/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.thetaPoincare
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_deriv2_integrableOn
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_deriv_bdd
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_continuousOn
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.intervalIntegrable_pth_slice
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_deriv2_weighted_integrableOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

set_option maxHeartbeats 800000

/-- The `θ`-derivative of the `θ`-slice of a function smooth on the open quadrant. -/
private lemma hasDerivAt_slice_pth {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (fun θ' : ℝ => F z θ') (Work.Spaces.pth F z θ) θ := by
  have hd : DifferentiableAt ℝ (fun θ' : ℝ => F z θ') θ :=
    ((hF.curry_θ hz).differentiableOn
      (by rw [Work.Stability.smoothOrder]; simp)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  exact hd.hasDerivAt

theorem slice_pth_poincare (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    {w : ℝ} (hw : 0 < w) :
    ∃ C : ℝ, 0 < C ∧
      (∫ s in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta s * (Work.Spaces.pth G w s) ^ 2)
        ≤ C * (∫ s in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.pth G) w s) ^ 2) := by
  have hTcopy : Work.FTS.EllSol.EllPkgAux.TraceClass G := hT
  obtain ⟨hsm, h0, hpi, -, -, -, -, -⟩ := hT
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  -- ## The angular derivatives of the two slices
  have hd1 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun θ' : ℝ => G w θ') (Work.Spaces.pth G w θ) θ :=
    fun θ hθ => hasDerivAt_slice_pth hsm hw hθ
  have hd2 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun θ' : ℝ => Work.Spaces.pth G w θ')
        (Work.Spaces.pth (Work.Spaces.pth G) w θ) θ :=
    fun θ hθ => hasDerivAt_slice_pth hsm.pth hw hθ
  -- ## Integrability of `∂_θG(w,·)` on `Iθ`
  have hint : IntervalIntegrable (fun s : ℝ => Work.Spaces.pth G w s) volume 0 (Real.pi / 2) :=
    intervalIntegrable_pth_slice G hTcopy hw
  have hfint : IntegrableOn (fun s : ℝ => Work.Spaces.pth G w s) Work.Spaces.Iθ := by
    have h1 : IntegrableOn (fun s : ℝ => Work.Spaces.pth G w s) (Set.Ioc 0 (Real.pi / 2)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp hint
    exact h1.congr_set_ae (MeasureTheory.Ioc_ae_eq_Icc (μ := volume)).symm
  -- ## Vanishing mean of `∂_θG(w,·)` (FTC on the slice, whose endpoint values both vanish)
  have hmeanz : (∫ s in (0 : ℝ)..(Real.pi / 2), Work.Spaces.pth G w s) = 0 := by
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := (0 : ℝ))
      (b := Real.pi / 2) hle (slice_continuousOn G hTcopy hw) hd1 hint
    rw [hftc, hpi w, h0 w, sub_zero]
  have hmean : (∫ s in Work.Spaces.Iθ, Work.Spaces.pth G w s) = 0 := by
    show (∫ s in Set.Icc (0 : ℝ) (Real.pi / 2), Work.Spaces.pth G w s) = 0
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
    exact hmeanz
  -- ## Integrability of the squared second angular derivative on `Iθ`
  have hwint : IntegrableOn
      (fun s : ℝ => (Work.Spaces.pth (Work.Spaces.pth G) w s) ^ 2
        * Work.FTS.EllipticEst.thEta s) Work.Spaces.Iθ :=
    slice_deriv2_weighted_integrableOn (G := G) hTcopy (w := w) hw
  have haesm : AEStronglyMeasurable
      (fun s : ℝ => (Work.Spaces.pth (Work.Spaces.pth G) w s) ^ 2)
      (volume.restrict Work.Spaces.Iθ) := by
    have hc : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2)
        Work.FTS.EllipticEst.Q0 := (hsm.pth.pth).continuousOn
    have h := Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2) hc hw
    convert h.mul h using 1
    ext s
    rw [Pi.mul_apply, pow_two]
  have hf'int : IntegrableOn
      (fun s : ℝ => (Work.Spaces.pth (Work.Spaces.pth G) w s) ^ 2) Work.Spaces.Iθ := by
    refine Integrable.mono' hwint haesm ?_
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun s hs => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact le_mul_of_one_le_right (sq_nonneg _) (one_le_thEta_of_mem_Ioo hs)
  -- ## The angular Poincaré estimate applied to `f = ∂_θG(w,·)`
  exact thetaPoincare (f := fun s : ℝ => Work.Spaces.pth G w s)
    (f' := fun s : ℝ => Work.Spaces.pth (Work.Spaces.pth G) w s) hd2 hf'int hfint hmean

end Work.FTS.EllSol.EllPkgAux.MollDom
