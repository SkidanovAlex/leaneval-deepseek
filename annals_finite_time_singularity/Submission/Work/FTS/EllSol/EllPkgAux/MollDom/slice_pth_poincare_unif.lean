/-
# `Work.FTS.EllSol.EllPkgAux.MollDom.slice_pth_poincare_unif`

**Uniform (in the radius `w`) slice Poincaré inequality for the angular derivative.**

The sibling `MollDom.slice_pth_poincare` proves, for each fixed radius `w > 0`, the weighted
angular Poincaré inequality

  `∫_{Iθ} thEta s · (∂_θG(w,s))² ≤ C_w ∫_{Iθ} (∂_θ²G(w,s))²`

with a constant `C_w` obtained from `MollDom.thetaPoincare` — an *existential* statement
whose witness a priori depends on the slice `f = ∂_θG(w,·)`.  Here the quantifier is
exchanged: a single constant works for every `w > 0`.

The point is that the underlying angular Poincaré estimate is uniform: its proof produces the
*same* explicit constant `10000·(π/2) + 1` for every datum, and that uniform form is already
available as `MollDom.thetaPoincare_unif`.  So the proof is the proof of the sibling with the
final application replaced.

**Proof.**  For `w > 0` put `f := ∂_θG(w,·)` and `f' := ∂_θ²G(w,·)`.  We must check the four
hypotheses of `thetaPoincare_unif`:

* `f` is differentiable on the open interval with derivative `f'`
  (`SmoothOpen.pth` of the trace-class datum `G`);
* `(f')²` is integrable on `Iθ` — this is the *honesty* of the `∂_θ²`-slot
  (`SliceHonestOpen.1` of `TraceClass`), which bounds the weighted square
  `(f')² · w(w)² · thEta`, both extra factors being `≥ 1` on the open interval;
* `f` is integrable on `Iθ` (`intervalIntegrable_pth_slice`, transported from the interval
  integral on `(0, π/2)`);
* `f` has vanishing mean over `Iθ`: the slice `s ↦ G w s` is continuous on `[0, π/2]`
  (`slice_continuousOn`) with equal endpoint values `G w 0 = G w (π/2) = 0`, so the
  fundamental theorem of calculus gives `∫_0^{π/2} ∂_θG(w,s) ds = 0`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.thetaPoincare_unif
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_pth_poincare
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_deriv2_integrableOn
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_deriv2_weighted_integrableOn
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.intervalIntegrable_pth_slice
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_continuousOn

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
private lemma hasDerivAt_slice_pth_unif {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (fun θ' : ℝ => F z θ') (Work.Spaces.pth F z θ) θ := by
  have hd : DifferentiableAt ℝ (fun θ' : ℝ => F z θ') θ :=
    ((hF.curry_θ hz).differentiableOn
      (by rw [Work.Stability.smoothOrder]; simp)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  exact hd.hasDerivAt

theorem slice_pth_poincare_unif (G : ℝ → ℝ → ℝ)
    (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℝ, 0 < w →
      (∫ s in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta s * (Work.Spaces.pth G w s) ^ 2)
        ≤ C * (∫ s in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.pth G) w s) ^ 2) := by
  -- the uniform angular Poincaré inequality supplies the constant once and for all
  obtain ⟨C, hC, hCbound⟩ := thetaPoincare_unif
  have hTcopy : Work.FTS.EllSol.EllPkgAux.TraceClass G := hT
  obtain ⟨hsm, h0, hpi, -, -, -, -, -⟩ := hT
  refine ⟨C, hC, ?_⟩
  intro w hw
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  -- ## The angular derivatives of the two slices
  have hd1 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun θ' : ℝ => G w θ') (Work.Spaces.pth G w θ) θ :=
    fun θ hθ => hasDerivAt_slice_pth_unif hsm hw hθ
  have hd2 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun θ' : ℝ => Work.Spaces.pth G w θ')
        (Work.Spaces.pth (Work.Spaces.pth G) w θ) θ :=
    fun θ hθ => hasDerivAt_slice_pth_unif hsm.pth hw hθ
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
  -- ## The *uniform* angular Poincaré estimate applied to `f = ∂_θG(w,·)`
  exact hCbound hd2 hf'int hfint hmean

end Work.FTS.EllSol.EllPkgAux.MollDom
