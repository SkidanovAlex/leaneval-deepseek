/-
# `Work.FTS.EllSol.EllPkgAux.MollAssem.StripAdm` — strip-admissibility of the approximant

`sliceDomMFA` is the slice domination `|G w τ| ≤ MG G w` (second-order Taylor formula at
`θ = π/4` + the interval estimate `MollAssem.sliceIntBoundMFA`), i.e. `MollSmooth.sliceDom`
with its missing ingredient supplied; `mollAdmMFA` then assembles the strip-admissibility
`StripAdm G δ ε` of `zmoll G δ ε` from the sorry-free convolution pieces of `MollSmooth`
(`zmoll_Gquad_eq_conv`, `zmoll_Gquad_eq_zmoll`, `zmoll_theta_zero`, `zmoll_theta_pihalf`,
`MG_integrableOn`, `Hxy_quad_locallyIntegrable`).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.MollAssem.Defs
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.MollConvDefs
import Submission.Work.FTS.EllSol.EllPkgAux.MollKdAux
import Submission.Work.FTS.EllSol.EllPkgAux.MollSmooth.slice_taylor_two
import Submission.Work.FTS.EllSol.EllPkgAux.MollSmooth.slice_dd_cont
import Submission.Work.FTS.EllSol.EllPkgAux.MollSmooth.MG_integrableOn
import Submission.Work.FTS.EllSol.EllPkgAux.MollSmooth.Hxy_quad_locallyIntegrable
import Submission.Work.FTS.EllSol.EllPkgAux.MollSmooth.zmoll_Gquad_eq_conv
import Submission.Work.FTS.EllSol.EllPkgAux.MollSmooth.zmoll_Gquad_eq_zmoll
import Submission.Work.FTS.EllSol.EllPkgAux.MollSmooth.zmoll_theta_zero
import Submission.Work.FTS.EllSol.EllPkgAux.MollSmooth.zmoll_theta_pihalf

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace MollAssem

/-! ## Strip-admissibility and slice honesty of the approximants -/

/-- The slice domination `|G w τ| ≤ MG G w` (the second-order Taylor formula at `θ = π/4`
plus the weighted Cauchy--Schwarz `sliceIntBoundMFA`).  This is `MollSmooth.sliceDom` with the
missing ingredient filled in, so that the present module does not depend on a `sorry`. -/
theorem sliceDomMFA (G : ℝ → ℝ → ℝ) (hS : Work.FTS.EllipticEst.SmoothOpen G)
    (hH : Work.EllipticEst.Core.i0Aux.SliceHonestOpen G) :
    ∀ w : ℝ, 0 < w → ∀ τ : ℝ, τ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      |G w τ| ≤ Work.FTS.EllSol.EllPkgAux.MG G w := by
  intro w hw τ hτ
  have hτ0 : 0 < τ := hτ.1
  have hτ1 : τ < Real.pi / 2 := hτ.2
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsmo : (2 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
    simp [Work.Stability.smoothOrder]
  have hf2 : ContDiffOn ℝ 2 (fun θ : ℝ => G w θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hS.curry_θ hw).of_le hsmo
  have ha0 : (0 : ℝ) < Real.pi / 4 := by linarith
  have ha1 : Real.pi / 4 < Real.pi / 2 := by linarith
  have ha_mem : (Real.pi / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨ha0, ha1⟩
  have hHint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
    have hc : (0 : ℝ) < (Work.Spaces.w w) ^ 2 := by
      rw [Work.Spaces.w]; positivity
    have h0 := hH.1 w hw
    have hEq : ∀ θ : ℝ, ((Work.Spaces.w w) ^ 2)⁻¹ *
        (Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * (Work.Spaces.w w) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
        = Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * Work.FTS.EllipticEst.thEta θ := by
      intro θ
      rw [show Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * (Work.Spaces.w w) ^ 2
            * Work.FTS.EllipticEst.thEta θ
          = (Work.Spaces.w w) ^ 2 * (Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2
            * Work.FTS.EllipticEst.thEta θ) from by ring]
      exact inv_mul_cancel_left₀ (ne_of_gt hc) _
    rw [show (fun θ : ℝ => Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2
          * Work.FTS.EllipticEst.thEta θ)
        = fun θ : ℝ => ((Work.Spaces.w w) ^ 2)⁻¹ *
          (Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * (Work.Spaces.w w) ^ 2
            * Work.FTS.EllipticEst.thEta θ) from funext (fun θ => (hEq θ).symm)]
    exact h0.const_mul _
  have hT := Work.FTS.EllSol.EllPkgAux.MollSmooth.slice_taylor_two hf2 ha_mem hτ
  have hTail : |∫ t in (Real.pi / 4)..τ,
        (τ - t) * deriv (deriv (fun θ : ℝ => G w θ)) t|
      ≤ (Real.pi / 4) * Real.sqrt (Real.pi / 4) *
        Real.sqrt (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
    rcases le_total (Real.pi / 4) τ with hle | hle
    · have hcont : ContinuousOn (fun t : ℝ => deriv (deriv (fun θ : ℝ => G w θ)) t)
          (Set.uIcc (Real.pi / 4) τ) :=
        Work.FTS.EllSol.EllPkgAux.MollSmooth.slice_dd_cont hf2 ha_mem hτ
      have hc : ∀ t ∈ Set.Icc (Real.pi / 4) τ, |τ - t| ≤ Real.pi / 4 := by
        intro t ht
        rw [abs_of_nonneg (by linarith [ht.2])]
        linarith [ht.1]
      exact sliceIntBoundMFA hle ha0 hτ1 (by linarith)
        hcont hc hHint
    · have hcont : ContinuousOn (fun t : ℝ => deriv (deriv (fun θ : ℝ => G w θ)) t)
          (Set.uIcc τ (Real.pi / 4)) :=
        Work.FTS.EllSol.EllPkgAux.MollSmooth.slice_dd_cont hf2 hτ ha_mem
      have hc : ∀ t ∈ Set.Icc τ (Real.pi / 4), |τ - t| ≤ Real.pi / 4 := by
        intro t ht
        rw [abs_of_nonpos (by linarith [ht.1])]
        linarith [ht.2]
      have h := sliceIntBoundMFA hle hτ0 ha1 (by linarith)
        hcont hc hHint
      rw [intervalIntegral.integral_symm, abs_neg]
      exact h
  have hMG : Work.FTS.EllSol.EllPkgAux.MG G w
      = |G w (Real.pi / 4)| + |Work.Spaces.pth G w (Real.pi / 4)|
        + Real.sqrt (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * Work.FTS.EllipticEst.thEta θ) := rfl
  rw [hMG]
  have habs : |τ - Real.pi / 4| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [Real.pi_le_four, Real.pi_pos]
  have hdnn : (0 : ℝ) ≤ |deriv (fun θ : ℝ => G w θ) (Real.pi / 4)| := abs_nonneg _
  have hcoef : (Real.pi / 4) * Real.sqrt (Real.pi / 4) ≤ 1 := by
    have h1 : Real.pi / 4 ≤ 1 := by linarith [Real.pi_le_four]
    have h2 : Real.sqrt (Real.pi / 4) ≤ 1 := Real.sqrt_le_one.mpr h1
    nlinarith [Real.sqrt_nonneg (Real.pi / 4)]
  have hsnn : (0 : ℝ) ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ,
      Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * Work.FTS.EllipticEst.thEta θ) :=
    Real.sqrt_nonneg _
  calc |G w τ|
      = |G w (Real.pi / 4) + (τ - Real.pi / 4) * deriv (fun θ : ℝ => G w θ) (Real.pi / 4)
          + ∫ t in (Real.pi / 4)..τ, (τ - t) * deriv (deriv (fun θ : ℝ => G w θ)) t| := by
        rw [hT]
    _ ≤ |G w (Real.pi / 4)| + |τ - Real.pi / 4| * |deriv (fun θ : ℝ => G w θ) (Real.pi / 4)|
          + |∫ t in (Real.pi / 4)..τ, (τ - t) * deriv (deriv (fun θ : ℝ => G w θ)) t| := by
        have h1 := abs_add_le
          (G w (Real.pi / 4) + (τ - Real.pi / 4) * deriv (fun θ : ℝ => G w θ) (Real.pi / 4))
          (∫ t in (Real.pi / 4)..τ, (τ - t) * deriv (deriv (fun θ : ℝ => G w θ)) t)
        have h2 := abs_add_le (G w (Real.pi / 4))
          ((τ - Real.pi / 4) * deriv (fun θ : ℝ => G w θ) (Real.pi / 4))
        rw [abs_mul] at h2
        linarith [h1, h2]
    _ ≤ |G w (Real.pi / 4)| + 1 * |deriv (fun θ : ℝ => G w θ) (Real.pi / 4)|
          + 1 * Real.sqrt (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
        have hmul : |τ - Real.pi / 4| * |deriv (fun θ : ℝ => G w θ) (Real.pi / 4)|
            ≤ 1 * |deriv (fun θ : ℝ => G w θ) (Real.pi / 4)| :=
          mul_le_mul_of_nonneg_right habs hdnn
        have hc2 : (Real.pi / 4) * Real.sqrt (Real.pi / 4) *
              Real.sqrt (∫ θ in Work.Spaces.Iθ,
                Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * Work.FTS.EllipticEst.thEta θ)
            ≤ 1 * Real.sqrt (∫ θ in Work.Spaces.Iθ,
                Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * Work.FTS.EllipticEst.thEta θ) :=
          mul_le_mul_of_nonneg_right hcoef hsnn
        linarith [hmul, hc2, hTail]
    _ = |G w (Real.pi / 4)| + |Work.Spaces.pth G w (Real.pi / 4)|
          + Real.sqrt (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
        rw [one_mul, one_mul]
        rfl

/-- **Strip-admissibility of the approximant**: `zmoll G δ ε` is `C^∞` on the half strip
`(0,∞) × (-1, π/2+1)` and vanishes at `θ = 0, π/2`, from the trace class and the four
integrabilities of `G`.  (Same statement as `mollAdm`, assembled here from the sorry-free
`MollSmooth` pieces and the locally proved `sliceDomMFA`.) -/
theorem mollAdmMFA : ∀ (G : ℝ → ℝ → ℝ), Work.FTS.EllSol.EllPkgAux.TraceClass G →
    Work.FTS.EllSol.EllPkgAux.FourInts G → ∀ (δ ε : ℝ), Work.FTS.EllSol.EllPkgAux.Params δ ε →
      Work.FTS.EllSol.EllPkgAux.StripAdm G δ ε := by
  intro G hTC hFI δ ε hP
  obtain ⟨hεpos, hεle, hδpos, hδle⟩ := hP
  obtain ⟨hS, h0, hpi0, hlim0, hlimpi, hdz0, hdzpi, hhon⟩ := hTC
  have hdom := sliceDomMFA G hS hhon
  have hint := Work.FTS.EllSol.EllPkgAux.MollSmooth.MG_integrableOn G hS hFI
  have hloc := Work.FTS.EllSol.EllPkgAux.MollSmooth.Hxy_quad_locallyIntegrable G hS hdom hint
  refine ⟨?_, ?_, ?_⟩
  · intro n
    have hKsm : ContDiff ℝ n (Work.FTS.EllSol.EllPkgAux.Kd δ ε) :=
      Work.FTS.EllSol.EllPkgAux.Kd_contDiff δ ε n
    have hKcs : HasCompactSupport (Work.FTS.EllSol.EllPkgAux.Kd δ ε) :=
      Work.FTS.EllSol.EllPkgAux.Kd_hasCompactSupport δ ε hδpos hεpos
    have hconvsm : ContDiff ℝ n
        (MeasureTheory.convolution
          (Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G))
          (Work.FTS.EllSol.EllPkgAux.Kd δ ε)
          (ContinuousLinearMap.mul ℝ ℝ) MeasureTheory.volume) :=
      hKcs.contDiff_convolution_right (n := (n : ℕ∞))
        (ContinuousLinearMap.mul ℝ ℝ) hloc hKsm
    have hlog : ContDiffOn ℝ n (fun q : ℝ × ℝ => Real.log q.1)
        Work.FTS.EllSol.EllPkgAux.Strp := by
      have h : ContDiffOn ℝ n (Real.log ∘ Prod.fst) Work.FTS.EllSol.EllPkgAux.Strp :=
        Real.contDiffOn_log.comp contDiffOn_fst (fun q hq => by
          simp only [Work.FTS.EllSol.EllPkgAux.Strp, Set.mem_prod, Set.mem_Ioi,
            Set.mem_Ioo] at hq
          exact ne_of_gt hq.1)
      simpa only [Function.comp_def] using h
    have hmap : ContDiffOn ℝ n (fun q : ℝ × ℝ => (Real.log q.1, q.2))
        Work.FTS.EllSol.EllPkgAux.Strp :=
      hlog.prodMk contDiffOn_snd
    have hcomp : ContDiffOn ℝ n (fun q : ℝ × ℝ =>
        MeasureTheory.convolution
          (Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G))
          (Work.FTS.EllSol.EllPkgAux.Kd δ ε)
          (ContinuousLinearMap.mul ℝ ℝ) MeasureTheory.volume (Real.log q.1, q.2))
        Work.FTS.EllSol.EllPkgAux.Strp :=
      hconvsm.comp_contDiffOn hmap
    refine hcomp.congr ?_
    rintro ⟨z, θ⟩ hq
    simp only [Work.FTS.EllSol.EllPkgAux.Strp, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hq
    obtain ⟨hz, hθ1, hθ2⟩ := hq
    show Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε z θ
        = MeasureTheory.convolution
            (Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G))
            (Work.FTS.EllSol.EllPkgAux.Kd δ ε)
            (ContinuousLinearMap.mul ℝ ℝ) MeasureTheory.volume (Real.log z, θ)
    rw [← Work.FTS.EllSol.EllPkgAux.MollSmooth.zmoll_Gquad_eq_zmoll G h0 hpi0 δ ε hεpos hεle
      z θ ⟨hθ1, hθ2⟩]
    exact Work.FTS.EllSol.EllPkgAux.MollSmooth.zmoll_Gquad_eq_conv G hloc δ ε hδpos hεpos
      z θ hz
  · exact Work.FTS.EllSol.EllPkgAux.MollSmooth.zmoll_theta_zero G δ ε hεpos hεle
  · exact Work.FTS.EllSol.EllPkgAux.MollSmooth.zmoll_theta_pihalf G δ ε hεpos hεle

end MollAssem

end Work.FTS.EllSol.EllPkgAux
