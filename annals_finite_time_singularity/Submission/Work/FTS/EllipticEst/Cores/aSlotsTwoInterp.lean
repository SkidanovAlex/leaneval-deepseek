import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.H2W.lzeroSliceL1Ae
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.TT.interpGamma
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.StrongPersist.QangSq6
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.WPQ.hardy_slice_Aang

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

local notation "Aof" => Work.FTS.EllipticEst.H2W.Aof

/-! ## Congruence of `L2Sq` on the open quadrant -/

/-- **The weighted `L2Sq` of two functions agreeing on the open quadrant.**  The weight `Wt α`
vanishes on the degenerate set `{z = 0} ∪ {θ = 0} ∪ {θ = π/2}` (Lean's `rpow` gives
`0^x = 0` for `x ≠ 0`), so the integrands agree *pointwise* on `Iz × Iθ`. -/
theorem l2sq_congr_q {α : ℝ} (hα : 0 < α) {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) :
    Work.Spaces.L2Sq (fun z θ => f z θ * Work.Spaces.Wt α z θ)
      = Work.Spaces.L2Sq (fun z θ => g z θ * Work.Spaces.Wt α z θ) := by
  have hgam : 0 < Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hexp : -(Work.Spaces.gam α / 2) ≠ 0 := by linarith
  rw [Work.Spaces.L2Sq, Work.Spaces.L2Sq]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z hz => ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hz0
  · subst hz0; simp [Work.Spaces.Wt, Work.Spaces.w]
  rcases eq_or_lt_of_le hθ.1 with hθ0 | hθ0
  · subst hθ0
    have hzero : Work.Spaces.Wt α z 0 = 0 := by
      simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
      rw [show 2 * (0 : ℝ) = 0 by ring, Real.sin_zero]
      simp [Real.zero_rpow hexp]
    rw [hzero]; ring
  rcases eq_or_lt_of_le hθ.2 with hθ2 | hθ2
  · subst hθ2
    have hzero : Work.Spaces.Wt α z (Real.pi / 2) = 0 := by
      simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
      rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      simp [Real.zero_rpow hexp]
    rw [hzero]; ring
  · rw [h z θ hz0 hθ0 hθ2]

/-! ## The two statement-level `Prop`s of the interpolation -/

/-- **The analytic core of the light-weight interpolation** (the input `hcore` of
`TT.interpGamma_of_core`, and verbatim the statement of `TT.interpGamma_core`). -/
def InterpGammaCore : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (G : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.SmoothOpen G →
      (∀ z : ℝ, G z 0 = 0) → (∀ z : ℝ, G z (Real.pi / 2) = 0) →
      Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 2 G) →
      Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 G) →
      Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 1 G) →
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iz →
      Work.FTS.EllipticEst.TT.Xint α G
        ≤ C * (Real.sqrt (Work.FTS.EllipticEst.TT.DDint α G
              * Work.FTS.EllipticEst.TT.TTint α G)
            + Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 G))



/-! ## The hypotheses of the interpolation at `G = A` -/


/-! ## The reduction -/


end

end Work.FTS.EllipticEst.Cores
