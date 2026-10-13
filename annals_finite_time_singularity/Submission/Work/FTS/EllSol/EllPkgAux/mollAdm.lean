import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.MollConvDefs
import Submission.Work.FTS.EllSol.EllPkgAux.MollKdAux
import Submission.Work.FTS.EllSol.EllPkgAux.MollSmooth.sliceDom
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

namespace Work.FTS.EllSol.EllPkgAux

theorem mollAdm : ∀ (G : ℝ → ℝ → ℝ), Work.FTS.EllSol.EllPkgAux.TraceClass G → Work.FTS.EllSol.EllPkgAux.FourInts G → ∀ (δ ε : ℝ), Work.FTS.EllSol.EllPkgAux.Params δ ε → Work.FTS.EllSol.EllPkgAux.StripAdm G δ ε := by
  intro G hTC hFI δ ε hP
  obtain ⟨hεpos, hεle, hδpos, hδle⟩ := hP
  obtain ⟨hS, h0, hpi0, hlim0, hlimpi, hdz0, hdzpi, hhon⟩ := hTC
  have hdom := Work.FTS.EllSol.EllPkgAux.MollSmooth.sliceDom G hS hhon
  have hint := Work.FTS.EllSol.EllPkgAux.MollSmooth.MG_integrableOn G hS hFI
  have hloc := Work.FTS.EllSol.EllPkgAux.MollSmooth.Hxy_quad_locallyIntegrable G hS hdom hint
  refine ⟨?_, ?_, ?_⟩
  · intro n
    have hKsm : ContDiff ℝ n (Kd δ ε) := Kd_contDiff δ ε n
    have hKcs : HasCompactSupport (Kd δ ε) := Kd_hasCompactSupport δ ε hδpos hεpos
    have hconvsm : ContDiff ℝ n
        (MeasureTheory.convolution (Hxy (Gquad G)) (Kd δ ε)
          (ContinuousLinearMap.mul ℝ ℝ) MeasureTheory.volume) :=
      hKcs.contDiff_convolution_right (n := (n : ℕ∞))
        (ContinuousLinearMap.mul ℝ ℝ) hloc hKsm
    have hlog : ContDiffOn ℝ n (fun q : ℝ × ℝ => Real.log q.1) Strp := by
      have h : ContDiffOn ℝ n (Real.log ∘ Prod.fst) Strp :=
        Real.contDiffOn_log.comp contDiffOn_fst (fun q hq => by
          simp only [Strp, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hq
          exact ne_of_gt hq.1)
      simpa only [Function.comp_def] using h
    have hmap : ContDiffOn ℝ n (fun q : ℝ × ℝ => (Real.log q.1, q.2)) Strp :=
      hlog.prodMk contDiffOn_snd
    have hcomp : ContDiffOn ℝ n (fun q : ℝ × ℝ =>
        MeasureTheory.convolution (Hxy (Gquad G)) (Kd δ ε)
          (ContinuousLinearMap.mul ℝ ℝ) MeasureTheory.volume (Real.log q.1, q.2)) Strp :=
      hconvsm.comp_contDiffOn hmap
    refine hcomp.congr ?_
    rintro ⟨z, θ⟩ hq
    simp only [Strp, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hq
    obtain ⟨hz, hθ1, hθ2⟩ := hq
    show Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε z θ
        = MeasureTheory.convolution (Hxy (Gquad G)) (Kd δ ε)
            (ContinuousLinearMap.mul ℝ ℝ) MeasureTheory.volume (Real.log z, θ)
    rw [← Work.FTS.EllSol.EllPkgAux.MollSmooth.zmoll_Gquad_eq_zmoll G h0 hpi0 δ ε hεpos hεle
      z θ ⟨hθ1, hθ2⟩]
    exact Work.FTS.EllSol.EllPkgAux.MollSmooth.zmoll_Gquad_eq_conv G hloc δ ε hδpos hεpos
      z θ hz
  · exact Work.FTS.EllSol.EllPkgAux.MollSmooth.zmoll_theta_zero G δ ε hεpos hεle
  · exact Work.FTS.EllSol.EllPkgAux.MollSmooth.zmoll_theta_pihalf G δ ε hεpos hεle

end Work.FTS.EllSol.EllPkgAux
