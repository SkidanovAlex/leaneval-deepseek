import Mathlib
import Submission.Work.FIArea6Hecke.ZFRDefs
import Submission.Work.FIArea5.HeckeZFR.Hadm.factorZero
import Submission.Work.FIArea5.HeckeZFR.Hadm.goodRadius
import Submission.Work.FIArea5.HeckeZFR.Hadm.cofactorBound
import Submission.Work.FIArea5.HeckeZFR.Hadm.pfConv
import Submission.Work.FIArea5.HeckeZFR.Lam_partialFraction
import Submission.Work.FIArea5.HeckeZFR.LamBaseBound
import Submission.Work.FIArea5.HeckeZFR.FELogDeriv
import Submission.Work.FIArea5.HeckeZFR.HeckeNonvanishing
import Submission.Work.FIArea6Hecke.R.HeckeLambdaLogDerivBounds
import Submission.Work.FIArea6Hecke.R.heckeStripNearOne
import Submission.Work.FIArea6Hecke.R.HeckeZFRCoreAsm
import Submission.Work.FIArea6Hecke.R.HeckeLDerivRe341
import Submission.Work.FIArea6Hecke.R.HeckeAxisLogDerivBound
import Submission.Work.FIArea6Hecke.R.ZFRStatementDefs
import Submission.Port.LogDerivCompat

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea6Hecke.R

open Complex Metric Filter
open scoped Topology BigOperators

noncomputable section

/-- `logDeriv` of the Hecke `L`-series in terms of the completion and the archimedean factor, at
points with `re s > 1`. -/
lemma logDeriv_L_eq (d : ℕ) (hd : 1 ≤ d) {chi : GaussianInt → ℂ} {m : ℤ} {Λ : ℂ → ℂ}
    (hAn : AnalyticOn ℂ Λ Set.univ) (h1 : chi 1 = 1)
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    (hagr : ∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
      Λ s = Work.FITop4.Bridge.heckeArch d m s *
        Work.FIArea5.S16Hecke.heckeLSeries chi m s)
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv (Work.FIArea5.S16Hecke.heckeLSeries chi m) s
      = logDeriv Λ s - logDeriv (Work.FITop4.Bridge.heckeArch d m) s := by
  have hmem : {z : ℂ | (1 : ℝ) < z.re} ∈ 𝓝 s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
  have hev : Λ =ᶠ[𝓝 s] fun z => Work.FITop4.Bridge.heckeArch d m z *
      Work.FIArea5.S16Hecke.heckeLSeries chi m z := by
    filter_upwards [hmem] with z hz
    exact Lam_eq_heckeArch_mul_of_one_lt_re hd hAn hb hagr hz
  have hArchne : Work.FITop4.Bridge.heckeArch d m s ≠ 0 :=
    heckeArch_ne_zero_of_one_lt_re hd m hs
  have hLne : Work.FIArea5.S16Hecke.heckeLSeries chi m s ≠ 0 :=
    Work.FIArea5.S16Hecke.heckeLSeries_ne_zero_of_one_lt_re chi m h1 hmul hb hs
  have hAd : DifferentiableAt ℂ (Work.FITop4.Bridge.heckeArch d m) s :=
    heckeArch_differentiableAt_of_pos hd m (by linarith)
  have hLd : DifferentiableAt ℂ (Work.FIArea5.S16Hecke.heckeLSeries chi m) s := by
    have habs : LSeries.abscissaOfAbsConv (Work.FIArea5.S16Hecke.heckeLam chi m) < (s.re : EReal) :=
      lt_of_le_of_lt (Work.FIArea5.S16Hecke.heckeLSeries_absc_le_one chi m hb)
        (EReal.coe_lt_coe_iff.mpr hs)
    exact (LSeries_hasDerivAt (f := Work.FIArea5.S16Hecke.heckeLam chi m) (s := s)
      habs).differentiableAt
  have hlog : logDeriv Λ s = logDeriv (Work.FITop4.Bridge.heckeArch d m) s
      + logDeriv (Work.FIArea5.S16Hecke.heckeLSeries chi m) s := by
    rw [(logDeriv_congr_nhds hev).eq_of_nhds]
    exact Submission.Port.logDeriv_mul_fun (f := Work.FITop4.Bridge.heckeArch d m)
      (g := Work.FIArea5.S16Hecke.heckeLSeries chi m) s hArchne hLne hAd hLd
  rw [hlog]; ring

/-- `Re (-L'/L)` in terms of the completion and the archimedean factor. -/
lemma neg_re_L_eq (d : ℕ) (hd : 1 ≤ d) {chi : GaussianInt → ℂ} {m : ℤ} {Λ : ℂ → ℂ}
    (hAn : AnalyticOn ℂ Λ Set.univ) (h1 : chi 1 = 1)
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    (hagr : ∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
      Λ s = Work.FITop4.Bridge.heckeArch d m s *
        Work.FIArea5.S16Hecke.heckeLSeries chi m s)
    {s : ℂ} (hs : 1 < s.re) :
    (-deriv (Work.FIArea5.S16Hecke.heckeLSeries chi m) s
        / Work.FIArea5.S16Hecke.heckeLSeries chi m s).re
      = -(deriv Λ s / Λ s).re
        + (logDeriv (Work.FITop4.Bridge.heckeArch d m) s).re := by
  have h := logDeriv_L_eq d hd hAn h1 hmul hb hagr hs
  rw [logDeriv_apply, logDeriv_apply, logDeriv_apply] at h
  have hgoal : (-deriv (Work.FIArea5.S16Hecke.heckeLSeries chi m) s
        / Work.FIArea5.S16Hecke.heckeLSeries chi m s)
      = -(deriv Λ s / Λ s) + logDeriv (Work.FITop4.Bridge.heckeArch d m) s := by
    rw [neg_div, h, logDeriv_apply]; ring
  rw [hgoal, Complex.add_re, Complex.neg_re]

end

end Work.FIArea6Hecke.R
