import Mathlib
import Submission.Work.WilE3.Frame.straighteningDefs
import Submission.Work.WilE3.API.eaEvalC_fderiv_analytic

namespace Work.WilE3.Frame

/-- The straightening map `PhiC c h ι z = (uCoord k ι z, eaEvalC c (h ·) z)` is complex-analytic at
the real base point `toC x` (in fact at every point). -/
theorem analyticAt_PhiC {k r j : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (h : Fin j → WilkiesDesign.E.EAPoly k r) (ι : Fin j → Fin k) (x : Fin k → ℝ) :
    AnalyticAt ℂ (Work.WilE3.Frame.PhiC c h ι) (Work.WilE3.Frame.toC x) := by
  -- `PhiC` is a pair, and analyticity into a normed product is componentwise.  The first
  -- component `uCoord k ι` is the continuous linear projection onto the `ι`-complement
  -- coordinates, hence analytic; the second component is componentwise `eaEvalC c (h a)`, which
  -- is analytic at every point by `eaEvalC_fderiv_analytic`.
  have h1 : AnalyticAt ℂ (Work.WilE3.Frame.uCoord k ι) (Work.WilE3.Frame.toC x) := by
    have hclm : Work.WilE3.Frame.uCoord k ι = ⇑(ContinuousLinearMap.pi fun i : U k ι =>
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i.1)) := by
      funext z i
      rfl
    rw [hclm]
    exact ContinuousLinearMap.analyticAt _ _
  have h2 : AnalyticAt ℂ (fun z => fun a => Work.WilE3.eaEvalC c (h a) z)
      (Work.WilE3.Frame.toC x) :=
    AnalyticAt.pi fun a =>
      (Work.WilE3.API.eaEvalC_fderiv_analytic c (h a) (Work.WilE3.Frame.toC x)).1
  exact h1.prod h2

end Work.WilE3.Frame
