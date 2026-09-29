import Mathlib
import Submission.Work.GenShared.wevD

namespace Work.GenShared

open Complex Metric Work.GenShared

noncomputable section

/-- `Rval f` is continuous at every point at which `f` is regular: `Rval f` is the analytic
branch of the rational function `f` cut out by its canonical numerator/denominator
representative, and `hasDerivAt_rval` supplies a derivative there. -/
lemma continuousOn_rval {f : RatFunc ℂ} {s : Set ℂ} (h : ∀ z ∈ s, Rreg f z) :
    ContinuousOn (fun w => Rval f w) s :=
  fun z hz => ((hasDerivAt_rval f z (h z hz)).continuousAt).continuousWithinAt

/-- The derivative of a function holomorphic on an open set is continuous there. -/
lemma continuousOn_deriv_of_differentiableOn {f : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s)
    (hf : DifferentiableOn ℂ f s) : ContinuousOn (deriv f) s :=
  (((analyticOnNhd_iff_differentiableOn hs).mpr hf).deriv_of_isOpen hs).continuousOn

theorem continuousOn_wev_Dv {k : ℕ} (p2 p1 p0 : Polynomial ℂ) (rn rd : Fin k → Polynomial ℂ)
    (x0 : ℂ) {δ : ℝ} (y1 : ℂ → ℂ) (hy1d : DifferentiableOn ℂ y1 (Metric.ball x0 δ))
    (J : Fin k → ℂ → ℂ) (hJd : ∀ i, DifferentiableOn ℂ (J i) (Metric.ball x0 δ))
    (n : Work.GenShared.W k) :
    ContinuousOn (fun w => Work.GenShared.Wev y1 J (Work.GenShared.Dv p2 p1 p0 rn rd n) w)
      (Work.GenShared.Nset x0 δ (Work.GenShared.Dv p2 p1 p0 rn rd n)) := by
  set m : W k := Dv p2 p1 p0 rn rd n with hm
  have hsub : Nset x0 δ m ⊆ ball x0 δ := fun z hz => hz.1
  have hy1c : ContinuousOn y1 (Nset x0 δ m) := hy1d.continuousOn.mono hsub
  have hdy1c : ContinuousOn (deriv y1) (Nset x0 δ m) :=
    (continuousOn_deriv_of_differentiableOn isOpen_ball hy1d).mono hsub
  have hJc : ∀ i, ContinuousOn (J i) (Nset x0 δ m) := fun i => (hJd i).continuousOn.mono hsub
  show ContinuousOn (fun w => Rval m.1 w * y1 w + Rval m.2.1 w * deriv y1 w
    + ∑ i, Rval (m.2.2 i) w * J i w) (Nset x0 δ m)
  refine ContinuousOn.add (ContinuousOn.add ?_ ?_) ?_
  · exact (continuousOn_rval (f := m.1) (fun z hz => hz.2.1)).mul hy1c
  · exact (continuousOn_rval (f := m.2.1) (fun z hz => hz.2.2.1)).mul hdy1c
  · exact continuousOn_finsetSum Finset.univ (fun i _ =>
      (continuousOn_rval (f := m.2.2 i) (fun z hz => hz.2.2.2 i)).mul (hJc i))

end

end Work.GenShared
