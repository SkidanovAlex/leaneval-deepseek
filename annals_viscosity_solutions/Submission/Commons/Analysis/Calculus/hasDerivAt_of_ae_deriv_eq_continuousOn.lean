import Submission.Commons.Analysis.Calculus.hasDerivAt_of_ae_deriv_eq_continuousOn_finiteDimensional

namespace Commons.Analysis.Calculus

/-- If `f` is absolutely continuous on `[a,b]` and its (a.e. defined) derivative agrees a.e. on
`(a,b)` with a function `P` which is continuous on `[a,b]`, then `f` is differentiable at every
point of `(a,b)` with derivative `P`. -/
theorem hasDerivAt_of_ae_deriv_eq_continuousOn {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    {f P : ℝ → F} {a b : ℝ} (hab : a < b) (hac : AbsolutelyContinuousOnInterval f a b)
    (hP : ContinuousOn P (Set.Icc a b))
    (h : Filter.Eventually (fun t => t ∈ Set.Ioo a b → deriv f t = P t)
      (MeasureTheory.ae (MeasureTheory.volume : MeasureTheory.Measure ℝ))) :
    ∀ t ∈ Set.Ioo a b, HasDerivAt f (P t) t :=
  -- This is exactly the finite-dimensional (i.e. correct) form of the statement, already
  -- available in the shared library under the name
  -- `Commons.Analysis.Calculus.hasDerivAt_of_ae_deriv_eq_continuousOn_finiteDimensional`.
  -- (Without `[FiniteDimensional ℝ F]` the statement is false: `F = C([0,1], ℝ)` with
  -- `f t = |x - t|` is a counterexample, see
  -- `counterexample_deriv_ae_eq_continuousOn`.)
  hasDerivAt_of_ae_deriv_eq_continuousOn_finiteDimensional hab hac hP h

end Commons.Analysis.Calculus
