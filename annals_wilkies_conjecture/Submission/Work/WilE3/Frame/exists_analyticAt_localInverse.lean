import Mathlib

namespace Work.WilE3.Frame

open Classical Topology

/-- **Analytic inverse function theorem.** If `f : E → F` is complex-analytic at `a` with invertible
strict derivative `f'` there, then there is a complex-analytic local inverse `g` of `f` at `f a`,
with derivative `f'.symm`. -/
theorem exists_analyticAt_localInverse {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (f : E → F)
    (f' : E ≃L[ℂ] F) (a : E) (hf : HasStrictFDerivAt f (f' : E →L[ℂ] F) a)
    (han : AnalyticAt ℂ f a) :
    ∃ g : F → E, g (f a) = a ∧ AnalyticAt ℂ g (f a) ∧
      (∀ᶠ y in 𝓝 (f a), f (g y) = y) ∧
      HasStrictFDerivAt g (f'.symm : F →L[ℂ] E) (f a) := by
  -- `f` is analytic at `a`, so it has a power series `p` there.
  rcases han with ⟨p, hp⟩
  -- The open partial homeomorphism produced by the (strict) inverse function theorem,
  -- whose inverse function is `hf.localInverse f f' a`.
  have ha : a ∈ (hf.toOpenPartialHomeomorph f).source := hf.mem_toOpenPartialHomeomorph_source
  -- The linear coefficient of `p` is the strict derivative `f'`.
  have hp1 : p 1 = (continuousMultilinearCurryFin1 ℂ E F).symm (f' : E →L[ℂ] F) := by
    have h1 : HasFDerivAt f ((continuousMultilinearCurryFin1 ℂ E F) (p 1)) a := hp.hasFDerivAt
    have h2 : HasFDerivAt f (f' : E →L[ℂ] F) a := hf.hasFDerivAt
    have h3 : (continuousMultilinearCurryFin1 ℂ E F) (p 1) = (f' : E →L[ℂ] F) := h1.unique h2
    have h4 := congrArg (fun L : E →L[ℂ] F ↦ (continuousMultilinearCurryFin1 ℂ E F).symm L) h3
    simpa using h4
  -- The inverse of the partial homeomorphism is analytic at `f a`, its power series being the
  -- left inverse series of `p`.
  have han' : AnalyticAt ℂ ((hf.toOpenPartialHomeomorph f).symm) (f a) :=
    ((hf.toOpenPartialHomeomorph f).hasFPowerSeriesAt_symm ha hp hp1).analyticAt
  exact ⟨(hf.toOpenPartialHomeomorph f).symm, hf.localInverse_apply_image, han',
    hf.eventually_right_inverse, hf.to_localInverse⟩

end Work.WilE3.Frame
