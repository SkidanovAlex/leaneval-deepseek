import Submission.Work.Smooth.JordanSeparation.offset_injective

/-!
# The collar of an immersed curve misses the curve

For an immersed simple `C¹` closed plane curve `c` carrying a Lipschitz unit field `v` uniformly
transverse to it (`IsTransverseUnitField`), the offset map `(t, u) ↦ c.γ t + u · v t` is injective on
a strip of width `δ` modulo the period (`offset_injective`); consequently the offsets of *non-zero*
height miss the trace:

`Work.Smooth.JordanSeparation.offset_notMem_trace`.

This is the elementary half of the collar theorem: the trace is the `u = 0` stratum of the collar
and every other stratum is off the curve. -/

open Work.Smooth.Jordan Work.Smooth.JordanSeparation

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- **The collar of an immersed closed curve misses the curve.**  Under the hypotheses of
`offset_injective` there is `δ > 0` such that every offset `c.γ t + u · v t` with `0 < |u| < δ`
avoids the trace of `c`. -/
theorem offset_notMem_trace (c : SmoothPlaneCurve)
    (himm : SmoothPlaneCurve.IsImmersion c) (hsimple : c.toPlaneCurve.IsSimple)
    {v : ℝ → ℂ} {κ L : ℝ} (hκ : 0 < κ) (hL : 0 < L)
    (hper : Function.Periodic v (2 * Real.pi))
    (htrans : IsTransverseUnitField c κ v) (hlip : IsLipschitzField L v) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t u : ℝ, 0 < |u| → |u| < δ → offset c v (t, u) ∉ c.trace := by
  obtain ⟨δ, hδpos, hinj⟩ := offset_injective c himm hsimple hκ hL hper htrans hlip
  refine ⟨δ, hδpos, fun t u hu huδ hmem => ?_⟩
  obtain ⟨t', ht'⟩ := hmem
  have hzero : |(0 : ℝ)| < δ := by simpa using hδpos
  have h := hinj t t' u 0 huδ hzero (by rw [offset_zero]; exact ht'.symm)
  rw [h.1] at hu
  simp at hu

end

end Work.Smooth.JordanSeparation
