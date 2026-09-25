import Mathlib
import Submission.Work.NN.Core.TelTwoDF.exists_analytic_holomorphic_dbar_split

namespace Work.NN.Core.TelTwoDF

open Set

/-- **Analyticity of the fibre data of an analytic function.**

Let `0 < Q s` and let `g` be real analytic on the polydisc `polydisc 0 Q`.  Then the data
`(z, w) ↦ g (Function.update z s w)` is real analytic on the product
`polydisc 0 Q × ball 0 (Q s)`.

Route: the map `insL s : (ℂⁿ × ℂ) → ℂⁿ`, `insL s (z, w) = Function.update z s w`, is a continuous
linear map (`Work.NN.Core.TelTwoDF.insL`, `insL_apply` in
`Submission/Work/NN/Core/TelTwoDF/exists_analytic_holomorphic_dbar_split.lean`), hence real
analytic everywhere; it maps the product into `polydisc 0 Q` because the `s`-th coordinate of
`update z s w` is `w` with `‖w‖ < Q s` and the other coordinates are those of `z`. -/
theorem analyticOn_update_comp {n : ℕ} (s : Fin n) {Q : Fin n → ℝ} (hQs : 0 < Q s)
    {g : (Fin n → ℂ) → ℂ} (hg : AnalyticOn ℝ g (Work.CR.Flat.polydisc 0 Q)) :
    AnalyticOn ℝ (fun r : (Fin n → ℂ) × ℂ => g (Function.update r.1 s r.2))
      (Work.CR.Flat.polydisc 0 Q ×ˢ Metric.ball (0 : ℂ) (Q s)) := by
  -- `insL s` maps the product into the polydisc.
  have hmaps : MapsTo (insL s)
      (Work.CR.Flat.polydisc 0 Q ×ˢ Metric.ball (0 : ℂ) (Q s))
      (Work.CR.Flat.polydisc 0 Q) := by
    rintro ⟨z, w⟩ ⟨hz, hw⟩ j
    rw [insL_apply]
    by_cases hj : j = s
    · subst hj
      rw [Function.update_self]
      rw [Metric.mem_ball, dist_eq_norm] at hw
      simpa using hw
    · rw [Function.update_of_ne hj]
      exact hz j
  -- `insL s` is a continuous linear map, hence real analytic.
  have hcomp := hg.comp (ContinuousLinearMap.analyticOn (insL s) _) hmaps
  -- Rewrite `g ∘ insL s` as the stated function.
  refine AnalyticOn.congr hcomp ?_
  rintro ⟨z, w⟩ -
  simp only [Function.comp_apply, insL_apply]

end Work.NN.Core.TelTwoDF
