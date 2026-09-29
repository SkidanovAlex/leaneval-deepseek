import Mathlib

/-!
# Analyticity tools: `Real.exp ∘ f`, `Real.sqrt ∘ f`

Two small closure lemmas for `AnalyticOnNhd ℝ`, used by the "SO(2) polar factor"
construction (`so2_polar_factor.lean`) and by `coboundary_of_conjugacy.lean`.

Mathlib has `AnalyticAt.log` for `Real.log` but no companion for `Real.exp`
(the real exponential is analytic because it is the restriction of `Complex.exp`).
`Real.sqrt` is then `exp ∘ (log / 2)` on the positive half-line.
-/

namespace Work.TMComp.RedProj

open Complex Real

/-- The real exponential, precomposed with an analytic function, is analytic. -/
theorem analyticAt_rexp {f : ℝ → ℝ} {x : ℝ} (hf : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (fun y => Real.exp (f y)) x := by
  have hC : AnalyticAt ℂ Complex.exp ((f x : ℂ)) := by
    rw [analyticAt_iff_eventually_differentiableAt]
    exact Filter.Eventually.of_forall fun z => Complex.differentiableAt_exp (x := z)
  have h1 : AnalyticAt ℝ (fun w : ℂ => Complex.exp w) ((f x : ℝ) : ℂ) := hC.restrictScalars
  have h2 : AnalyticAt ℝ (fun y : ℝ => ((f y : ℝ) : ℂ)) x :=
    (Complex.ofRealCLM.analyticAt (f x)).comp hf
  have h3 : AnalyticAt ℝ (fun y : ℝ => Complex.exp ((f y : ℝ) : ℂ)) x := h1.comp (x := x) h2
  have h4 : AnalyticAt ℝ (fun y : ℝ => (Complex.exp ((f y : ℝ) : ℂ)).re) x :=
    (Complex.reCLM.analyticAt _).comp h3
  refine h4.congr ?_
  filter_upwards with y
  simp [Complex.exp_ofReal_re]

theorem analyticOnNhd_rexp {f : ℝ → ℝ} {s : Set ℝ} (hf : AnalyticOnNhd ℝ f s) :
    AnalyticOnNhd ℝ (fun y => Real.exp (f y)) s :=
  fun x hx => analyticAt_rexp (hf x hx)

/-- `Real.sqrt ∘ f` is analytic wherever `f` is analytic and positive. -/
theorem analyticAt_sqrt {f : ℝ → ℝ} {x : ℝ} (hf : AnalyticAt ℝ f x) (hx : 0 < f x) :
    AnalyticAt ℝ (fun y => Real.sqrt (f y)) x := by
  have h1 : AnalyticAt ℝ (fun y => Real.log (f y)) x := hf.log hx
  have h2 : AnalyticAt ℝ (fun y => Real.log (f y) / 2) x := h1.div_const
  have h3 : AnalyticAt ℝ (fun y => Real.exp (Real.log (f y) / 2)) x := analyticAt_rexp h2
  refine h3.congr ?_
  filter_upwards [hf.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hx)] with y hy
  simp only [Set.mem_preimage, Set.mem_Ioi] at hy
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy]
  ring_nf

theorem analyticOnNhd_sqrt {f : ℝ → ℝ} {s : Set ℝ} (hf : AnalyticOnNhd ℝ f s)
    (hx : ∀ x ∈ s, 0 < f x) :
    AnalyticOnNhd ℝ (fun y => Real.sqrt (f y)) s :=
  fun x hx' => analyticAt_sqrt (hf x hx') (hx x hx')

end Work.TMComp.RedProj
