/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Auxiliary facts about the cutoff `openCut`

`openCut ζ = σ((cutOut² - ‖ζ‖²)/(cutOut² - cutIn²))` where `σ = Real.smoothTransition`
is the standard `C^∞` step function, equal to `1` on `[1,∞)` and to `0` on `(-∞,0]`.

This file collects the elementary properties of `openCut` used by
`Work.CR.Flat.Cauchy.openCut_props`:

* `openCut` is the composition of `σ` with an affine function of `‖ζ‖²`,
  recorded as `openCut ζ = (openCutReal (Complex.normSq ζ) : ℂ)`;
* it is `1` on `‖ζ‖ ≤ cutIn` and `0` on `cutOut ≤ ‖ζ‖`;
* it is `C^∞` and bounded by `1`;
* `openCutReal` has vanishing derivative on the two regions
  (`‖ζ‖ ≤ cutIn` and `cutOut ≤ ‖ζ‖`), which is what makes `∂̄ openCut` vanish there.
-/
import Mathlib
import Submission.Work.CR.Flat.Cauchy.openSolDefs

noncomputable section

open scoped NNReal ENNReal ContDiff
open MeasureTheory Set

namespace Work.CR.Flat.Cauchy

/-- The radial profile of the cutoff: `openCut ζ = (openCutReal (‖ζ‖²) : ℂ)`. -/
noncomputable def openCutReal (s : ℝ) : ℝ :=
  Real.smoothTransition ((cutOut ^ 2 - s) / (cutOut ^ 2 - cutIn ^ 2))

lemma cutIn_pos : 0 < cutIn := by rw [cutIn]; norm_num

lemma cutOut_pos : 0 < cutOut := by rw [cutOut]; norm_num

lemma cutOut_sq_sub_cutIn_sq_pos : 0 < cutOut ^ 2 - cutIn ^ 2 := by
  rw [cutOut, cutIn]; norm_num

lemma openCutReal_nonneg (s : ℝ) : 0 ≤ openCutReal s :=
  Real.smoothTransition.nonneg _

lemma openCutReal_le_one (s : ℝ) : openCutReal s ≤ 1 :=
  Real.smoothTransition.le_one _

lemma openCut_eq_openCutReal (ζ : ℂ) : openCut ζ = (openCutReal (Complex.normSq ζ) : ℂ) := by
  rw [openCut, openCutReal, Complex.normSq_eq_norm_sq]

lemma openCut_eq_fun : openCut = fun w : ℂ => (openCutReal (Complex.normSq w) : ℂ) :=
  funext openCut_eq_openCutReal

/-- On `‖ζ‖ ≤ cutIn` the profile argument is `≥ 1`, hence `σ = 1`. -/
lemma openCutReal_eq_one_of_le {s : ℝ} (hs : s ≤ cutIn ^ 2) : openCutReal s = 1 := by
  rw [openCutReal, Real.smoothTransition.one_of_one_le]
  rw [le_div_iff₀ cutOut_sq_sub_cutIn_sq_pos]
  linarith

/-- On `cutOut ≤ ‖ζ‖` the profile argument is `≤ 0`, hence `σ = 0`. -/
lemma openCutReal_eq_zero_of_le {s : ℝ} (hs : cutOut ^ 2 ≤ s) : openCutReal s = 0 := by
  rw [openCutReal, Real.smoothTransition.zero_of_nonpos]
  apply div_nonpos_of_nonpos_of_nonneg _ cutOut_sq_sub_cutIn_sq_pos.le
  linarith

lemma contDiff_openCutReal : ContDiff ℝ ∞ openCutReal := by
  have h : ContDiff ℝ ∞ (fun s : ℝ => (cutOut ^ 2 - s) / (cutOut ^ 2 - cutIn ^ 2)) := by
    have h' : (fun s : ℝ => (cutOut ^ 2 - s) / (cutOut ^ 2 - cutIn ^ 2))
        = fun s : ℝ => (cutOut ^ 2 - s) * (cutOut ^ 2 - cutIn ^ 2)⁻¹ := by
      funext s; rw [div_eq_mul_inv]
    rw [h']; fun_prop
  exact (Real.smoothTransition.contDiff (n := ⊤)).comp h

lemma contDiff_normSq : ContDiff ℝ ∞ (fun ζ : ℂ => Complex.normSq ζ) := by
  have h : (fun ζ : ℂ => Complex.normSq ζ)
      = fun ζ : ℂ => Complex.reCLM ζ * Complex.reCLM ζ + Complex.imCLM ζ * Complex.imCLM ζ := by
    funext ζ; rw [Complex.normSq_apply]; rfl
  rw [h]; fun_prop

lemma contDiff_openCut : ContDiff ℝ ∞ openCut := by
  rw [openCut_eq_fun]
  exact (Complex.ofRealCLM.contDiff).comp (contDiff_openCutReal.comp contDiff_normSq)

lemma openCut_eq_one_of_norm_le {ζ : ℂ} (h : ‖ζ‖ ≤ cutIn) : openCut ζ = 1 := by
  have hs : Complex.normSq ζ ≤ cutIn ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg ζ) h 2
  rw [openCut_eq_openCutReal, openCutReal_eq_one_of_le hs]
  norm_num

lemma openCut_eq_zero_of_le_norm {ζ : ℂ} (h : cutOut ≤ ‖ζ‖) : openCut ζ = 0 := by
  have hs : cutOut ^ 2 ≤ Complex.normSq ζ := by
    rw [Complex.normSq_eq_norm_sq]
    have hc : (0 : ℝ) ≤ cutOut := by rw [cutOut]; norm_num
    exact pow_le_pow_left₀ hc h 2
  rw [openCut_eq_openCutReal, openCutReal_eq_zero_of_le hs]
  norm_num

lemma norm_openCut_le_one (ζ : ℂ) : ‖openCut ζ‖ ≤ 1 := by
  rw [openCut_eq_openCutReal]
  have h1 : 0 ≤ openCutReal (Complex.normSq ζ) := openCutReal_nonneg _
  have h2 : openCutReal (Complex.normSq ζ) ≤ 1 := openCutReal_le_one _
  have h3 : ‖((openCutReal (Complex.normSq ζ)) : ℂ)‖ = |openCutReal (Complex.normSq ζ)| := by
    simp
  rw [h3, abs_of_nonneg h1]; exact h2

/-- The profile is locally constant `1` on `(-∞, cutIn²]`, so its derivative vanishes there. -/
lemma deriv_openCutReal_eq_zero_of_le {s : ℝ} (hs : s ≤ cutIn ^ 2) : deriv openCutReal s = 0 := by
  have hdiff : DifferentiableAt ℝ openCutReal s :=
    (contDiff_openCutReal.differentiable (by simp)) s
  have hu : UniqueDiffWithinAt ℝ (Iic s) s := uniqueDiffWithinAt_Iic s
  have h1 : HasDerivWithinAt openCutReal 0 (Iic s) s :=
    (hasDerivWithinAt_const s (Iic s) (1 : ℝ)).congr
      (fun x hx => openCutReal_eq_one_of_le (le_trans hx hs))
      (openCutReal_eq_one_of_le hs)
  have h2 : HasDerivWithinAt openCutReal (deriv openCutReal s) (Iic s) s :=
    hdiff.hasDerivAt.hasDerivWithinAt
  rw [← h2.derivWithin hu, h1.derivWithin hu]

/-- The profile is locally constant `0` on `[cutOut², ∞)`, so its derivative vanishes there. -/
lemma deriv_openCutReal_eq_zero_of_le' {s : ℝ} (hs : cutOut ^ 2 ≤ s) : deriv openCutReal s = 0 := by
  have hdiff : DifferentiableAt ℝ openCutReal s :=
    (contDiff_openCutReal.differentiable (by simp)) s
  have hu : UniqueDiffWithinAt ℝ (Ici s) s := uniqueDiffWithinAt_Ici s
  have h1 : HasDerivWithinAt openCutReal 0 (Ici s) s :=
    (hasDerivWithinAt_const s (Ici s) (0 : ℝ)).congr
      (fun x hx => openCutReal_eq_zero_of_le (le_trans hs hx))
      (openCutReal_eq_zero_of_le hs)
  have h2 : HasDerivWithinAt openCutReal (deriv openCutReal s) (Ici s) s :=
    hdiff.hasDerivAt.hasDerivWithinAt
  rw [← h2.derivWithin hu, h1.derivWithin hu]

lemma hasCompactSupport_openCut : HasCompactSupport openCut := by
  refine HasCompactSupport.intro (K := Metric.closedBall (0 : ℂ) cutOut)
    (isCompact_closedBall (0 : ℂ) cutOut) ?_
  intro x hx
  have hx' : cutOut ≤ ‖x‖ := by
    by_contra h
    exact hx (by rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_lt (not_le.mp h))
  exact openCut_eq_zero_of_le_norm hx'

end Work.CR.Flat.Cauchy
