/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Properties of the cutoff `openCut`, at the correct smoothness level

**Warning about the smoothness index.**  In this Mathlib version `ContDiff 𝕜 n` takes
`n : ℕ∞ω = WithTop ℕ∞`, and the header of `Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
declares

* `∞ = (⊤ : ℕ∞) : ℕ∞ω`  (="`C^∞`", all finite orders), and
* `ω = ⊤ : ℕ∞ω`  (analyticity: `contDiff_omega_iff_analyticOnNhd`).

So a `C^∞` cutoff has to be stated with `∞`, *not* with `⊤`.  The statement
`Work.CR.Flat.Cauchy.openCut_props` in `Submission/Work/CR/Flat/Cauchy/openCut_props.lean`
uses `ContDiff ℝ ⊤ openCut`, i.e. it asks for *real analyticity* of `openCut`.  That
conjunct is **false** (see `not_openCut_props_aux` below): an analytic function equal to
`1` on the closed ball of radius `cutIn` would be equal to `1` everywhere, by the identity
theorem, contradicting `openCut ζ = 0` for `cutOut ≤ ‖ζ‖`.

This file proves the corrected statement, `openCut_props_infty`, which is exactly
`openCut_props` with `∞` in place of `⊤`.
-/
import Mathlib
import Submission.Work.CR.Flat.Cauchy.openCutAux

noncomputable section

open scoped NNReal ENNReal ContDiff
open MeasureTheory Set

namespace Work.CR.Flat

/-- The real differential of `Complex.normSq`: it is the real gradient `2ζ`, i.e. `2` times
the inner product with `ζ`. -/
lemma hasFDerivAt_normSq_aux (ζ : ℂ) :
    HasFDerivAt (fun w : ℂ => Complex.normSq w) (2 • innerSL ℝ ζ) ζ := by
  have h := (hasStrictFDerivAt_norm_sq ζ).hasFDerivAt
  simpa only [Complex.normSq_eq_norm_sq] using h

/-- `∂̄` of a function of `‖ζ‖²`: for `u ζ = v (‖ζ‖²)` one has `∂̄ u ζ = v'(‖ζ‖²) · ζ`,
because `∂̄ (‖ζ‖²) = ζ`. -/
lemma dbarC_comp_normSq_aux (v : ℝ → ℝ) (hv : Differentiable ℝ v) (ζ : ℂ) :
    dbarC (fun w : ℂ => (v (Complex.normSq w) : ℂ)) ζ
      = ((deriv v (Complex.normSq ζ) : ℝ) : ℂ) * ζ := by
  have hder : HasDerivAt v (deriv v (Complex.normSq ζ)) (Complex.normSq ζ) :=
    (hv (Complex.normSq ζ)).hasDerivAt
  have hcomp : HasFDerivAt (fun w : ℂ => v (Complex.normSq w))
      (deriv v (Complex.normSq ζ) • (2 • innerSL ℝ ζ)) ζ :=
    hder.comp_hasFDerivAt ζ (hasFDerivAt_normSq_aux ζ)
  have hcompC : HasFDerivAt (fun w : ℂ => (v (Complex.normSq w) : ℂ))
      (Complex.ofRealCLM.comp (deriv v (Complex.normSq ζ) • (2 • innerSL ℝ ζ))) ζ := by
    have h := Complex.ofRealCLM.hasFDerivAt.comp ζ hcomp
    convert h using 1
    funext w; rfl
  rw [dbarC, hcompC.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, smul_eq_mul, Complex.ofRealCLM_apply,
    innerSL_apply_apply, Complex.inner]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
    Complex.one_re, Complex.one_im, mul_zero, mul_one, zero_sub, sub_zero, smul_eq_mul]
  set d : ℝ := deriv v (Complex.normSq ζ) with hd
  conv_rhs => rw [← Complex.re_add_im ζ]
  push_cast
  ring

end Work.CR.Flat

namespace Work.CR.Flat.Cauchy

open Work.CR.Flat

/-- `∂̄ openCut` in terms of the radial profile: `∂̄ openCut ζ = openCutReal'(‖ζ‖²) · ζ`. -/
lemma dbarC_openCut_eq (ζ : ℂ) :
    dbarC openCut ζ = ((deriv openCutReal (Complex.normSq ζ) : ℝ) : ℂ) * ζ := by
  rw [openCut_eq_fun,
    dbarC_comp_normSq_aux openCutReal (contDiff_openCutReal.differentiable (by simp)) ζ]

/-- `∂̄ openCut` vanishes on `‖ζ‖ ≤ cutIn`, where `openCutReal` is constant `1`. -/
lemma dbarC_openCut_eq_zero_of_norm_le {ζ : ℂ} (h : ‖ζ‖ ≤ cutIn) : dbarC openCut ζ = 0 := by
  rw [dbarC_openCut_eq,
    deriv_openCutReal_eq_zero_of_le (s := Complex.normSq ζ) ?_, Complex.ofReal_zero, zero_mul]
  rw [Complex.normSq_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg ζ) h 2

/-- `∂̄ openCut` vanishes on `cutOut ≤ ‖ζ‖`, where `openCutReal` is constant `0`. -/
lemma dbarC_openCut_eq_zero_of_le_norm {ζ : ℂ} (h : cutOut ≤ ‖ζ‖) : dbarC openCut ζ = 0 := by
  rw [dbarC_openCut_eq,
    deriv_openCutReal_eq_zero_of_le' (s := Complex.normSq ζ) ?_, Complex.ofReal_zero, zero_mul]
  rw [Complex.normSq_eq_norm_sq]
  have hc : (0 : ℝ) ≤ cutOut := by rw [cutOut]; norm_num
  exact pow_le_pow_left₀ hc h 2

/-- `dbarC openCut` is `C^∞`: `openCut` is `C^∞`, hence so is `fderiv ℝ openCut`, and
`dbarC openCut` is a fixed linear combination of two of its evaluations. -/
lemma contDiff_dbarC_openCut_aux : ContDiff ℝ ∞ (dbarC openCut) := by
  have hff : ContDiff ℝ ∞ (fun z : ℂ => fderiv ℝ openCut z) :=
    contDiff_openCut.fderiv_right (m := ∞) (by simp)
  have h1 : ContDiff ℝ ∞ (fun z : ℂ => fderiv ℝ openCut z (1 : ℂ)) :=
    hff.clm_apply contDiff_const
  have hI : ContDiff ℝ ∞ (fun z : ℂ => fderiv ℝ openCut z Complex.I) :=
    hff.clm_apply contDiff_const
  have hsum : ContDiff ℝ ∞
      (fun z : ℂ => fderiv ℝ openCut z 1 + Complex.I * fderiv ℝ openCut z Complex.I) :=
    h1.add (contDiff_const.mul hI)
  change ContDiff ℝ ∞ (fun z : ℂ =>
    (1 / 2 : ℂ) * (fderiv ℝ openCut z 1 + Complex.I * fderiv ℝ openCut z Complex.I))
  exact contDiff_const.mul hsum

/-- `dbarC openCut` is supported in the closed ball of radius `cutOut`. -/
lemma hasCompactSupport_dbarC_openCut : HasCompactSupport (dbarC openCut) := by
  refine HasCompactSupport.intro (K := Metric.closedBall (0 : ℂ) cutOut)
    (isCompact_closedBall (0 : ℂ) cutOut) ?_
  intro x hx
  have hx' : cutOut ≤ ‖x‖ := by
    by_contra h
    exact hx (by rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_lt (not_le.mp h))
  exact dbarC_openCut_eq_zero_of_le_norm hx'

/-- `dbarC openCut` is bounded on `ℂ`. -/
theorem dbarC_openCut_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ζ : ℂ, ‖dbarC openCut ζ‖ ≤ C := by
  obtain ⟨C, hC⟩ := hasCompactSupport_dbarC_openCut.exists_bound_of_continuous
    contDiff_dbarC_openCut_aux.continuous
  exact ⟨max C 0, le_max_right _ _, fun ζ => (hC ζ).trans (le_max_left _ _)⟩

/-- `dbarC openCut` is globally Lipschitz. -/
theorem dbarC_openCut_lipschitz :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ζ ζ' : ℂ, ‖dbarC openCut ζ - dbarC openCut ζ'‖ ≤ C * ‖ζ - ζ'‖ := by
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hasCompactSupport_dbarC_openCut
    contDiff_dbarC_openCut_aux (by simp)
  refine ⟨(C : ℝ), C.coe_nonneg, fun ζ ζ' => ?_⟩
  simpa only [dist_eq_norm] using hC.dist_le_mul ζ ζ'

/-- **The corrected form of `openCut_props`**: every conjunct is as in
`Work.CR.Flat.Cauchy.openCut_props`, except that the smoothness level is the true
`C^∞` (`∞ = (⊤ : ℕ∞) : ℕ∞ω`) instead of `⊤ = ω`, which would ask for real analyticity. -/
theorem openCut_props_infty :
    ContDiff ℝ ∞ openCut ∧
    (∀ ζ : ℂ, ‖ζ‖ ≤ cutIn → openCut ζ = 1) ∧
    (∀ ζ : ℂ, cutOut ≤ ‖ζ‖ → openCut ζ = 0) ∧
    (∀ ζ : ℂ, ‖openCut ζ‖ ≤ 1) ∧
    (∀ ζ : ℂ, ‖ζ‖ ≤ cutIn → dbarC openCut ζ = 0) ∧
    (∀ ζ : ℂ, cutOut ≤ ‖ζ‖ → dbarC openCut ζ = 0) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ ζ : ℂ, ‖dbarC openCut ζ‖ ≤ C) ∧
    (∃ C : ℝ, 0 ≤ C ∧
      ∀ ζ ζ' : ℂ, ‖dbarC openCut ζ - dbarC openCut ζ'‖ ≤ C * ‖ζ - ζ'‖) :=
  ⟨contDiff_openCut,
   fun _ h => openCut_eq_one_of_norm_le h,
   fun _ h => openCut_eq_zero_of_le_norm h,
   norm_openCut_le_one,
   fun _ h => dbarC_openCut_eq_zero_of_norm_le h,
   fun _ h => dbarC_openCut_eq_zero_of_le_norm h,
   dbarC_openCut_bounded,
   dbarC_openCut_lipschitz⟩

/-- **The conjunction `openCut_props` is contradictory.**  Its first conjunct
`ContDiff ℝ ⊤ openCut` says (since `⊤ = ω`) that `openCut` is real-analytic on `ℂ`; combined
with `openCut = 1` on `‖ζ‖ ≤ cutIn` and `openCut = 0` for `cutOut ≤ ‖ζ‖` this is impossible:
by the identity theorem (`AnalyticOnNhd.eq_of_eventuallyEq`) an analytic function equal to `1`
near `0` is equal to `1` everywhere, but it must vanish at `ζ = 2`, where `‖2‖ = 2 ≥ cutOut`.

This is stated for the first three conjuncts only, so it also shows that *no* definition of
`openCut` can satisfy the requested statement: the three conjuncts are mutually inconsistent. -/
theorem not_openCut_props_aux
    (hcont : ContDiff ℝ ⊤ openCut)
    (h1 : ∀ ζ : ℂ, ‖ζ‖ ≤ cutIn → openCut ζ = 1)
    (h0 : ∀ ζ : ℂ, cutOut ≤ ‖ζ‖ → openCut ζ = 0) : False := by
  have hA : AnalyticOnNhd ℝ openCut univ := hcont.analyticOnNhd
  have hconst : openCut = fun _ : ℂ => 1 := by
    refine AnalyticOnNhd.eq_of_eventuallyEq (z₀ := 0) hA analyticOnNhd_const ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) cutIn_pos] with z hz
    refine h1 z ?_
    have hz' : ‖z - 0‖ < cutIn := by simpa [Metric.mem_ball] using hz
    simpa using hz'.le
  have h2 : openCut (2 : ℂ) = 0 := by
    apply h0
    rw [cutOut]
    norm_num
  have h3 : openCut (2 : ℂ) = 1 := congr_fun hconst 2
  rw [h2] at h3
  exact zero_ne_one h3

/-- The precise refutation: the first three conjuncts of `openCut_props` are contradictory,
so the conjunction asked for in `openCut_props` is false. -/
theorem not_openCut_props :
    ¬ (ContDiff ℝ ⊤ openCut ∧
        (∀ ζ : ℂ, ‖ζ‖ ≤ cutIn → openCut ζ = 1) ∧
        (∀ ζ : ℂ, cutOut ≤ ‖ζ‖ → openCut ζ = 0)) := by
  rintro ⟨hcont, h1, h0⟩
  exact not_openCut_props_aux hcont h1 h0

end Work.CR.Flat.Cauchy
