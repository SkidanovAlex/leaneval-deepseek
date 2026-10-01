/-
# Basic facts about Heath-Brown's extremal function `extCosF θ λ`

`Commons.NumberTheory.Linnik.extCosF θ lam` (defined in
`Submission/Work/NumberTheory/Linnik/scratch_l71cond.lean`) is Heath-Brown Lemma 7.1's extremal
function: it equals the closed form

  `λ(1+tan²θ)[λ(1+tan²θ)(γ - x/2)cos ζx + λ(2γ - x) + sin(2θ-ζx)/sin 2θ - 2(1 + sin(θ-ζx)/sin θ)]`

on `0 ≤ x ≤ 2γ` (`ζ = λ tan θ`, `γ = θ/ζ`) and vanishes for `x ≥ 2γ`.  This file collects the
elementary consequences that the Deuring–Heilbronn package needs: equality with the closed form,
positivity at `0`, non-negativity on `[0,∞)`, continuity on `[0,∞)`, `C²`-regularity and a bound
for the second derivative on the open support, the identity of Heath-Brown Lemma 7.5 (with `k = 2`)
and the resulting `κ`-bound.
-/
import Mathlib
import Submission.Work.NumberTheory.Linnik.scratch_l71cond
import Submission.Work.NumberTheory.Linnik.scratch_l75

open Real MeasureTheory intervalIntegral Set Filter
open scoped Real Topology

namespace Work.LinnikAreas.DhRepel

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-- `ζ = λ tan θ`. -/
def zetaF (θ lam : ℝ) : ℝ := lam * Real.tan θ

/-- `γ = θ/ζ = θ/(λ tan θ)`. -/
def gammaF (θ lam : ℝ) : ℝ := θ / (lam * Real.tan θ)

/-- The closed form of Heath-Brown Lemma 7.1 (out of which `extCosF` is cut). -/
def closedForm (θ lam x : ℝ) : ℝ :=
  lam * (1 + Real.tan θ ^ 2) *
    (lam * (1 + Real.tan θ ^ 2) * (gammaF θ lam - x / 2) * Real.cos (zetaF θ lam * x)
      + lam * (2 * gammaF θ lam - x)
      + Real.sin (2 * θ - zetaF θ lam * x) / Real.sin (2 * θ)
      - 2 * (1 + Real.sin (θ - zetaF θ lam * x) / Real.sin θ))

variable {θ lam : ℝ}

lemma sinTheta_pos (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) : 0 < Real.sin θ :=
  Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])

lemma cosTheta_pos (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) : 0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩

lemma tanTheta_pos (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) : 0 < Real.tan θ :=
  Real.tan_pos_of_pos_of_lt_pi_div_two hθ0 hθ1

lemma zetaF_pos (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) : 0 < zetaF θ lam := by
  rw [zetaF]
  exact mul_pos hlam (tanTheta_pos hθ0 hθ1)

lemma gammaF_pos (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) : 0 < gammaF θ lam := by
  rw [gammaF]
  exact div_pos hθ0 (by rw [← zetaF]; exact zetaF_pos hθ0 hθ1 hlam)

lemma sinTwoTheta_pos (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)

theorem continuous_closedForm (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    Continuous (closedForm θ lam) := by
  have hS : Real.sin θ ≠ 0 := ne_of_gt (sinTheta_pos hθ0 hθ1)
  have hS2 : Real.sin (2 * θ) ≠ 0 := ne_of_gt (sinTwoTheta_pos hθ0 hθ1)
  unfold closedForm
  fun_prop

theorem contDiff_closedForm (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    ContDiff ℝ 2 (closedForm θ lam) := by
  have hS : Real.sin θ ≠ 0 := ne_of_gt (sinTheta_pos hθ0 hθ1)
  have hS2 : Real.sin (2 * θ) ≠ 0 := ne_of_gt (sinTwoTheta_pos hθ0 hθ1)
  unfold closedForm
  fun_prop

/-- `extCosF` agrees with the closed form on `[0, 2γ]`. -/
theorem extCosF_eq_closedForm (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam)
    {x : ℝ} (hx : x ∈ Set.Icc 0 (2 * gammaF θ lam)) :
    Commons.NumberTheory.Linnik.extCosF θ lam x = closedForm θ lam x := by
  obtain ⟨h0, h2⟩ := hx
  rw [Commons.NumberTheory.Linnik.extCosF, if_pos ⟨h0, by simpa only [gammaF] using h2⟩]
  simp only [closedForm, gammaF, zetaF]

/-- The closed form vanishes at `2γ`. -/
theorem closedForm_two_gamma (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    closedForm θ lam (2 * gammaF θ lam) = 0 := by
  have hS : Real.sin θ ≠ 0 := ne_of_gt (sinTheta_pos hθ0 hθ1)
  have hT : Real.tan θ ≠ 0 := ne_of_gt (tanTheta_pos hθ0 hθ1)
  have hzg : zetaF θ lam * (2 * gammaF θ lam) = 2 * θ := by
    rw [zetaF, gammaF]
    field_simp
  have h3 : Real.sin (2 * θ - zetaF θ lam * (2 * gammaF θ lam)) = 0 := by
    rw [hzg, sub_self, Real.sin_zero]
  have h4 : Real.sin (θ - zetaF θ lam * (2 * gammaF θ lam)) = -Real.sin θ := by
    rw [hzg, show θ - 2 * θ = -θ by ring, Real.sin_neg]
  rw [closedForm, h3, h4]
  simp [hS]

/-- `extCosF` vanishes for `t ≥ 2γ`. -/
theorem extCosF_eq_zero_of_ge (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam)
    {t : ℝ} (ht : 2 * gammaF θ lam ≤ t) : Commons.NumberTheory.Linnik.extCosF θ lam t = 0 := by
  by_cases h : 0 ≤ t ∧ t ≤ 2 * (θ / (lam * Real.tan θ))
  · have hte : t = 2 * gammaF θ lam :=
      le_antisymm (by simpa only [gammaF] using h.2) ht
    have hmem : (2 * gammaF θ lam) ∈ Set.Icc 0 (2 * gammaF θ lam) :=
      ⟨by have := gammaF_pos hθ0 hθ1 hlam; linarith, le_refl _⟩
    rw [hte, extCosF_eq_closedForm hθ0 hθ1 hlam hmem]
    exact closedForm_two_gamma hθ0 hθ1 hlam
  · rw [Commons.NumberTheory.Linnik.extCosF, if_neg h]

/-- `extCosF ≥ 0` on `[0,∞)`. -/
theorem extCosF_nonneg_of_nonneg (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Commons.NumberTheory.Linnik.extCosF θ lam t := by
  by_cases h : t ≤ 2 * gammaF θ lam
  · exact Commons.NumberTheory.Linnik.extCosF_nonneg hθ0 hθ1 hlam
      ⟨ht, by simpa only [gammaF] using h⟩
  · rw [extCosF_eq_zero_of_ge hθ0 hθ1 hlam (le_of_lt (not_le.mp h))]

/-- `extCosF` is continuous on `[0,∞)`. -/
theorem continuousOn_extCosF (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    ContinuousOn (Commons.NumberTheory.Linnik.extCosF θ lam) (Set.Ici 0) := by
  have hγ : 0 < gammaF θ lam := gammaF_pos hθ0 hθ1 hlam
  have h1 : ContinuousOn (Commons.NumberTheory.Linnik.extCosF θ lam)
      (Set.Icc 0 (2 * gammaF θ lam)) :=
    ContinuousOn.congr ((continuous_closedForm hθ0 hθ1 hlam).continuousOn)
      (fun x hx => extCosF_eq_closedForm hθ0 hθ1 hlam hx)
  have h2 : ContinuousOn (Commons.NumberTheory.Linnik.extCosF θ lam)
      (Set.Ici (2 * gammaF θ lam)) :=
    ContinuousOn.congr continuousOn_const
      (fun x hx => extCosF_eq_zero_of_ge hθ0 hθ1 hlam hx)
  have hunion : Set.Icc 0 (2 * gammaF θ lam) ∪ Set.Ici (2 * gammaF θ lam) = Set.Ici 0 := by
    ext x
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ici]
    constructor
    · rintro (⟨h, _⟩ | h) <;> linarith
    · intro h
      by_cases hx : x ≤ 2 * gammaF θ lam
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr (le_of_lt (not_le.mp hx))
  rw [← hunion]
  exact (continuousOn_union_iff_of_isClosed isClosed_Icc isClosed_Ici).mpr ⟨h1, h2⟩

/-- `t ↦ (extCosF θ λ t : ℂ)` is `C²` on the open support. -/
theorem contDiffOn_extCosF (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    ContDiffOn ℝ 2 (fun t : ℝ => ((Commons.NumberTheory.Linnik.extCosF θ lam t : ℝ) : ℂ))
      (Set.Ioo 0 (2 * gammaF θ lam)) := by
  have hmem : ∀ x ∈ Set.Ioo (0:ℝ) (2 * gammaF θ lam),
      x ∈ Set.Icc 0 (2 * gammaF θ lam) := fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hφ : ContDiff ℝ 2 (fun t : ℝ => ((closedForm θ lam t : ℝ) : ℂ)) :=
    (ContinuousLinearMap.contDiff Complex.ofRealCLM).comp (contDiff_closedForm hθ0 hθ1 hlam)
  refine hφ.contDiffOn.congr (fun x hx => ?_)
  show ((Commons.NumberTheory.Linnik.extCosF θ lam x : ℝ) : ℂ) = _
  rw [extCosF_eq_closedForm hθ0 hθ1 hlam (hmem x hx)]

/-- A bound for the second derivative of `t ↦ (extCosF θ λ t : ℂ)` on the open support. -/
theorem exists_iteratedDeriv_two_bound_extCosF (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hlam : 0 < lam) :
    ∃ B : ℝ, ∀ t ∈ Set.Ioo (0:ℝ) (2 * gammaF θ lam),
      ‖iteratedDeriv 2 (fun t : ℝ => ((Commons.NumberTheory.Linnik.extCosF θ lam t : ℝ) : ℂ)) t‖ ≤ B := by
  have hφdiff : ContDiff ℝ 2 (fun t : ℝ => ((closedForm θ lam t : ℝ) : ℂ)) :=
    (ContinuousLinearMap.contDiff Complex.ofRealCLM).comp (contDiff_closedForm hθ0 hθ1 hlam)
  obtain ⟨B, hB⟩ :=
    (isCompact_Icc (a := (0:ℝ)) (b := 2 * gammaF θ lam)).exists_bound_of_continuousOn
      (hφdiff.continuous_iteratedDeriv 2 (by norm_num)).continuousOn
  refine ⟨B, ?_⟩
  intro t ht
  have hEq : (fun s : ℝ => ((Commons.NumberTheory.Linnik.extCosF θ lam s : ℝ) : ℂ))
      =ᶠ[𝓝 t] (fun s : ℝ => ((closedForm θ lam s : ℝ) : ℂ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    rw [extCosF_eq_closedForm hθ0 hθ1 hlam ⟨le_of_lt hs.1, le_of_lt hs.2⟩]
  have hEq2 : iteratedDeriv 2
        (fun s : ℝ => ((Commons.NumberTheory.Linnik.extCosF θ lam s : ℝ) : ℂ)) t
      = iteratedDeriv 2 (fun s : ℝ => ((closedForm θ lam s : ℝ) : ℂ)) t :=
    (Filter.EventuallyEq.iteratedDeriv hEq 2).eq_of_nhds
  rw [hEq2]
  exact hB t ⟨le_of_lt ht.1, le_of_lt ht.2⟩

/-- The value of the closed form at `0` (Heath-Brown Lemma 7.1). -/
theorem closedForm_zero (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    closedForm θ lam 0 =
      lam * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ * (Real.cos θ / Real.sin θ) - 3) := by
  have h := (Commons.Analysis.Integral.extremal_cosine_integral hθ0 hθ1 hlam).1
  simpa only [closedForm, gammaF, zetaF] using h

/-- The integral of the closed form over one support (Heath-Brown Lemma 7.1). -/
theorem integral_closedForm (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    (∫ x in (0:ℝ)..(2 * gammaF θ lam), closedForm θ lam x)
      = 2 * (1 + Real.tan θ ^ 2) * (1 - θ * (Real.cos θ / Real.sin θ)) ^ 2 := by
  have h := (Commons.Analysis.Integral.extremal_cosine_integral hθ0 hθ1 hlam).2.1
  simpa only [closedForm, gammaF, zetaF] using h

/-- The weighted integral of the closed form (Heath-Brown Lemma 7.1). -/
theorem integral_exp_closedForm (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    (∫ x in (0:ℝ)..(2 * gammaF θ lam), Real.exp (lam * x) * closedForm θ lam x)
      = 2 * Real.tan θ ^ 2 + 3 - 3 * θ * Real.tan θ - 3 * θ * (Real.cos θ / Real.sin θ) := by
  have h := (Commons.Analysis.Integral.extremal_cosine_integral hθ0 hθ1 hlam).2.2
  simpa only [closedForm, gammaF, zetaF] using h

/-- `extCosF θ λ 0 > 0` for the special `θ` with `sin²θ = 2(1 - θ cot θ)` (which forces
`θ > 3/4`). -/
theorem extCosF_zero_pos (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam)
    (hθ34 : 3 / 4 < θ) (heq : Real.sin θ ^ 2 = 2 * (1 - θ * (Real.cos θ / Real.sin θ))) :
    0 < Commons.NumberTheory.Linnik.extCosF θ lam 0 := by
  have hγ := gammaF_pos hθ0 hθ1 hlam
  have hmem : (0:ℝ) ∈ Set.Icc 0 (2 * gammaF θ lam) := ⟨le_refl 0, by linarith⟩
  rw [extCosF_eq_closedForm hθ0 hθ1 hlam hmem, closedForm_zero hθ0 hθ1 hlam]
  have hS := sinTheta_pos hθ0 hθ1
  have hC := cosTheta_pos hθ0 hθ1
  have hU : θ * (Real.cos θ / Real.sin θ) = 1 - Real.sin θ ^ 2 / 2 := by linarith [heq]
  have hbracket : 0 < θ * Real.tan θ + 3 * θ * (Real.cos θ / Real.sin θ) - 3 := by
    have hsin2le : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hkey : θ * Real.tan θ + 3 * θ * (Real.cos θ / Real.sin θ) - 3
        = Real.sin θ * (θ - 3 / 4 * Real.sin (2 * θ)) / Real.cos θ := by
      rw [Real.tan_eq_sin_div_cos]
      rw [show 3 * θ * (Real.cos θ / Real.sin θ)
            = 3 * (θ * (Real.cos θ / Real.sin θ)) by ring, hU, Real.sin_two_mul]
      field_simp
      ring
    rw [hkey]
    exact div_pos (mul_pos hS (by nlinarith [hsin2le, hθ34])) hC
  exact mul_pos (mul_pos hlam (by positivity)) hbracket

/-- **Heath-Brown Lemma 7.5 with `k = 2`** for the extremal function `extCosF`. -/
theorem extCosF_laplace_identity (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam)
    (heq : Real.sin θ ^ 2 = 2 * (1 - θ * (Real.cos θ / Real.sin θ))) :
    (∫ t in (0:ℝ)..(2 * gammaF θ lam),
        Real.exp (lam * t) * Commons.NumberTheory.Linnik.extCosF θ lam t)
      - 2 * (∫ t in (0:ℝ)..(2 * gammaF θ lam), Commons.NumberTheory.Linnik.extCosF θ lam t)
      = -(1 / lam) * Commons.NumberTheory.Linnik.extCosF θ lam 0 * Real.cos θ ^ 2 := by
  have hγ : 0 ≤ 2 * gammaF θ lam := by have := gammaF_pos hθ0 hθ1 hlam; linarith
  -- the identity of Heath-Brown Lemma 7.5, transported to the closed form
  have hclosed : (∫ x in (0:ℝ)..(2 * gammaF θ lam),
        Real.exp (lam * x) * closedForm θ lam x)
      - 2 * (∫ x in (0:ℝ)..(2 * gammaF θ lam), closedForm θ lam x)
      = -(1 / lam) * closedForm θ lam 0 * Real.cos θ ^ 2 := by
    have h := Commons.NumberTheory.Linnik.extremal_cosine_lemma75 (θ := θ) (lam := lam) (k := 2)
      hθ0 hθ1 (by norm_num) (by norm_num) hlam heq
    simpa only [closedForm, gammaF, zetaF, one_div] using h
  have hI1 : (∫ t in (0:ℝ)..(2 * gammaF θ lam),
        Real.exp (lam * t) * Commons.NumberTheory.Linnik.extCosF θ lam t)
      = ∫ t in (0:ℝ)..(2 * gammaF θ lam), Real.exp (lam * t) * closedForm θ lam t := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hγ] at hx
    show Real.exp (lam * x) * Commons.NumberTheory.Linnik.extCosF θ lam x
      = Real.exp (lam * x) * closedForm θ lam x
    rw [extCosF_eq_closedForm hθ0 hθ1 hlam hx]
  have hI2 : (∫ t in (0:ℝ)..(2 * gammaF θ lam), Commons.NumberTheory.Linnik.extCosF θ lam t)
      = ∫ t in (0:ℝ)..(2 * gammaF θ lam), closedForm θ lam t := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hγ] at hx
    exact extCosF_eq_closedForm hθ0 hθ1 hlam hx
  have h0 : Commons.NumberTheory.Linnik.extCosF θ lam 0 = closedForm θ lam 0 :=
    extCosF_eq_closedForm hθ0 hθ1 hlam ⟨le_refl 0, hγ⟩
  rw [hI1, hI2, h0]
  exact hclosed

/-- **The `κ`-bound**: from the five-term inequality of Heath-Brown Lemma 8.5 the parameter `λ₂`
is bounded below by `cos²θ/A`. -/
theorem cos_sq_le_of_five_term {lam1 lam2 A : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (heq : Real.sin θ ^ 2 = 2 * (1 - θ * (Real.cos θ / Real.sin θ)))
    (hlam2 : 0 < lam2) (hlam1 : 0 ≤ lam1) (h12 : lam1 ≤ lam2)
    (hf0 : 0 < Commons.NumberTheory.Linnik.extCosF θ lam2 0)
    (hineq : 0 ≤
        (∫ t in (0:ℝ)..(2 * gammaF θ lam2),
            Real.exp (lam2 * t) * Commons.NumberTheory.Linnik.extCosF θ lam2 t)
        - (∫ t in (0:ℝ)..(2 * gammaF θ lam2),
            Real.exp ((lam2 - lam1) * t) * Commons.NumberTheory.Linnik.extCosF θ lam2 t)
        - (∫ t in (0:ℝ)..(2 * gammaF θ lam2), Commons.NumberTheory.Linnik.extCosF θ lam2 t)
        + Commons.NumberTheory.Linnik.extCosF θ lam2 0 * A) :
    Real.cos θ ^ 2 ≤ lam2 * A := by
  have hγ : 0 ≤ 2 * gammaF θ lam2 := by have := gammaF_pos hθ0 hθ1 hlam2; linarith
  have hid := extCosF_laplace_identity (θ := θ) (lam := lam2) hθ0 hθ1 hlam2 heq
  have hcont : ContinuousOn (fun t : ℝ => Commons.NumberTheory.Linnik.extCosF θ lam2 t)
      (Set.uIcc (0:ℝ) (2 * gammaF θ lam2)) :=
    (continuousOn_extCosF hθ0 hθ1 hlam2).mono (fun x hx => by
      rw [Set.uIcc_of_le hγ] at hx; exact hx.1)
  have hcont2 : ContinuousOn
      (fun t : ℝ => Real.exp ((lam2 - lam1) * t) * Commons.NumberTheory.Linnik.extCosF θ lam2 t)
      (Set.uIcc (0:ℝ) (2 * gammaF θ lam2)) :=
    ((by fun_prop : ContinuousOn (fun t : ℝ => Real.exp ((lam2 - lam1) * t))
        (Set.uIcc (0:ℝ) (2 * gammaF θ lam2)))).mul hcont
  have hint1 : IntervalIntegrable (fun t : ℝ => Commons.NumberTheory.Linnik.extCosF θ lam2 t)
      volume (0:ℝ) (2 * gammaF θ lam2) := hcont.intervalIntegrable
  have hint2 : IntervalIntegrable
      (fun t : ℝ => Real.exp ((lam2 - lam1) * t) * Commons.NumberTheory.Linnik.extCosF θ lam2 t)
      volume (0:ℝ) (2 * gammaF θ lam2) := hcont2.intervalIntegrable
  have hpt : ∀ t ∈ Set.Icc (0:ℝ) (2 * gammaF θ lam2),
      Commons.NumberTheory.Linnik.extCosF θ lam2 t
        ≤ Real.exp ((lam2 - lam1) * t) * Commons.NumberTheory.Linnik.extCosF θ lam2 t := by
    intro t ht
    have hf : 0 ≤ Commons.NumberTheory.Linnik.extCosF θ lam2 t :=
      extCosF_nonneg_of_nonneg hθ0 hθ1 hlam2 ht.1
    have hexp : 1 ≤ Real.exp ((lam2 - lam1) * t) := Real.one_le_exp (by nlinarith [ht.1])
    calc Commons.NumberTheory.Linnik.extCosF θ lam2 t
        = 1 * Commons.NumberTheory.Linnik.extCosF θ lam2 t := by ring
      _ ≤ Real.exp ((lam2 - lam1) * t) * Commons.NumberTheory.Linnik.extCosF θ lam2 t :=
          mul_le_mul_of_nonneg_right hexp hf
  have hmono : (∫ t in (0:ℝ)..(2 * gammaF θ lam2),
        Commons.NumberTheory.Linnik.extCosF θ lam2 t)
      - (∫ t in (0:ℝ)..(2 * gammaF θ lam2),
          Real.exp ((lam2 - lam1) * t) * Commons.NumberTheory.Linnik.extCosF θ lam2 t) ≤ 0 := by
    have := intervalIntegral.integral_mono_on hγ hint1 hint2 hpt
    linarith
  have hid' : (∫ t in (0:ℝ)..(2 * gammaF θ lam2),
        Real.exp (lam2 * t) * Commons.NumberTheory.Linnik.extCosF θ lam2 t)
      - 2 * (∫ t in (0:ℝ)..(2 * gammaF θ lam2),
          Commons.NumberTheory.Linnik.extCosF θ lam2 t)
      + (1 / lam2) * (Commons.NumberTheory.Linnik.extCosF θ lam2 0 * Real.cos θ ^ 2) = 0 := by
    linarith [hid]
  have hsub : 0 ≤ (∫ t in (0:ℝ)..(2 * gammaF θ lam2),
        Commons.NumberTheory.Linnik.extCosF θ lam2 t)
      - (∫ t in (0:ℝ)..(2 * gammaF θ lam2),
          Real.exp ((lam2 - lam1) * t) * Commons.NumberTheory.Linnik.extCosF θ lam2 t)
      - (1 / lam2) * (Commons.NumberTheory.Linnik.extCosF θ lam2 0 * Real.cos θ ^ 2)
      + Commons.NumberTheory.Linnik.extCosF θ lam2 0 * A := by
    linarith [hineq, hid']
  have h3 : (1 / lam2) * (Commons.NumberTheory.Linnik.extCosF θ lam2 0 * Real.cos θ ^ 2)
      ≤ Commons.NumberTheory.Linnik.extCosF θ lam2 0 * A := by
    linarith [hsub, hmono]
  have h5 : Commons.NumberTheory.Linnik.extCosF θ lam2 0 * Real.cos θ ^ 2
      ≤ (Commons.NumberTheory.Linnik.extCosF θ lam2 0 * A) * lam2 := by
    have h := mul_le_mul_of_nonneg_right h3 (le_of_lt hlam2)
    have heq' : (1 / lam2) * (Commons.NumberTheory.Linnik.extCosF θ lam2 0 * Real.cos θ ^ 2)
        * lam2 = Commons.NumberTheory.Linnik.extCosF θ lam2 0 * Real.cos θ ^ 2 := by
      calc (1 / lam2) * (Commons.NumberTheory.Linnik.extCosF θ lam2 0 * Real.cos θ ^ 2) * lam2
          = (Commons.NumberTheory.Linnik.extCosF θ lam2 0 * Real.cos θ ^ 2)
            * ((1 / lam2) * lam2) := by ring
        _ = (Commons.NumberTheory.Linnik.extCosF θ lam2 0 * Real.cos θ ^ 2) * 1 := by
            rw [one_div, inv_mul_cancel₀ (ne_of_gt hlam2)]
        _ = Commons.NumberTheory.Linnik.extCosF θ lam2 0 * Real.cos θ ^ 2 := by ring
    rwa [heq'] at h
  calc Real.cos θ ^ 2
        = (Commons.NumberTheory.Linnik.extCosF θ lam2 0 * Real.cos θ ^ 2)
          / Commons.NumberTheory.Linnik.extCosF θ lam2 0 := by
          rw [eq_div_iff (ne_of_gt hf0)]
          ring
    _ ≤ ((Commons.NumberTheory.Linnik.extCosF θ lam2 0 * A) * lam2)
          / Commons.NumberTheory.Linnik.extCosF θ lam2 0 :=
          div_le_div_of_nonneg_right h5 (le_of_lt hf0)
    _ = lam2 * A := by
        rw [div_eq_iff (ne_of_gt hf0)]
        ring

end

end Work.LinnikAreas.DhRepel
