import Mathlib
import Submission.Work.Asymptotics.F2LayerDefs

namespace Work.Asymptotics

open scoped Topology

/-!
# `psi1` is real analytic (hence `C^ω`)

The regularising factor `psi1 x = 2(1 - cos x)/x²`, extended by its integral representation
`psi1 x = 2 ∫_0^1 (1-s) cos (s x) ds`, satisfies `psi1 x = (sinc (x/2))²`.  Since `sinc` is the
divided slope `dslope sin 0` of the analytic function `sin`, it is real analytic everywhere (at
`0` because `dslope` of an analytic function is analytic, by
`HasFPowerSeriesAt.has_fpower_series_dslope_fslope`; away from `0` because there `sinc = sin/id`),
and a square of an analytic function is analytic.  Composing with the (real-linear) coercion
`ℝ → ℂ` gives the statement of the target lemma.
-/

/-- `psi1 x = (sinc (x/2))²`.  Away from `0` this is the half-angle formula
`2 - 2 cos x = 4 sin²(x/2)` combined with the defining identity `x² * psi1 x = 2 - 2 cos x`;
at `0` both sides equal `1`. -/
theorem psi1_eq_sinc_sq (x : ℝ) : psi1 x = (Real.sinc (x / 2)) ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [psi1_zero]; norm_num
  · rw [Real.sinc_of_ne_zero (div_ne_zero hx (by norm_num : (2 : ℝ) ≠ 0))]
    have hcos : Real.cos x = 2 * Real.cos (x / 2) ^ 2 - 1 := by
      have h := Real.cos_two_mul (x / 2)
      rwa [show 2 * (x / 2) = x from by ring] at h
    have hsin : Real.sin (x / 2) ^ 2 = 1 - Real.cos (x / 2) ^ 2 := by
      linarith [Real.sin_sq_add_cos_sq (x / 2)]
    have h1 : x ^ 2 * psi1 x = 4 * Real.sin (x / 2) ^ 2 := by
      rw [sq_mul_psi1, hcos, hsin]; ring
    have h2 : x ^ 2 * (Real.sin (x / 2) / (x / 2)) ^ 2 = 4 * Real.sin (x / 2) ^ 2 := by
      field_simp
      ring
    exact mul_left_cancel₀ (pow_ne_zero 2 hx) (by rw [h1, h2])

/-- The sinc function is real analytic everywhere.  At `0` this uses that `sinc` is the divided
slope of `sin` at `0` and that `dslope` preserves analyticity; away from `0` it is the quotient of
the analytic functions `sin` and `id`. -/
theorem analyticAt_sinc (y : ℝ) : AnalyticAt ℝ Real.sinc y := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [Real.sinc_eq_dslope]
    obtain ⟨p, hp⟩ := Real.analyticAt_sin (x := 0)
    exact (HasFPowerSeriesAt.has_fpower_series_dslope_fslope hp).analyticAt
  · have h : AnalyticAt ℝ (fun z : ℝ => Real.sin z / z) y :=
      Real.analyticAt_sin.div analyticAt_id hy
    refine h.congr ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using hy)] with z hz
    exact (Real.sinc_of_ne_zero hz).symm

/-- The complexified regularising factor `x ↦ ((psi1 x : ℝ) : ℂ)` is real analytic everywhere. -/
theorem analyticAt_psi1_complex (x : ℝ) :
    AnalyticAt ℝ (fun x : ℝ => ((psi1 x : ℝ) : ℂ)) x := by
  have hdiv : AnalyticAt ℝ (fun y : ℝ => y / 2) x := by
    simpa using (analyticAt_id (𝕜 := ℝ) (z := x)).div_const (c := 2)
  have hcomp : AnalyticAt ℝ (fun y : ℝ => Real.sinc (y / 2)) x :=
    AnalyticAt.comp (f := fun y : ℝ => y / 2) (x := x) (analyticAt_sinc (x / 2)) hdiv
  have hprod : AnalyticAt ℝ
      ((fun y : ℝ => Real.sinc (y / 2)) * (fun y : ℝ => Real.sinc (y / 2))) x :=
    hcomp.mul hcomp
  have hpsi : AnalyticAt ℝ psi1 x :=
    hprod.congr (Filter.Eventually.of_forall fun z => by
      show Real.sinc (z / 2) * Real.sinc (z / 2) = psi1 z
      rw [← pow_two, ← psi1_eq_sinc_sq])
  have h := AnalyticAt.comp
    (ContinuousLinearMap.analyticAt Complex.ofRealCLM (psi1 x)) hpsi
  simpa [Function.comp_def, Complex.ofRealCLM_apply] using h

theorem psi1_contDiff_omega :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (fun x : ℝ => ((Work.Asymptotics.psi1 x : ℝ) : ℂ)) := by
  refine contDiff_iff_contDiffAt.mpr (fun x => ?_)
  exact (analyticAt_psi1_complex x).contDiffAt

end Work.Asymptotics
