import Mathlib
import Submission.Work.ZeroFreeTables.tf72fK_defs

/-!
# ZeroFreeTables — differentiability of the gap functional `tf72fPhi`

The gap functional of HB Lemma 7.2 at `λ = 6/7` is the integral

  `tf72fPhi lam = ∫_0^{7/3} exp (lam t) * tf72fK t dt`

against the signed kernel `tf72fK`.  Since the interval of integration is compact
and the kernel is continuous there, differentiating under the integral sign is
legitimate and gives

  `tf72fPhi' lam = ∫_0^{7/3} t * (exp (lam t) * tf72fK t) dt`.

This is the content of `tf72fK_hasDerivAt`.

The proof is an instance of the standard parametric-integral theorem
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the
dominating constant

  `B = exp ((|lam| + 1) * (7/3)) * (7/3) * M`,

where `M` bounds `|tf72fK|` on `[0, 7/3]` (which exists because `tf72fK` is
continuous there, by `tf72fK_continuousOn`: on `[0, 7/3] ⊆ [0, 2/(6/7)]` the test
function `tf72f (6/7)` is the explicit polynomial of `tf72f_eq_poly`).
-/

open scoped Interval
open MeasureTheory

noncomputable section
namespace Work.ZeroFreeTables

/-- On `[0, 7/3] = [0, 2/(6/7)]` the test function `tf72f (6/7)` is the explicit
cubic-times-quadratic polynomial of `tf72f_eq_poly`; consequently `tf72fK` agrees
there with an everywhere continuous function. -/
private lemma tf72fK_eq_poly (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) (7/3)) :
    tf72fK t = (1 - 2 * Real.exp (-(6/7) * t)) *
      ((6/7/30 : ℝ) * (2 - (6/7) * t)^3 * (4 + 6*(6/7)*t + (6/7)^2 * t^2)) := by
  have h : (2:ℝ)/(6/7) = 7/3 := by norm_num
  unfold tf72fK
  rw [tf72f_eq_poly (6/7) (by norm_num) t (by simpa [h] using ht)]

/-- `tf72fK` is continuous on the interval of integration. -/
private lemma tf72fK_continuousOn : ContinuousOn tf72fK (Set.uIcc (0:ℝ) (7/3)) := by
  have hp : Continuous (fun t : ℝ => (1 - 2 * Real.exp (-(6/7) * t)) *
      ((6/7/30 : ℝ) * (2 - (6/7) * t)^3 * (4 + 6*(6/7)*t + (6/7)^2 * t^2))) := by fun_prop
  refine hp.continuousOn.congr ?_
  intro t ht
  have ht' : t ∈ Set.Icc (0:ℝ) (7/3) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 7/3)] at ht; exact ht
  exact tf72fK_eq_poly t ht'

/-- Differentiation under the integral sign for the gap functional `tf72fPhi`:
its derivative at `lam` is the integral of `t * exp (lam t) * tf72fK t`. -/
theorem tf72fK_hasDerivAt (lam : ℝ) :
    HasDerivAt tf72fPhi
      (∫ t in (0:ℝ)..(7/3), t * (Real.exp (lam * t) * tf72fK t)) lam := by
  have hcontK : ContinuousOn tf72fK (Set.uIcc (0:ℝ) (7/3)) := tf72fK_continuousOn
  have hcontKicc : ContinuousOn tf72fK (Set.Icc (0:ℝ) (7/3)) := by
    simpa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 7/3)] using hcontK
  -- a uniform bound `M'` for `|tf72fK|` on `[0, 7/3]`
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0:ℝ)) (b := (7/3))).exists_bound_of_continuousOn
    hcontKicc
  set M' : ℝ := max M 0 with hM'def
  have hMK : ∀ t ∈ Set.Icc (0:ℝ) (7/3), ‖tf72fK t‖ ≤ M' :=
    fun t ht => (hM t ht).trans (le_max_left _ _)
  set B : ℝ := Real.exp ((|lam| + 1) * (7/3)) * (7/3) * M' with hBdef
  -- continuity of the integrand and of its `lam`-derivative
  have hcontF : ∀ x : ℝ,
      ContinuousOn (fun t : ℝ => Real.exp (x*t) * tf72fK t) (Set.uIcc (0:ℝ) (7/3)) :=
    fun x => ((by fun_prop : Continuous fun t : ℝ => Real.exp (x*t)).continuousOn).mul hcontK
  have hcontF' : ContinuousOn (fun t : ℝ => t * (Real.exp (lam*t) * tf72fK t))
      (Set.uIcc (0:ℝ) (7/3)) :=
    continuous_id.continuousOn.mul (hcontF lam)
  have hmeas1 : ∀ᶠ x in nhds lam, AEStronglyMeasurable (fun t : ℝ => Real.exp (x*t) * tf72fK t)
      (volume.restrict (Ι (0:ℝ) (7/3))) :=
    Filter.Eventually.of_forall fun x =>
      ((hcontF x).mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  have hint1 : IntervalIntegrable (fun t : ℝ => Real.exp (lam*t) * tf72fK t) volume 0 (7/3) :=
    (hcontF lam).intervalIntegrable
  have hmeas2 : AEStronglyMeasurable (fun t : ℝ => t * (Real.exp (lam*t) * tf72fK t))
      (volume.restrict (Ι (0:ℝ) (7/3))) :=
    (hcontF'.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  -- the dominating bound: for `t ∈ (0, 7/3]` and `|x| ≤ |lam| + 1`,
  -- `|t * exp (x t) * tf72fK t| ≤ exp ((|lam|+1) * 7/3) * (7/3) * M'`
  have hbound : ∀ᵐ t ∂volume, t ∈ Ι (0:ℝ) (7/3) → ∀ x ∈ Metric.ball lam 1,
      ‖t * (Real.exp (x*t) * tf72fK t)‖ ≤ B := by
    filter_upwards with t ht x hx
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 7/3)] at ht
    obtain ⟨ht0, ht1⟩ := ht
    have hx1 : |x - lam| < 1 := by
      rw [Metric.mem_ball, Real.dist_eq] at hx; exact hx
    have hxn : |x| ≤ |lam| + 1 := by
      have h1 : |x| ≤ |x - lam| + |lam| := by
        have h := abs_add_le (x - lam) lam
        simpa [sub_add_cancel] using h
      linarith
    have htabs : |t| ≤ 7/3 := by rw [abs_of_pos ht0]; exact ht1
    have hxt : x * t ≤ (|lam| + 1) * (7/3) := by
      calc x*t ≤ |x*t| := le_abs_self _
        _ = |x| * |t| := abs_mul x t
        _ ≤ (|lam|+1) * (7/3) := mul_le_mul hxn htabs (abs_nonneg t) (by positivity)
    have hexp : Real.exp (x*t) ≤ Real.exp ((|lam|+1) * (7/3)) := Real.exp_le_exp.mpr hxt
    have hKabs : |tf72fK t| ≤ M' := by
      simpa [Real.norm_eq_abs] using hMK t ⟨ht0.le, ht1⟩
    have hnorm : ‖t * (Real.exp (x*t) * tf72fK t)‖ = |t| * Real.exp (x*t) * |tf72fK t| := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
      ring
    rw [hnorm]
    have h1 : |t| * Real.exp (x*t) ≤ (7/3) * Real.exp ((|lam|+1) * (7/3)) :=
      mul_le_mul htabs hexp (Real.exp_pos _).le (by norm_num)
    have h2 : |t| * Real.exp (x*t) * |tf72fK t| ≤ (7/3) * Real.exp ((|lam|+1) * (7/3)) * M' :=
      mul_le_mul h1 hKabs (abs_nonneg _) (by positivity)
    rw [hBdef]
    linarith [h2]
  -- the derivative of `x ↦ exp (x t) * tf72fK t` at every `x`
  have hdiff : ∀ᵐ t ∂volume, t ∈ Ι (0:ℝ) (7/3) → ∀ x ∈ Metric.ball lam 1,
      HasDerivAt (fun x : ℝ => Real.exp (x*t) * tf72fK t)
        (t * (Real.exp (x*t) * tf72fK t)) x := by
    filter_upwards with t ht x hx
    have h1 : HasDerivAt (fun y : ℝ => y * t) t x := by
      simpa using (hasDerivAt_id x).mul_const t
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (y*t)) (Real.exp (x*t) * t) x := h1.exp
    refine (h2.mul_const (tf72fK t)).congr_deriv ?_
    ring
  -- Differentiate under the integral sign.  The result is stated with an explicit
  -- expected type so that the type class instances in the conclusion are the
  -- canonical ones of `ℝ` (matching the statement of this theorem).
  have key : HasDerivAt
      (fun x : ℝ => ∫ t in (0:ℝ)..(7/3), Real.exp (x*t) * tf72fK t)
      (∫ t in (0:ℝ)..(7/3), t * (Real.exp (lam*t) * tf72fK t)) lam :=
    (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun x t => Real.exp (x*t) * tf72fK t)
      (F' := fun x t => t * (Real.exp (x*t) * tf72fK t))
      (x₀ := lam) (s := Metric.ball lam 1) (bound := fun _ => B) (a := (0:ℝ)) (b := (7/3))
      (𝕜 := ℝ) (μ := volume) (E := ℝ)
      (Metric.ball_mem_nhds lam one_pos) hmeas1 hint1 hmeas2 hbound intervalIntegrable_const
      hdiff).2
  have hfun : (fun x : ℝ => ∫ t in (0:ℝ)..(7/3), Real.exp (x*t) * tf72fK t) = tf72fPhi := rfl
  rw [hfun] at key
  exact key

end Work.ZeroFreeTables
