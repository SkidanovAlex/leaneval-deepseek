/-
# Bounds for the cutoff `outerCut R`

Uniform bounds (in the radius) for the derivative and the Laplace trace of the smooth cutoff
`outerCut R = radialCut (‖·‖²/R²)`, together with the interior vanishing of those derivatives and
a uniform bound for the second derivative of the profile `radialCut`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.PressureOn.Auxiliary.gradient_comp_normSq
import Submission.Work.FTS.PressureOn.PoissonAux.Defs
import Submission.Work.FTS.PressureOn.PoissonAux.exists_bound_deriv_radialCut
import Submission.Work.FTS.PressureOn.PoissonAux.exists_bound_deriv_deriv_rhoProfile
import Submission.Work.FTS.PressureOn.PoissonAux.deriv_deriv_rhoProfile_support
import Submission.Work.FTS.PressureOn.PoissonAux.laplaceTrace_cutKernel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter Topology
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.Auxiliary

noncomputable section

/-! ## The cutoff `outerCut R` -/

/-- Inside the open ball of radius `R` the cutoff `outerCut R` is locally the constant `1`, hence
its derivative vanishes there. -/
lemma fderiv_outerCut_eq_zero_of_norm_lt {R : ℝ} (hR : 0 < R) {y : R3} (hy : ‖y‖ < R) :
    fderiv ℝ (Work.FTS.PressureOn.outerCut R) y = 0 := by
  have hmem : Metric.ball (0 : R3) R ∈ 𝓝 y :=
    Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_zero_right]; exact hy)
  have hev : Work.FTS.PressureOn.outerCut R =ᶠ[𝓝 y] (fun _ : R3 => (1 : ℝ)) := by
    filter_upwards [hmem] with z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    exact Work.FTS.PressureOn.outerCut_eq_one hR hz.le
  rw [hev.fderiv_eq]
  simp

/-- Inside the open ball of radius `R` the Laplace trace of the cutoff `outerCut R` vanishes. -/
lemma laplaceTrace_outerCut_eq_zero_of_norm_lt {R : ℝ} (hR : 0 < R) {y : R3} (hy : ‖y‖ < R) :
    Work.FTS.PressureOn.laplaceTrace (Work.FTS.PressureOn.outerCut R) y = 0 := by
  have hmem : Metric.ball (0 : R3) R ∈ 𝓝 y :=
    Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_zero_right]; exact hy)
  have hfd : (fun w : R3 => fderiv ℝ (Work.FTS.PressureOn.outerCut R) w)
      =ᶠ[𝓝 y] (fun _ : R3 => 0) := by
    filter_upwards [hmem] with z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    exact fderiv_outerCut_eq_zero_of_norm_lt hR hz
  rw [Work.FTS.PressureOn.laplaceTrace]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hev : (fun w : R3 => fderiv ℝ (Work.FTS.PressureOn.outerCut R) w
      (FiniteTimeSingularity.e i)) =ᶠ[𝓝 y] (fun _ : R3 => (0 : ℝ)) := by
    filter_upwards [hfd] with z hz
    rw [hz]
    simp
  rw [hev.fderiv_eq]
  simp

/-- The second derivative of `radialCut` vanishes above `2`. -/
lemma radialCut_deriv_deriv_eq_zero_of_two_lt {t : ℝ} (ht : 2 < t) :
    deriv (deriv Work.FTS.PressureOn.radialCut) t = 0 :=
  Work.FTS.PressureOn.PoissonAux.deriv_deriv_eq_zero_of_isOpen_const isOpen_Ioi ht
    (fun s hs => Work.FTS.PressureOn.radialCut_eq_zero hs.le)

/-- The second derivative of `radialCut` is bounded on `ℝ`. -/
lemma exists_bound_deriv_deriv_radialCut :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, |deriv (deriv Work.FTS.PressureOn.radialCut) t| ≤ B := by
  have hcont : Continuous (deriv (deriv Work.FTS.PressureOn.radialCut)) := by
    have hcd : ContDiff ℝ 1 (deriv Work.FTS.PressureOn.radialCut) := by
      simpa only [Nat.reduceAdd] using (Work.FTS.PressureOn.contDiff_radialCut 2).deriv'
    exact hcd.continuous_deriv_one
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support
    (Work.FTS.PressureOn.PoissonAux.hasCompactSupport_deriv_radialCut.deriv)
  exact ⟨C, le_trans (norm_nonneg _) (hC 0), fun t => by
    rw [← Real.norm_eq_abs]; exact hC t⟩

/-- The chain rule for the rescaled profile `s ↦ radialCut (s / R ^ 2)`. -/
lemma deriv_radialCut_div (R s : ℝ) :
    deriv (fun s : ℝ => Work.FTS.PressureOn.radialCut (s / R ^ 2)) s
      = deriv Work.FTS.PressureOn.radialCut (s / R ^ 2) * (1 / R ^ 2) := by
  have h1 : HasDerivAt (fun s : ℝ => s / R ^ 2) (1 / R ^ 2) s :=
    (hasDerivAt_id s).div_const _
  have h2 : HasDerivAt Work.FTS.PressureOn.radialCut
      (deriv Work.FTS.PressureOn.radialCut (s / R ^ 2)) (s / R ^ 2) :=
    ((Work.FTS.PressureOn.contDiff_radialCut 1).differentiable one_ne_zero
      (s / R ^ 2)).hasDerivAt
  exact (h2.comp s h1).deriv

/-- **Uniform bound for the derivative of the cutoff.** -/
lemma exists_bound_fderiv_outerCut :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ R : ℝ, 1 ≤ R → ∀ y : R3,
      ‖fderiv ℝ (Work.FTS.PressureOn.outerCut R) y‖ ≤ A := by
  obtain ⟨A0, hA0nn, hA0⟩ := Work.FTS.PressureOn.PoissonAux.exists_bound_deriv_radialCut
  refine ⟨4 * A0, by positivity, fun R hR y => ?_⟩
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR
  have hR2pos : (0 : ℝ) < R ^ 2 := by positivity
  have hfd : fderiv ℝ (Work.FTS.PressureOn.outerCut R) y
      = (2 * (deriv Work.FTS.PressureOn.radialCut (‖y‖ ^ 2 / R ^ 2) * (1 / R ^ 2))) •
          innerSL ℝ y := by
    have h1 : Work.FTS.PressureOn.outerCut R
        = fun x : R3 => Work.FTS.PressureOn.radialCut (‖x‖ ^ 2 / R ^ 2) := rfl
    rw [h1, gradient_comp_normSq (fun s : ℝ => Work.FTS.PressureOn.radialCut (s / R ^ 2))
      ((Work.FTS.PressureOn.contDiff_radialCut 1).comp (contDiff_id.div_const _)) y,
      deriv_radialCut_div]
  rw [hfd, norm_smul, innerSL_apply_norm, Real.norm_eq_abs]
  by_cases hcase : ‖y‖ ^ 2 ≤ 2 * R ^ 2
  · have hynorm : ‖y‖ ≤ 2 * R := by
      have h2 : ‖y‖ ^ 2 ≤ (Real.sqrt 2 * R) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num)]
        exact hcase
      have h3 := Real.sqrt_le_sqrt h2
      rw [Real.sqrt_sq (norm_nonneg y),
        Real.sqrt_sq (by positivity : (0 : ℝ) ≤ Real.sqrt 2 * R)] at h3
      nlinarith [h3, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2, hRpos.le,
        norm_nonneg y]
    calc |2 * (deriv Work.FTS.PressureOn.radialCut (‖y‖ ^ 2 / R ^ 2) * (1 / R ^ 2))| * ‖y‖
        = (2 * (1 / R ^ 2) * |deriv Work.FTS.PressureOn.radialCut (‖y‖ ^ 2 / R ^ 2)|) * ‖y‖ := by
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
            abs_of_pos (by positivity : (0 : ℝ) < 1 / R ^ 2)]
          ring
      _ ≤ (2 * (1 / R ^ 2) * A0) * (2 * R) := by
          have hb : (2 * (1 / R ^ 2)) * |deriv Work.FTS.PressureOn.radialCut (‖y‖ ^ 2 / R ^ 2)|
              ≤ (2 * (1 / R ^ 2)) * A0 :=
            mul_le_mul_of_nonneg_left (hA0 _) (by positivity)
          exact mul_le_mul hb hynorm (norm_nonneg y) (by positivity)
      _ = 4 * A0 / R := by
          have hRne : R ≠ 0 := ne_of_gt hRpos
          field_simp
          ring
      _ ≤ 4 * A0 := by
          rw [div_le_iff₀ hRpos]
          nlinarith [hA0nn, hR]
  · push_neg at hcase
    have ht : (2 : ℝ) < ‖y‖ ^ 2 / R ^ 2 := by
      rw [lt_div_iff₀ hR2pos]
      linarith
    have hz : deriv Work.FTS.PressureOn.radialCut (‖y‖ ^ 2 / R ^ 2) = 0 := by
      rw [(Work.FTS.PressureOn.PoissonAux.eventuallyEq_zero_of_lt ht).deriv_eq]
      simp
    rw [hz]
    simp only [mul_zero, abs_zero, zero_mul]
    positivity

/-- **Uniform bound for the Laplace trace of the cutoff.** -/
lemma exists_bound_laplaceTrace_outerCut :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ R : ℝ, 1 ≤ R → ∀ y : R3,
      |Work.FTS.PressureOn.laplaceTrace (Work.FTS.PressureOn.outerCut R) y| ≤ B := by
  obtain ⟨A0, hA0nn, hA0⟩ := Work.FTS.PressureOn.PoissonAux.exists_bound_deriv_radialCut
  obtain ⟨A1, hA1nn, hA1⟩ := exists_bound_deriv_deriv_radialCut
  refine ⟨6 * A0 + 8 * A1, by positivity, fun R hR y => ?_⟩
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR
  have hR2pos : (0 : ℝ) < R ^ 2 := by positivity
  have hlt : Work.FTS.PressureOn.laplaceTrace (Work.FTS.PressureOn.outerCut R) y
      = 6 * deriv (fun s : ℝ => Work.FTS.PressureOn.radialCut (s / R ^ 2)) (‖y‖ ^ 2)
        + 4 * ‖y‖ ^ 2
            * deriv (deriv (fun s : ℝ => Work.FTS.PressureOn.radialCut (s / R ^ 2)))
                (‖y‖ ^ 2) := by
    rw [show Work.FTS.PressureOn.outerCut R
        = fun y : R3 => (fun s : ℝ => Work.FTS.PressureOn.radialCut (s / R ^ 2)) (‖y‖ ^ 2)
        from rfl]
    exact Work.FTS.PressureOn.PoissonAux.laplaceTrace_normSq _
      ((Work.FTS.PressureOn.contDiff_radialCut 2).comp (contDiff_id.div_const _)) y
  have hd1 : |deriv (fun s : ℝ => Work.FTS.PressureOn.radialCut (s / R ^ 2)) (‖y‖ ^ 2)|
      ≤ A0 / R ^ 2 := by
    have htmp : |deriv Work.FTS.PressureOn.radialCut (‖y‖ ^ 2 / R ^ 2)| * (1 / R ^ 2)
        ≤ A0 * (1 / R ^ 2) :=
      mul_le_mul_of_nonneg_right (hA0 _) (by positivity)
    rw [deriv_radialCut_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / R ^ 2)]
    simpa [div_eq_mul_inv] using htmp
  have hd2 : |deriv (deriv (fun s : ℝ => Work.FTS.PressureOn.radialCut (s / R ^ 2))) (‖y‖ ^ 2)|
      ≤ A1 / R ^ 4 := by
    rw [Work.FTS.PressureOn.PoissonAux.deriv_deriv_rescale _
        (Work.FTS.PressureOn.contDiff_radialCut 2) (R ^ 2) (‖y‖ ^ 2),
      abs_div, abs_of_pos (by positivity : (0 : ℝ) < (R ^ 2) ^ 2),
      show (R ^ 2) ^ 2 = R ^ 4 from by ring, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hA1 _) (by positivity)
  rw [hlt]
  by_cases hcase : ‖y‖ ^ 2 ≤ 2 * R ^ 2
  · have h1 : |6 * deriv (fun s : ℝ => Work.FTS.PressureOn.radialCut (s / R ^ 2)) (‖y‖ ^ 2)
        + 4 * ‖y‖ ^ 2
            * deriv (deriv (fun s : ℝ => Work.FTS.PressureOn.radialCut (s / R ^ 2))) (‖y‖ ^ 2)|
        ≤ 6 * (A0 / R ^ 2) + 4 * ‖y‖ ^ 2 * (A1 / R ^ 4) := by
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
      refine add_le_add (mul_le_mul_of_nonneg_left hd1 (by norm_num)) ?_
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * ‖y‖ ^ 2)]
      exact mul_le_mul_of_nonneg_left hd2 (by positivity)
    have h2 : 6 * (A0 / R ^ 2) + 4 * ‖y‖ ^ 2 * (A1 / R ^ 4) ≤ 6 * A0 + 8 * A1 := by
      have hA0div : 6 * (A0 / R ^ 2) ≤ 6 * A0 := by
        rw [div_eq_mul_inv]
        have h1 : (R ^ 2)⁻¹ ≤ 1 := by
          rw [inv_le_one_iff₀]
          right
          nlinarith
        nlinarith [hA0nn, h1]
      have hA1div : 4 * ‖y‖ ^ 2 * (A1 / R ^ 4) ≤ 8 * A1 := by
        have h1 : 4 * ‖y‖ ^ 2 * (A1 / R ^ 4) ≤ 4 * (2 * R ^ 2) * (A1 / R ^ 4) := by
          have h2 : (0 : ℝ) ≤ A1 / R ^ 4 := by positivity
          have h3 : 4 * ‖y‖ ^ 2 ≤ 4 * (2 * R ^ 2) := by linarith only [hcase]
          exact mul_le_mul_of_nonneg_right h3 h2
        have h2 : 4 * (2 * R ^ 2) * (A1 / R ^ 4) = 8 * A1 / R ^ 2 := by
          have hRne : R ≠ 0 := ne_of_gt hRpos
          field_simp
          ring
        rw [h2] at h1
        refine le_trans h1 ?_
        rw [div_le_iff₀ hR2pos]
        have hR2ge : (1 : ℝ) ≤ R ^ 2 := by nlinarith
        nlinarith [hA1nn, hR2ge]
      linarith
    linarith
  · push_neg at hcase
    have ht : (2 : ℝ) < ‖y‖ ^ 2 / R ^ 2 := by
      rw [lt_div_iff₀ hR2pos]
      linarith
    have hz1 : deriv (fun s : ℝ => Work.FTS.PressureOn.radialCut (s / R ^ 2)) (‖y‖ ^ 2)
        = 0 := by
      rw [deriv_radialCut_div]
      have hz : deriv Work.FTS.PressureOn.radialCut (‖y‖ ^ 2 / R ^ 2) = 0 := by
        rw [(Work.FTS.PressureOn.PoissonAux.eventuallyEq_zero_of_lt ht).deriv_eq]
        simp
      rw [hz, zero_mul]
    have hz2 : deriv (deriv (fun s : ℝ => Work.FTS.PressureOn.radialCut (s / R ^ 2)))
        (‖y‖ ^ 2) = 0 := by
      rw [Work.FTS.PressureOn.PoissonAux.deriv_deriv_rescale _
        (Work.FTS.PressureOn.contDiff_radialCut 2) (R ^ 2) (‖y‖ ^ 2),
        radialCut_deriv_deriv_eq_zero_of_two_lt ht, zero_div]
    rw [hz1, hz2]
    simp only [mul_zero, add_zero, abs_zero]
    positivity

end

end Work.FTS.PressureOn.Auxiliary
