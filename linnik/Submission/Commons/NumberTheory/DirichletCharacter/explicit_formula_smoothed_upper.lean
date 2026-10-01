import Mathlib
import Submission.Commons.NumberTheory.Linnik.tentMellin_bridge_scale
import Submission.Commons.NumberTheory.DirichletCharacter.rectInt_logDeriv_completed_tentF_eq
import Submission.Commons.NumberTheory.DirichletCharacter.rectInt_logDeriv_gammaFactor_mul_eq
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_le
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt
import Submission.Commons.Analysis.Complex.laplace_transform_bound_complex
import Submission.Commons.Analysis.Complex.laplace_transform_integral_eq
import Submission.Commons.Analysis.Complex.rectInt_tendsto_vertical_gen
import Submission.Commons.Analysis.Integral.norm_intervalIntegral_mul_le_gen
import Submission.Commons.NumberTheory.DirichletCharacter.divisorSum_summable_and_tendsto
import Submission.Commons.NumberTheory.DirichletCharacter.norm_logDeriv_LFunction_le_re_gt_one
import Submission.Commons.NumberTheory.DirichletCharacter.smoothed_vonMangoldt_eq_line
import Submission.Commons.NumberTheory.DirichletCharacter.norm_integral_logDeriv_L_lefthalf_le
import Submission.Commons.NumberTheory.DirichletCharacter.completedL_shift_identity_gen
import Submission.Commons.NumberTheory.DirichletCharacter.gammaFactor_shift_identity_gen
import Submission.Commons.NumberTheory.DirichletCharacter.logDeriv_completedLFunction_one_sub
import Submission.Commons.NumberTheory.DirichletCharacter.horizontal_logDeriv_completedL_tendsto_gen
import Submission.Commons.NumberTheory.DirichletCharacter.horizontal_logDeriv_gammaFactor_tendsto_gen

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open Complex MeasureTheory intervalIntegral Filter
open scoped Real Topology BigOperators

namespace Commons.NumberTheory.DirichletCharacter

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The Laplace transform `F(z) = ∫_0^{x₀} e^{-zt} f(t) dt`. -/
def lapX (x₀ : ℝ) (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * f t

/-- `lapX x₀ f` is entire when `f` is continuous on `[0,x₀]`. -/
lemma differentiable_lapX {x₀ : ℝ} {f : ℝ → ℂ} (h0x : (0:ℝ) ≤ x₀)
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) :
    Differentiable ℂ (lapX x₀ f) := by
  obtain ⟨C, hC⟩ : ∃ C, ∀ t ∈ Set.Icc (0:ℝ) x₀, ‖f t‖ ≤ C := by
    have hb : Bornology.IsBounded (f '' Set.Icc (0:ℝ) x₀) :=
      (isCompact_Icc (a := (0:ℝ)) (b := x₀)).image_of_continuousOn hcont |>.isBounded
    obtain ⟨C, hC⟩ := hb.exists_norm_le
    exact ⟨C, fun t ht => hC (f t) (Set.mem_image_of_mem f ht)⟩
  intro z
  rw [show lapX x₀ f = fun w => ∫ t in (0:ℝ)..x₀, Complex.exp (-(w * (t : ℂ))) * f t from rfl]
  have hfAE : AEStronglyMeasurable f (volume.restrict (Set.uIoc (0:ℝ) x₀)) :=
    (hcont.aestronglyMeasurable measurableSet_Icc).mono_measure
      (Measure.restrict_mono (fun t ht => by rw [Set.uIoc_of_le h0x] at ht; exact ⟨le_of_lt ht.1, ht.2⟩) le_rfl)
  have hmulAE : ∀ (g : ℝ → ℂ), Continuous g →
      AEStronglyMeasurable g (volume.restrict (Set.uIoc (0:ℝ) x₀)) := by
    intro g hg
    exact (hg.aestronglyMeasurable).mono_measure
      (Measure.restrict_le_self (μ := volume) (s := Set.uIoc (0:ℝ) x₀))
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := (0:ℝ)) (b := x₀)
    (F := fun w t => Complex.exp (-(w * (t : ℂ))) * f t)
    (F' := fun w t => (-(t : ℂ)) * Complex.exp (-(w * (t : ℂ))) * f t)
    (x₀ := z) (s := Metric.ball z 1)
    (bound := fun _ => x₀ * Real.exp ((‖z‖ + 1) * x₀) * C)
    (Metric.ball_mem_nhds z one_pos)
    (Filter.Eventually.of_forall (fun w =>
      (hmulAE (fun t : ℝ => Complex.exp (-(w * (t : ℂ)))) (by fun_prop)).mul hfAE))
    (by
      have hc : ContinuousOn (fun t : ℝ => Complex.exp (-(z * (t : ℂ))) * f t) (Set.uIcc 0 x₀) :=
        (Continuous.continuousOn (by fun_prop)).mul (hcont.mono (by rw [Set.uIcc_of_le h0x]))
      exact hc.intervalIntegrable)
    ((hmulAE (fun t : ℝ => (-(t : ℂ)) * Complex.exp (-(z * (t : ℂ)))) (by fun_prop)).mul hfAE)
    (by
      filter_upwards with t ht x hx
      rw [Set.uIoc_of_le h0x] at ht
      have ht' : t ∈ Set.Icc (0:ℝ) x₀ := ⟨le_of_lt ht.1, ht.2⟩
      have hnorm : ‖Complex.exp (-(x * (t : ℂ)))‖ ≤ Real.exp ((‖z‖ + 1) * x₀) := by
        rw [Complex.norm_exp]
        apply Real.exp_le_exp.mpr
        have hx1 : ‖x - z‖ < 1 := by rw [← dist_eq_norm]; exact hx
        have hxz : ‖x‖ ≤ ‖z‖ + 1 := by
          have hxx : ‖x‖ = ‖(x - z) + z‖ := by rw [sub_add_cancel]
          rw [hxx]
          calc ‖(x - z) + z‖ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
            _ ≤ ‖z‖ + 1 := by linarith
        calc -(x * (t:ℂ)).re ≤ ‖x * (t:ℂ)‖ := le_trans (neg_le_abs _) (Complex.abs_re_le_norm _)
          _ = ‖x‖ * |t| := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          _ ≤ (‖z‖ + 1) * x₀ := by
              apply mul_le_mul hxz _ (abs_nonneg t) (by linarith [norm_nonneg z])
              rw [abs_le]; exact ⟨by linarith [ht'.1], ht'.2⟩
      calc ‖(-(t : ℂ)) * Complex.exp (-(x * (t : ℂ))) * f t‖
          = |t| * ‖Complex.exp (-(x * (t : ℂ)))‖ * ‖f t‖ := by
            rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ x₀ * Real.exp ((‖z‖ + 1) * x₀) * C := by
            gcongr
            · rw [abs_le]; exact ⟨by linarith [ht'.1], ht'.2⟩
            · exact hC t ht')
    (by apply ContinuousOn.intervalIntegrable; apply continuousOn_const)
    (by
      filter_upwards with t ht x hx
      rw [Set.uIoc_of_le h0x] at ht
      have h1 : HasDerivAt (fun w : ℂ => w * (t : ℂ)) (t : ℂ) x := hasDerivAt_mul_const _
      have h1' : HasDerivAt (fun w : ℂ => -(w * (t : ℂ))) (-(t : ℂ)) x := h1.neg
      have h2 := (Complex.hasDerivAt_exp (-(x * (t : ℂ)))).comp x h1'
      have h2' : HasDerivAt (fun y : ℂ => Complex.exp (-(y * (t : ℂ))))
          (Complex.exp (-(x * (t : ℂ))) * (-(t : ℂ))) x := by
        simpa only [Function.comp_def] using h2
      have h3 : HasDerivAt (fun y : ℂ => Complex.exp (-(y * (t : ℂ))))
          ((-(t : ℂ)) * Complex.exp (-(x * (t : ℂ)))) x := h2'.congr_deriv (by ring)
      exact h3.mul_const (f t))
  exact hmain.2.differentiableAt



/-! ## Bounds for the Laplace transform of `f` -/

/-- The Laplace transform bound of `laplace_transform_bound_complex`, phrased for `lapX`. -/
lemma lapX_norm_le {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B) {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0) (hf0 : f 0 = 0) {z : ℂ} (hz : 0 < z.re) :
    ‖lapX x₀ f z‖ ≤ 3 * B * x₀ / ‖z‖ ^ 2 :=
  Commons.Analysis.Complex.laplace_transform_bound_complex hx₀ hB hcont hf2 hBnd hvan hf0 hz

/-- Bound for `lapX x₀ f ((s - u) * L)`, `L > 0`, `Re u < Re s`. -/
lemma lapX_affine_norm_le {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B) {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0) (hf0 : f 0 = 0)
    {L : ℝ} (hL : 0 < L) {s u : ℂ} (hu : u.re < s.re) :
    ‖lapX x₀ f ((s - u) * (L : ℂ))‖ ≤ 3 * B * x₀ / (L ^ 2 * ‖s - u‖ ^ 2) := by
  have hz : 0 < ((s - u) * (L : ℂ)).re := by
    rw [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im]
    simpa [mul_comm, Complex.sub_re] using mul_pos hL (sub_pos.mpr hu)
  have h := lapX_norm_le hx₀ hB hcont hf2 hBnd hvan hf0 hz
  have hnorm : ‖(s - u) * (L : ℂ)‖ = L * ‖s - u‖ := by
    rw [norm_mul, Complex.norm_of_nonneg hL.le, mul_comm]
  rw [hnorm] at h
  calc ‖lapX x₀ f ((s - u) * (L : ℂ))‖ ≤ 3 * B * x₀ / (L * ‖s - u‖) ^ 2 := h
    _ = 3 * B * x₀ / (L ^ 2 * ‖s - u‖ ^ 2) := by ring_nf

/-- The decay bound for `Φ u = lapX x₀ f ((s-u) L)` on the zeros of `Λ` (which satisfy
`0 < Re u < 1` and `‖u‖ ≥ 2`): `‖Φ u‖ ≤ A / ‖u‖²`. -/
theorem lapX_ratio_le {x₀ B L : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B) (hL : 1 < L) {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0) (hf0 : f 0 = 0)
    {s : ℂ} (hs : 1 < s.re) {u : ℂ} (hu2 : u.re < 1) (hu3 : 2 ≤ ‖u‖) :
    ‖lapX x₀ f ((s - u) * (L : ℂ))‖ ≤
      (3 * B * x₀ / (L ^ 2 * min (1 / 4 : ℝ) ((s.re - 1) ^ 2 / (4 * ‖s‖ ^ 2))) + 1) / ‖u‖ ^ 2 := by
  have hL0 : (0:ℝ) < L := by linarith
  have hsu : u.re < s.re := by linarith
  have hb := lapX_affine_norm_le hx₀ hB hcont hf2 hBnd hvan hf0 hL0 hsu
  set c : ℝ := min (1 / 4 : ℝ) ((s.re - 1) ^ 2 / (4 * ‖s‖ ^ 2)) with hcdef
  have hc1 : c ≤ 1 / 4 := min_le_left _ _
  have hc2 : c ≤ (s.re - 1) ^ 2 / (4 * ‖s‖ ^ 2) := min_le_right _ _
  have hd0 : 0 < s.re - 1 := by linarith
  have hsnorm : (0:ℝ) < ‖s‖ := lt_of_lt_of_le (by linarith : (0:ℝ) < s.re) (Complex.re_le_norm s)
  have hcd0 : 0 < c := lt_min (by norm_num) (div_pos (pow_pos hd0 2) (by positivity))
  have hkey : c * ‖u‖ ^ 2 ≤ ‖s - u‖ ^ 2 := by
    by_cases hcase : ‖u‖ ≤ 2 * ‖s‖
    · have h3 : ‖u‖ ^ 2 ≤ 4 * ‖s‖ ^ 2 := by nlinarith [hcase, norm_nonneg u, norm_nonneg s]
      have h4 : (s.re - 1) ^ 2 ≤ ‖s - u‖ ^ 2 := by
        have h1 : s.re - 1 ≤ ‖s - u‖ := by
          calc s.re - 1 ≤ s.re - u.re := by linarith
            _ = (s - u).re := by simp
            _ ≤ ‖s - u‖ := Complex.re_le_norm _
        nlinarith [h1, hd0.le]
      calc c * ‖u‖ ^ 2 ≤ ((s.re - 1) ^ 2 / (4 * ‖s‖ ^ 2)) * ‖u‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hc2 (by positivity)
        _ ≤ ((s.re - 1) ^ 2 / (4 * ‖s‖ ^ 2)) * (4 * ‖s‖ ^ 2) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = (s.re - 1) ^ 2 := by field_simp
        _ ≤ ‖s - u‖ ^ 2 := h4
    · have h1 : ‖u‖ - ‖s‖ ≤ ‖s - u‖ := by
        have h := norm_add_le (u - s) s
        rw [sub_add_cancel] at h
        have h2 : ‖u - s‖ = ‖s - u‖ := by rw [← norm_neg, neg_sub]
        rw [h2] at h
        linarith
      have h4 : ‖u‖ ^ 2 / 4 ≤ ‖s - u‖ ^ 2 := by
        have h5 : (2 * ‖s‖) < ‖u‖ := lt_of_not_ge hcase
        have h6 : ‖s‖ ≤ ‖u‖ / 2 := by linarith
        have h7 : ‖u‖ / 2 ≤ ‖s - u‖ := by linarith
        nlinarith [h7, norm_nonneg (s - u), norm_nonneg u]
      calc c * ‖u‖ ^ 2 ≤ (1 / 4) * ‖u‖ ^ 2 := mul_le_mul_of_nonneg_right hc1 (by positivity)
        _ = ‖u‖ ^ 2 / 4 := by ring
        _ ≤ ‖s - u‖ ^ 2 := h4
  have hsune : s - u ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [h] at hsu; exact lt_irrefl _ hsu
  have hdenu : (0:ℝ) < ‖s - u‖ := norm_pos_iff.mpr hsune
  have hun : (0:ℝ) < ‖u‖ := by linarith
  have hstep1 : 3 * B * x₀ / (L ^ 2 * ‖s - u‖ ^ 2) ≤ 3 * B * x₀ / (L ^ 2 * (c * ‖u‖ ^ 2)) := by
    have h1 : L ^ 2 * (c * ‖u‖ ^ 2) ≤ L ^ 2 * ‖s - u‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hkey (by positivity)
    have h2 : 0 < L ^ 2 * ‖s - u‖ ^ 2 := by positivity
    have h3 : 0 < L ^ 2 * (c * ‖u‖ ^ 2) := by positivity
    rw [div_le_div_iff₀ h2 h3]
    nlinarith [h1, mul_le_mul_of_nonneg_left h1 (show (0:ℝ) ≤ 3 * B * x₀ by positivity)]
  calc ‖lapX x₀ f ((s - u) * (L : ℂ))‖ ≤ 3 * B * x₀ / (L ^ 2 * ‖s - u‖ ^ 2) := hb
    _ ≤ 3 * B * x₀ / (L ^ 2 * (c * ‖u‖ ^ 2)) := hstep1
    _ = (3 * B * x₀ / (L ^ 2 * c)) / ‖u‖ ^ 2 := by
        rw [div_div]; ring_nf
    _ ≤ (3 * B * x₀ / (L ^ 2 * c) + 1) / ‖u‖ ^ 2 := by
        rw [add_div]
        exact le_add_of_nonneg_right (by positivity)


/-! ## The bound `‖Φ u‖ ≤ M / (1 + ‖u‖²)` on the half-plane `Re u ≤ α` -/

/-- On the half-plane `Re u ≤ α` with `α < Re s`, the Laplace transform `Φ u = lapX x₀ f ((s-u)L)`
is bounded by `M / (1 + ‖u‖²)` for the explicit constant `M` below. -/
theorem lapX_M_bound {x₀ B L : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B) (hL : 1 < L) {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0) (hf0 : f 0 = 0)
    {s : ℂ} {α : ℝ} (hασ : α < s.re) {u : ℂ} (hu : u.re ≤ α) :
    ‖lapX x₀ f ((s - u) * (L : ℂ))‖ ≤
      (3 * B * x₀ / L ^ 2 * ((1 + 2 * ‖s‖ ^ 2) / (s.re - α) ^ 2 + 2) + 1) / (1 + ‖u‖ ^ 2) := by
  have hL0 : (0:ℝ) < L := by linarith
  have hsu : u.re < s.re := lt_of_le_of_lt hu hασ
  have hb := lapX_affine_norm_le hx₀ hB hcont hf2 hBnd hvan hf0 hL0 hsu
  have hδ : 0 < s.re - α := by linarith
  have hδ2 : 0 < (s.re - α) ^ 2 := pow_pos hδ 2
  have hre : s.re - α ≤ ‖s - u‖ := by
    calc s.re - α ≤ s.re - u.re := by linarith
      _ = (s - u).re := by simp
      _ ≤ ‖s - u‖ := Complex.re_le_norm _
  have hden : (s.re - α) ^ 2 ≤ ‖s - u‖ ^ 2 := by nlinarith [hre, hδ.le]
  have hsune : s - u ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [h] at hsu; exact lt_irrefl _ hsu
  have hdenu : (0:ℝ) < ‖s - u‖ ^ 2 := by positivity
  have hnum : 1 + ‖u‖ ^ 2 ≤ (1 + 2 * ‖s‖ ^ 2) + 2 * ‖s - u‖ ^ 2 := by
    have hle : ‖u‖ ≤ ‖s - u‖ + ‖s‖ := by
      have h := norm_add_le (u - s) s
      rw [sub_add_cancel] at h
      have h2 : ‖u - s‖ = ‖s - u‖ := by rw [← norm_neg, neg_sub]
      rw [h2] at h
      exact h
    have hsq : ‖u‖ ^ 2 ≤ 2 * ‖s - u‖ ^ 2 + 2 * ‖s‖ ^ 2 := by
      have h1 : ‖u‖ ^ 2 ≤ (‖s - u‖ + ‖s‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg u) hle 2
      have h2 : (‖s - u‖ + ‖s‖) ^ 2 ≤ 2 * ‖s - u‖ ^ 2 + 2 * ‖s‖ ^ 2 := by
        nlinarith [sq_nonneg (‖s - u‖ - ‖s‖)]
      linarith
    linarith
  have hstep : (1 + ‖u‖ ^ 2) / ‖s - u‖ ^ 2 ≤ (1 + 2 * ‖s‖ ^ 2) / (s.re - α) ^ 2 + 2 := by
    have h1 : (1 + ‖u‖ ^ 2) / ‖s - u‖ ^ 2
        ≤ ((1 + 2 * ‖s‖ ^ 2) + 2 * ‖s - u‖ ^ 2) / ‖s - u‖ ^ 2 :=
      div_le_div_of_nonneg_right hnum hdenu.le
    have h2 : ((1 + 2 * ‖s‖ ^ 2) + 2 * ‖s - u‖ ^ 2) / ‖s - u‖ ^ 2
        = (1 + 2 * ‖s‖ ^ 2) / ‖s - u‖ ^ 2 + 2 := by
      field_simp
    have h3 : (1 + 2 * ‖s‖ ^ 2) / ‖s - u‖ ^ 2 ≤ (1 + 2 * ‖s‖ ^ 2) / (s.re - α) ^ 2 := by
      rw [div_le_div_iff₀ hdenu hδ2]
      nlinarith [hden]
    linarith [h1, h2.le, h2.ge, h3]
  have hkey : ‖lapX x₀ f ((s - u) * (L : ℂ))‖ * (1 + ‖u‖ ^ 2)
      ≤ 3 * B * x₀ / L ^ 2 * ((1 + 2 * ‖s‖ ^ 2) / (s.re - α) ^ 2 + 2) + 1 := by
    have h1 : ‖lapX x₀ f ((s - u) * (L : ℂ))‖ * (1 + ‖u‖ ^ 2)
        ≤ 3 * B * x₀ / (L ^ 2 * ‖s - u‖ ^ 2) * (1 + ‖u‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    have h2 : 3 * B * x₀ / (L ^ 2 * ‖s - u‖ ^ 2) * (1 + ‖u‖ ^ 2)
        = 3 * B * x₀ / L ^ 2 * ((1 + ‖u‖ ^ 2) / ‖s - u‖ ^ 2) := by
      field_simp
    have h3 : 3 * B * x₀ / L ^ 2 * ((1 + ‖u‖ ^ 2) / ‖s - u‖ ^ 2)
        ≤ 3 * B * x₀ / L ^ 2 * ((1 + 2 * ‖s‖ ^ 2) / (s.re - α) ^ 2 + 2) :=
      mul_le_mul_of_nonneg_left hstep (by positivity)
    linarith [h1, h2.le, h2.ge, h3]
  rw [le_div_iff₀ (by positivity : (0:ℝ) < 1 + ‖u‖ ^ 2)]
  linarith [hkey]

/-! ## Bounds for the logarithmic derivative of the gamma factor on the line `Re s = α` -/

/-- Pointwise bound for `logDeriv (gammaFactor χ)` on `Re s = α` with `1 < α ≤ 2`. -/
lemma norm_logDeriv_gammaFactor_alpha {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {α : ℝ}
    (hα1 : 1 < α) (hα2 : α ≤ 2) (t : ℝ) :
    ‖logDeriv (DirichletCharacter.gammaFactor χ) ((α : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      Real.log Real.pi / 2 + (1 / 2 : ℝ) * (Real.log (2 + |t|) + 8) := by
  have hcomm : ((α : ℂ) + (t : ℂ) * Complex.I) = ((α : ℂ) + Complex.I * (t : ℂ)) := by ring
  rcases χ.even_or_odd with hE | hO
  · have hfun : DirichletCharacter.gammaFactor χ = Complex.Gammaℝ := funext hE.gammaFactor_def
    rw [hfun, hcomm]
    exact Commons.NumberTheory.DirichletCharacter.norm_logDeriv_Gammaℝ_le α t (by linarith) (by linarith)
  · have hfun : DirichletCharacter.gammaFactor χ = fun s => Complex.Gammaℝ (s + 1) :=
      funext hO.gammaFactor_def
    rw [hfun]
    have hα1' : 0 < ((α : ℂ) + (t : ℂ) * Complex.I + 1).re := by simp; linarith
    have hcomp : logDeriv (fun s : ℂ => Complex.Gammaℝ (s + 1)) ((α : ℂ) + (t : ℂ) * Complex.I)
        = logDeriv Complex.Gammaℝ ((α : ℂ) + (t : ℂ) * Complex.I + 1) := by
      have h := logDeriv_comp (f := Complex.Gammaℝ) (g := fun s : ℂ => s + 1)
        (x := ((α : ℂ) + (t : ℂ) * Complex.I))
        (differentiableAt_Gammaℝ _ hα1')
        (by fun_prop : DifferentiableAt ℂ (fun s : ℂ => s + 1) ((α : ℂ) + (t : ℂ) * Complex.I))
      have hder : deriv (fun s : ℂ => s + 1) ((α : ℂ) + (t : ℂ) * Complex.I) = 1 := by simp
      rw [hder, mul_one] at h
      simpa [Function.comp_def] using h
    rw [hcomp]
    have h2 : ((α : ℂ) + (t : ℂ) * Complex.I + 1) = (((α + 1 : ℝ)) : ℂ) + Complex.I * (t : ℂ) := by
      push_cast; ring
    rw [h2]
    exact Commons.NumberTheory.DirichletCharacter.norm_logDeriv_Gammaℝ_le (α + 1) t (by linarith) (by linarith)


/-- Integrability of a product `g · P` when `g` grows at most logarithmically and `P` is
dominated by a Lorentzian `K / (a² + (t-b)²)`. -/
private lemma integrable_of_log_le_lorentz_aux {g P : ℝ → ℂ} {a b C K : ℝ} (ha : 0 < a)
    (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hmeas : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => g t * P t) MeasureTheory.volume)
    (hb : ∀ t : ℝ, ‖g t‖ ≤ C * (Real.log (2 + |t|) + 1))
    (hP : ∀ t : ℝ, ‖P t‖ ≤ K / (a ^ 2 + (t - b) ^ 2)) :
    MeasureTheory.Integrable (fun t : ℝ => g t * P t) MeasureTheory.volume := by
  set c : ℝ := min (a ^ 2) 1 / (4 * (1 + b ^ 2)) with hcdef
  have hc : 0 < c := by
    rw [hcdef]
    have h1 : 0 < min (a ^ 2) 1 := lt_min (pow_pos ha 2) (by norm_num)
    positivity
  have hkey : ∀ t : ℝ, c * (1 + t ^ 2) ≤ a ^ 2 + (t - b) ^ 2 := by
    intro t
    have hm0 : (0:ℝ) ≤ min (a ^ 2) 1 := le_of_lt (lt_min (pow_pos ha 2) (by norm_num))
    have hm1 : min (a ^ 2) 1 ≤ 1 := min_le_right _ _
    have hma : min (a ^ 2) 1 ≤ a ^ 2 := min_le_left _ _
    have h1 : min (a ^ 2) 1 / 2 * (1 + (t - b) ^ 2) ≤ a ^ 2 + (t - b) ^ 2 := by
      by_cases hcase : 1 ≤ (t - b) ^ 2
      · nlinarith [hm1, hcase, hm0]
      · nlinarith [hma, lt_of_not_ge hcase, hm0]
    have h2 : 1 + t ^ 2 ≤ 2 * (1 + b ^ 2) * (1 + (t - b) ^ 2) := by
      have h3 : 2 * b * (t - b) ≤ 1 + b ^ 2 * (t - b) ^ 2 := by
        nlinarith [sq_nonneg (b * (t - b) - 1)]
      nlinarith [h3, sq_nonneg (t - b), sq_nonneg b]
    have h3 : c * (1 + t ^ 2) ≤ c * (2 * (1 + b ^ 2) * (1 + (t - b) ^ 2)) :=
      mul_le_mul_of_nonneg_left h2 hc.le
    have h4 : c * (2 * (1 + b ^ 2) * (1 + (t - b) ^ 2))
        = min (a ^ 2) 1 / 2 * (1 + (t - b) ^ 2) := by
      rw [hcdef]; field_simp; ring
    linarith
  refine Commons.NumberTheory.Linnik.integrable_of_log_bound (C := C * K / c) (by positivity) hmeas ?_
  intro t
  rw [norm_mul]
  have hlog : 0 ≤ Real.log (2 + |t|) + 1 := by
    have := Real.log_nonneg (show (1:ℝ) ≤ 2 + |t| by linarith [abs_nonneg t]); linarith
  have hden : 0 < a ^ 2 + (t - b) ^ 2 := by nlinarith [sq_nonneg (t - b), pow_pos ha 2]
  have hkey' := hkey t
  have hbound : 1 / (a ^ 2 + (t - b) ^ 2) ≤ (1 / c) / (1 + t ^ 2) := by
    rw [div_le_div_iff₀ hden (by positivity), one_mul, div_mul_eq_mul_div, le_div_iff₀ hc]
    linarith [hkey']
  calc ‖g t‖ * ‖P t‖ ≤ (C * (Real.log (2 + |t|) + 1)) * (K / (a ^ 2 + (t - b) ^ 2)) :=
        mul_le_mul (hb t) (hP t) (norm_nonneg _) (by positivity)
    _ ≤ (C * (Real.log (2 + |t|) + 1)) * (K * ((1 / c) / (1 + t ^ 2))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc K / (a ^ 2 + (t - b) ^ 2) = K * (1 / (a ^ 2 + (t - b) ^ 2)) := by ring
          _ ≤ K * ((1 / c) / (1 + t ^ 2)) := mul_le_mul_of_nonneg_left hbound hK
    _ = (C * K / c) * (Real.log (2 + |t|) + 1) / (1 + t ^ 2) := by ring


/-! ## Integrability of the integrands on the vertical lines -/

/-- Pointwise Lorentz-type bound for `Φ (β + it) = lapX x₀ f ((s - (β + it)) L)`, `β < Re s`. -/
lemma lapX_lorentz_bound {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B) {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0) (hf0 : f 0 = 0)
    {L : ℝ} (hL : 1 < L) {s : ℂ} {β : ℝ} (hβ : β < s.re) (t : ℝ) :
    ‖lapX x₀ f ((s - ((β : ℂ) + (t : ℂ) * Complex.I)) * (L : ℂ))‖ ≤
      (3 * B * x₀ / L ^ 2) / ((s.re - β) ^ 2 + (t - s.im) ^ 2) := by
  have hL0 : (0:ℝ) < L := by linarith
  have hbre : (((β : ℂ) + (t : ℂ) * Complex.I)).re = β := by simp
  have hb : ‖lapX x₀ f ((s - ((β : ℂ) + (t : ℂ) * Complex.I)) * (L : ℂ))‖ ≤
      3 * B * x₀ / (L ^ 2 * ‖s - ((β : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) :=
    lapX_affine_norm_le hx₀ hB hcont hf2 hBnd hvan hf0 hL0 (by rw [hbre]; exact hβ)
  have hnorm : ‖s - ((β : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 = (s.re - β) ^ 2 + (t - s.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  rw [hnorm] at hb
  calc ‖lapX x₀ f ((s - ((β : ℂ) + (t : ℂ) * Complex.I)) * (L : ℂ))‖
      ≤ 3 * B * x₀ / (L ^ 2 * ((s.re - β) ^ 2 + (t - s.im) ^ 2)) := hb
    _ = (3 * B * x₀ / L ^ 2) / ((s.re - β) ^ 2 + (t - s.im) ^ 2) := by rw [div_div]

/-- The map `u ↦ lapX x₀ f ((s-u)L)` is entire. -/
lemma differentiable_lapX_affine {x₀ : ℝ} {f : ℝ → ℂ} (h0x : (0:ℝ) ≤ x₀)
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) (s : ℂ) (L : ℝ) :
    Differentiable ℂ (fun u : ℂ => lapX x₀ f ((s - u) * (L : ℂ))) := by
  refine (differentiable_lapX h0x hcont).comp (fun z => ?_)
  exact (by fun_prop : DifferentiableAt ℂ (fun u : ℂ => (s - u) * (L : ℂ)) z)

/-- Measurability of `logDeriv` of the `L`-function. -/
lemma measurable_logDeriv_LFunction' {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) :
    Measurable (fun z : ℂ => logDeriv (DirichletCharacter.LFunction χ) z) := by
  have hdF : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    DirichletCharacter.differentiable_LFunction hχ
  have hd : Measurable (deriv (DirichletCharacter.LFunction χ)) := hdF.deriv.continuous.measurable
  have hFm : Measurable (DirichletCharacter.LFunction χ) := hdF.continuous.measurable
  unfold logDeriv
  exact hd.div hFm

/-- Pointwise bound for `logDeriv (gammaFactor χ)` on `Re s = α`, `1 < α ≤ 2`. -/
lemma norm_logDeriv_gammaFactor_alpha_log {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {α : ℝ} (hα1 : 1 < α) (hα2 : α ≤ 2) (t : ℝ) :
    ‖logDeriv (DirichletCharacter.gammaFactor χ) ((α : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      13 * (Real.log (2 + |t|) + 1) := by
  have h := norm_logDeriv_gammaFactor_alpha χ hα1 hα2 t
  have hlog : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hpi : Real.log Real.pi / 2 + 2 ≤ 5 := by
    have h1 := Real.log_le_sub_one_of_pos Real.pi_pos
    have h2 := Real.pi_lt_four
    linarith
  nlinarith [h, hlog, hpi]

/-- Integrability of `logDeriv γ · Φ` on the line `Re s = α`. -/
lemma integrable_logDeriv_gammaFactor_mul_lapX_alpha {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B)
    {f : ℝ → ℂ} (hcont : ContinuousOn f (Set.Icc 0 x₀))
    (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0) (hf0 : f 0 = 0)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {L : ℝ} (hL : 1 < L) {s : ℂ}
    {α : ℝ} (hα1 : 1 < α) (hα2 : α ≤ 2) (hασ : α < s.re) :
    MeasureTheory.Integrable (fun t : ℝ =>
      logDeriv (DirichletCharacter.gammaFactor χ) ((α : ℂ) + (t : ℂ) * Complex.I) *
      lapX x₀ f ((s - ((α : ℂ) + (t : ℂ) * Complex.I)) * (L : ℂ))) := by
  have hδ : 0 < s.re - α := by linarith
  have hK : (0:ℝ) ≤ 3 * B * x₀ / L ^ 2 := by positivity
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun t : ℝ =>
      logDeriv (DirichletCharacter.gammaFactor χ) ((α : ℂ) + (t : ℂ) * Complex.I) *
      lapX x₀ f ((s - ((α : ℂ) + (t : ℂ) * Complex.I)) * (L : ℂ))) MeasureTheory.volume := by
    refine (Commons.NumberTheory.Linnik.measurable_logDeriv_gammaFactor_line χ α).mul ?_
    exact ((differentiable_lapX_affine (le_of_lt hx₀) hcont s L).continuous.measurable.comp
      (by fun_prop)).aestronglyMeasurable
  refine integrable_of_log_le_lorentz_aux (a := s.re - α) (b := s.im) (C := 13) (K := 3 * B * x₀ / L ^ 2)
    hδ (by norm_num) hK hmeas (fun t => norm_logDeriv_gammaFactor_alpha_log χ hα1 hα2 t) (fun t => ?_)
  exact lapX_lorentz_bound hx₀ hB hcont hf2 hBnd hvan hf0 hL hασ t

/-- Integrability of `logDeriv γ · Φ` on the line `Re s = -1/2`. -/
lemma integrable_logDeriv_gammaFactor_mul_lapX_left {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B)
    {f : ℝ → ℂ} (hcont : ContinuousOn f (Set.Icc 0 x₀))
    (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0) (hf0 : f 0 = 0)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {L : ℝ} (hL : 1 < L) {s : ℂ}
    (hs : 1 < s.re) :
    MeasureTheory.Integrable (fun t : ℝ =>
      logDeriv (DirichletCharacter.gammaFactor χ) (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I) *
      lapX x₀ f ((s - (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I)) * (L : ℂ))) := by
  have hδ : 0 < s.re + 1/2 := by linarith
  have hK : (0:ℝ) ≤ 3 * B * x₀ / L ^ 2 := by positivity
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun t : ℝ =>
      logDeriv (DirichletCharacter.gammaFactor χ) (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I) *
      lapX x₀ f ((s - (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I)) * (L : ℂ))) MeasureTheory.volume := by
    refine (Commons.NumberTheory.Linnik.measurable_logDeriv_gammaFactor_line χ (-1/2)).mul ?_
    exact ((differentiable_lapX_affine (le_of_lt hx₀) hcont s L).continuous.measurable.comp
      (by fun_prop)).aestronglyMeasurable
  refine integrable_of_log_le_lorentz_aux (a := s.re + 1/2) (b := s.im) (C := 13) (K := 3 * B * x₀ / L ^ 2)
    (by linarith) (by norm_num) hK hmeas
    (fun t => Commons.NumberTheory.Linnik.norm_logDeriv_gammaFactor_left χ t) (fun t => ?_)
  have h : ‖lapX x₀ f ((s - (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I)) * (L : ℂ))‖ ≤
      (3 * B * x₀ / L ^ 2) / ((s.re - (-1/2)) ^ 2 + (t - s.im) ^ 2) :=
    lapX_lorentz_bound hx₀ hB hcont hf2 hBnd hvan hf0 hL (β := -1/2) (by linarith) t
  have harg : ((s.re - (-1/2) : ℝ) ^ 2 + (t - s.im) ^ 2) = ((s.re + 1/2) ^ 2 + (t - s.im) ^ 2) := by
    ring
  rwa [harg] at h

/-- Integrability of `logDeriv L(χ) · Φ` on the line `Re s = α`. -/
lemma integrable_logDeriv_LFunction_mul_lapX_alpha {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B)
    {f : ℝ → ℂ} (hcont : ContinuousOn f (Set.Icc 0 x₀))
    (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0) (hf0 : f 0 = 0)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {L : ℝ} (hL : 1 < L) {s : ℂ}
    {α : ℝ} (hα1 : 1 < α) (hα2 : α ≤ 2) (hασ : α < s.re) :
    MeasureTheory.Integrable (fun t : ℝ =>
      logDeriv (DirichletCharacter.LFunction χ) ((α : ℂ) + (t : ℂ) * Complex.I) *
      lapX x₀ f ((s - ((α : ℂ) + (t : ℂ) * Complex.I)) * (L : ℂ))) := by
  have hδ : 0 < s.re - α := by linarith
  have hK : (0:ℝ) ≤ 3 * B * x₀ / L ^ 2 := by positivity
  have hC : (0:ℝ) ≤ 100 / (α - 1) ^ 2 + 100 := by positivity
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun t : ℝ =>
      logDeriv (DirichletCharacter.LFunction χ) ((α : ℂ) + (t : ℂ) * Complex.I) *
      lapX x₀ f ((s - ((α : ℂ) + (t : ℂ) * Complex.I)) * (L : ℂ))) MeasureTheory.volume := by
    refine ((measurable_logDeriv_LFunction' χ hχ).comp (by fun_prop)).aestronglyMeasurable.mul ?_
    exact ((differentiable_lapX_affine (le_of_lt hx₀) hcont s L).continuous.measurable.comp
      (by fun_prop)).aestronglyMeasurable
  refine integrable_of_log_le_lorentz_aux (a := s.re - α) (b := s.im)
    (C := 100 / (α - 1) ^ 2 + 100) (K := 3 * B * x₀ / L ^ 2) hδ hC hK hmeas (fun t => ?_) (fun t => ?_)
  · have h := norm_logDeriv_LFunction_le_re_gt_one χ
      (s := ((α : ℂ) + (t : ℂ) * Complex.I)) (by simp; exact hα1) (by simp; linarith)
    have hre : ((α : ℂ) + (t : ℂ) * Complex.I).re = α := by simp
    rw [hre] at h
    have hlog : 1 ≤ Real.log (2 + |t|) + 1 := by
      have := Real.log_nonneg (show (1:ℝ) ≤ 2 + |t| by linarith [abs_nonneg t])
      linarith
    nlinarith [h, hlog]
  · exact lapX_lorentz_bound hx₀ hB hcont hf2 hBnd hvan hf0 hL hασ t

/-- Integrability of `logDeriv L(χ) · Φ` on the line `Re s = -1/2`. -/
lemma integrable_logDeriv_LFunction_mul_lapX_left {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B)
    {f : ℝ → ℂ} (hcont : ContinuousOn f (Set.Icc 0 x₀))
    (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0) (hf0 : f 0 = 0)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
    {L : ℝ} (hL : 1 < L) {s : ℂ} (hs : 1 < s.re) :
    MeasureTheory.Integrable (fun t : ℝ =>
      logDeriv (DirichletCharacter.LFunction χ) (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I) *
      lapX x₀ f ((s - (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I)) * (L : ℂ))) := by
  have hδ : 0 < s.re + 1/2 := by linarith
  have hK : (0:ℝ) ≤ 3 * B * x₀ / L ^ 2 := by positivity
  have hN : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast NeZero.one_le
  have hC : (0:ℝ) ≤ 100 * (Real.log (N:ℝ) + 2) := by
    have : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg hN
    linarith
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun t : ℝ =>
      logDeriv (DirichletCharacter.LFunction χ) (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I) *
      lapX x₀ f ((s - (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I)) * (L : ℂ))) MeasureTheory.volume := by
    refine ((measurable_logDeriv_LFunction' χ hχ).comp (by fun_prop)).aestronglyMeasurable.mul ?_
    exact ((differentiable_lapX_affine (le_of_lt hx₀) hcont s L).continuous.measurable.comp
      (by fun_prop)).aestronglyMeasurable
  refine integrable_of_log_le_lorentz_aux (a := s.re + 1/2) (b := s.im)
    (C := 100 * (Real.log (N:ℝ) + 2)) (K := 3 * B * x₀ / L ^ 2) hδ hC hK hmeas
    (fun t => ?_) (fun t => ?_)
  · have h := Commons.NumberTheory.Linnik.logDeriv_LFunction_leftEdge_uniform χ hχ ‹_› t
    have hlogN : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg hN
    have hlog : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
    have hkey : Real.log (N:ℝ) + Real.log (2 + |t|) + 1
        ≤ (Real.log (N:ℝ) + 2) * (Real.log (2 + |t|) + 1) := by nlinarith
    calc ‖logDeriv (DirichletCharacter.LFunction χ) (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I)‖
        ≤ 100 * (Real.log (N:ℝ) + Real.log (2 + |t|) + 1) := h
      _ ≤ 100 * (Real.log (N:ℝ) + 2) * (Real.log (2 + |t|) + 1) := by
          have : (0:ℝ) ≤ 100 := by norm_num
          nlinarith [hkey]
  · have h : ‖lapX x₀ f ((s - (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I)) * (L : ℂ))‖ ≤
        (3 * B * x₀ / L ^ 2) / ((s.re - (-1/2)) ^ 2 + (t - s.im) ^ 2) :=
      lapX_lorentz_bound hx₀ hB hcont hf2 hBnd hvan hf0 hL (β := -1/2) (by linarith) t
    have harg : ((s.re - (-1/2) : ℝ) ^ 2 + (t - s.im) ^ 2) = ((s.re + 1/2) ^ 2 + (t - s.im) ^ 2) := by
      ring
    rwa [harg] at h


/-! ## The smoothed explicit formula -/


/-- Elementary numerical estimate for the final bound. -/
private lemma final_estimate {B x₀ L Λ c : ℝ} (hB : 0 ≤ B) (hx₀ : 0 < x₀) (hL : 0 < L)
    (hc : 1 ≤ c) (hΛ : 1 ≤ Λ) :
    (L / (2 * Real.pi)) * ((3 * B * x₀ / L ^ 2) * 2000 * Λ) + L * (3 * B * x₀ / (L ^ 2 * c))
      ≤ (3 * B * x₀ * (1 + 1000 / Real.pi) + 1) * Λ / L := by
  have hBx : 0 ≤ 3 * B * x₀ := by positivity
  have hΛ0 : 0 ≤ Λ := by linarith
  have hc0 : 0 < c := by linarith
  have h2 : L * (3 * B * x₀ / (L ^ 2 * c)) ≤ 3 * B * x₀ * Λ / L := by
    have heq : L * (3 * B * x₀ / (L ^ 2 * c)) = 3 * B * x₀ / (L * c) := by field_simp
    rw [heq, div_le_div_iff₀ (by positivity : (0:ℝ) < L * c) hL]
    have hΛc : 1 ≤ Λ * c := by nlinarith [hΛ, hc]
    nlinarith [hΛc, hBx, hL, mul_nonneg hBx (le_of_lt hL)]
  have h1 : (L / (2 * Real.pi)) * ((3 * B * x₀ / L ^ 2) * 2000 * Λ)
      = (3 * B * x₀ * (1000 / Real.pi) * Λ) / L := by
    field_simp
    ring
  have h3 : (3 * B * x₀ * (1000 / Real.pi) * Λ) / L + 3 * B * x₀ * Λ / L
      ≤ (3 * B * x₀ * (1 + 1000 / Real.pi) + 1) * Λ / L := by
    rw [← add_div, div_le_div_iff₀ hL hL]
    nlinarith [hΛ0, hBx, hL, mul_nonneg hΛ0 (le_of_lt hL)]
  rw [h1]
  linarith

/-- The main theorem: the smoothed explicit formula of Heath-Brown (1992, §5). -/
theorem explicit_formula_smoothed_upper {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
      (hχprim : χ.IsPrimitive) {L : ℝ} (hL : 1 < L) {f : ℝ → ℂ} {s : ℂ} (hs : 1 < s.re)
      (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
      (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
      (hvanish : ∀ t : ℝ, x₀ ≤ t → f t = 0) (hf0 : f 0 = 0),
      ‖(∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) / (n : ℂ) ^ s *
            f (Real.log n / L))
        + L * (∑' u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) *
            (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * (L : ℂ)) * (t : ℂ))) * f t))‖
        ≤ K * (Real.log (2 + ‖s‖) + 1) / L := by
  refine ⟨3 * B * x₀ * (1 + 1000 / Real.pi) + 1, by positivity, ?_⟩
  intro N _ χ hχ hχprim L hL f s hs hcont hf2 hBnd hvanish hf0
  have hL0 : (0:ℝ) < L := by linarith
  -- the auxiliary line `Re = α`
  set α : ℝ := (1 + min s.re 2) / 2 with hαdef
  have hα1 : 1 < α := by
    rw [hαdef]
    have : 1 < min s.re 2 := lt_min hs (by norm_num)
    linarith
  have hα2 : α < 2 := by
    rw [hαdef]
    have : min s.re 2 ≤ 2 := min_le_right _ _
    linarith
  have hασ : α < s.re := by
    rw [hαdef]
    by_cases h : s.re ≤ 2
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right (le_of_not_ge h)]; linarith
  have hα2le : α ≤ 2 := le_of_lt hα2
  -- the entire kernel `Φ u = F((s-u)L)`
  set Φ : ℂ → ℂ := fun u => lapX x₀ f ((s - u) * (L : ℂ)) with hΦdef
  have hΦdiff : Differentiable ℂ Φ := differentiable_lapX_affine (le_of_lt hx₀) hcont s L
  -- the constant `M` of the horizontal-vanishing estimates
  have hMpos : 0 < 3 * B * x₀ / L ^ 2 * ((1 + 2 * ‖s‖ ^ 2) / (s.re - α) ^ 2 + 2) + 1 := by
    positivity
  have hΦb : ∀ u : ℂ, u.re ≤ α → ‖Φ u‖ ≤
      (3 * B * x₀ / L ^ 2 * ((1 + 2 * ‖s‖ ^ 2) / (s.re - α) ^ 2 + 2) + 1) / (1 + ‖u‖ ^ 2) := by
    intro u hu
    exact lapX_M_bound hx₀ hB hL hcont hf2 hBnd hvanish hf0 hασ hu
  -- the summability of the divisor series, and the limit of the strip sums
  have hApos : 0 < 3 * B * x₀ / (L ^ 2 * min (1 / 4 : ℝ) ((s.re - 1) ^ 2 / (4 * ‖s‖ ^ 2))) + 1 := by
    positivity
  have hΦratio : ∀ u : ℂ, 0 < u.re → u.re < 1 → 2 ≤ ‖u‖ → ‖Φ u‖ ≤
      (3 * B * x₀ / (L ^ 2 * min (1 / 4 : ℝ) ((s.re - 1) ^ 2 / (4 * ‖s‖ ^ 2))) + 1) / ‖u‖ ^ 2 := by
    intro u _ hu2 hu3
    exact lapX_ratio_le hx₀ hB hL hcont hf2 hBnd hvanish hf0 hs hu2 hu3
  obtain ⟨hsumm, hZ⟩ :=
    divisorSum_summable_and_tendsto χ hχ hχprim (Φ := Φ) hApos hΦratio
  -- integrability of the integrands on the two vertical lines
  have hILα : MeasureTheory.Integrable (fun t : ℝ =>
      logDeriv (DirichletCharacter.LFunction χ) ((α : ℂ) + (t : ℂ) * Complex.I) *
        Φ ((α : ℂ) + (t : ℂ) * Complex.I)) := by
    simpa only [hΦdef] using
      integrable_logDeriv_LFunction_mul_lapX_alpha hx₀ hB hcont hf2 hBnd hvanish hf0 χ hχ hL hα1 hα2le hασ
  have hILl : MeasureTheory.Integrable (fun t : ℝ =>
      logDeriv (DirichletCharacter.LFunction χ) (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I) *
        Φ (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I)) := by
    simpa only [hΦdef] using
      integrable_logDeriv_LFunction_mul_lapX_left hx₀ hB hcont hf2 hBnd hvanish hf0 χ hχ hχprim hL hs
  have hIGα : MeasureTheory.Integrable (fun t : ℝ =>
      logDeriv (DirichletCharacter.gammaFactor χ) ((α : ℂ) + (t : ℂ) * Complex.I) *
        Φ ((α : ℂ) + (t : ℂ) * Complex.I)) := by
    simpa only [hΦdef] using
      integrable_logDeriv_gammaFactor_mul_lapX_alpha hx₀ hB hcont hf2 hBnd hvanish hf0 χ hL hα1 hα2le hασ
  have hIGl : MeasureTheory.Integrable (fun t : ℝ =>
      logDeriv (DirichletCharacter.gammaFactor χ) (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I) *
        Φ (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I)) := by
    simpa only [hΦdef] using
      integrable_logDeriv_gammaFactor_mul_lapX_left hx₀ hB hcont hf2 hBnd hvanish hf0 χ hL hs
  have hIAα : MeasureTheory.Integrable (fun t : ℝ =>
      logDeriv (DirichletCharacter.completedLFunction χ) ((α : ℂ) + (t : ℂ) * Complex.I) *
        Φ ((α : ℂ) + (t : ℂ) * Complex.I)) := by
    refine (hIGα.add hILα).congr (Filter.Eventually.of_forall (fun t => ?_))
    change logDeriv (DirichletCharacter.gammaFactor χ) ((α : ℂ) + (t : ℂ) * Complex.I) *
        Φ ((α : ℂ) + (t : ℂ) * Complex.I)
      + logDeriv (DirichletCharacter.LFunction χ) ((α : ℂ) + (t : ℂ) * Complex.I) *
        Φ ((α : ℂ) + (t : ℂ) * Complex.I)
      = logDeriv (DirichletCharacter.completedLFunction χ) ((α : ℂ) + (t : ℂ) * Complex.I) *
        Φ ((α : ℂ) + (t : ℂ) * Complex.I)
    have hs0 : ((α : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hre1 : -(1 : ℝ) < ((α : ℂ) + (t : ℂ) * Complex.I).re := by simp; linarith
    have hL0' : DirichletCharacter.LFunction χ ((α : ℂ) + (t : ℂ) * Complex.I) ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ) (Or.inl hχ) (by simp; linarith)
    have := logDeriv_completedL_eq_add χ hχ hs0 hre1 hL0'
    rw [this]; ring
  have hIAl : MeasureTheory.Integrable (fun t : ℝ =>
      logDeriv (DirichletCharacter.completedLFunction χ) (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I) *
        Φ (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I)) := by
    refine (hIGl.add hILl).congr (Filter.Eventually.of_forall (fun t => ?_))
    change logDeriv (DirichletCharacter.gammaFactor χ) (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I) *
        Φ (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I)
      + logDeriv (DirichletCharacter.LFunction χ) (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I) *
        Φ (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I)
      = logDeriv (DirichletCharacter.completedLFunction χ) (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I) *
        Φ (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I)
    have hs0 : (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this
    have hre1 : -(1 : ℝ) < (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I).re := by simp; norm_num
    have hL0' : DirichletCharacter.LFunction χ (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I) ≠ 0 :=
      LFunction_ne_zero_of_re_eq_neg_half χ hχ hχprim t
    have := logDeriv_completedL_eq_add χ hχ hs0 hre1 hL0'
    rw [this]; ring
  -- notation for the six contour integrals
  set Ja : ℂ := ∫ τ : ℝ, (- logDeriv (DirichletCharacter.LFunction χ)
      ((α : ℂ) + (τ : ℂ) * Complex.I)) * Φ ((α : ℂ) + (τ : ℂ) * Complex.I) with hJadef
  set Ia : ℂ := ∫ τ : ℝ, logDeriv (DirichletCharacter.LFunction χ)
      ((α : ℂ) + (τ : ℂ) * Complex.I) * Φ ((α : ℂ) + (τ : ℂ) * Complex.I) with hIadef
  set La : ℂ := ∫ τ : ℝ, logDeriv (DirichletCharacter.gammaFactor χ)
      ((α : ℂ) + (τ : ℂ) * Complex.I) * Φ ((α : ℂ) + (τ : ℂ) * Complex.I) with hLadef
  set Ll : ℂ := ∫ τ : ℝ, logDeriv (DirichletCharacter.gammaFactor χ)
      (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I) * Φ (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I) with hLldef
  set Ba : ℂ := ∫ τ : ℝ, logDeriv (DirichletCharacter.completedLFunction χ)
      ((α : ℂ) + (τ : ℂ) * Complex.I) * Φ ((α : ℂ) + (τ : ℂ) * Complex.I) with hBadef
  set Bl : ℂ := ∫ τ : ℝ, logDeriv (DirichletCharacter.completedLFunction χ)
      (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I) * Φ (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I) with hBldef
  set Il : ℂ := ∫ τ : ℝ, logDeriv (DirichletCharacter.LFunction χ)
      (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I) * Φ (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I) with hIldef
  set T : ℂ := ∑' u : ℂ,
    ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) * Φ u with hTdef
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    refine mul_ne_zero two_ne_zero ?_
    exact_mod_cast Real.pi_ne_zero
  -- the three ingredients
  have hP2a := completedL_shift_identity_gen hα1 hα2 hΦdiff hMpos hΦb χ hχ hχprim hIAα hIAl hZ
  have hP2b := gammaFactor_shift_identity_gen hα1 hα2 hΦdiff hMpos hΦb χ hIGα hIGl
  have hP1 := smoothed_vonMangoldt_eq_line hx₀ hB hcont hf2 hBnd hvanish hf0 χ hL hs hα1 hασ
  -- rewriting the ingredients in the notation
  have hJa : Ja = -Ia := by
    rw [hJadef, hIadef, ← MeasureTheory.integral_neg]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with τ
    ring
  have hP1' : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) /
        (n : ℂ) ^ s * f (Real.log n / L)) = (L / (2 * (Real.pi : ℂ))) * Ja := by
    rw [hP1, hJadef]
    congr 1
  have hP2a' : Ba - Bl = (2 * (Real.pi : ℂ)) * T := by
    have h := hP2a
    rw [← hBadef, ← hBldef] at h
    have hcancel : (2 * (Real.pi : ℂ)) * ((1 / (2 * (Real.pi : ℂ))) * (Ba - Bl)) = Ba - Bl := by
      rw [← mul_assoc, mul_one_div_cancel hpi, one_mul]
    have hh := congrArg (fun w : ℂ => (2 * (Real.pi : ℂ)) * w) h
    rw [hcancel] at hh
    exact hh
  have hP2b' : La - Ll = -(2 * (Real.pi : ℂ)) * (if χ.Even then Φ 0 else 0) := by
    have h := hP2b
    rw [← hLadef, ← hLldef] at h
    have hcancel : (2 * (Real.pi : ℂ)) * ((1 / (2 * (Real.pi : ℂ))) * (La - Ll)) = La - Ll := by
      rw [← mul_assoc, mul_one_div_cancel hpi, one_mul]
    have hh := congrArg (fun w : ℂ => (2 * (Real.pi : ℂ)) * w) h
    rw [hcancel] at hh
    rw [hh]
    ring
  have hsplitα : Ba = La + Ia := by
    rw [hBadef, hLadef, hIadef, ← MeasureTheory.integral_add hIGα hILα]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    change logDeriv (DirichletCharacter.completedLFunction χ) ((α : ℂ) + (t : ℂ) * Complex.I) *
        Φ ((α : ℂ) + (t : ℂ) * Complex.I)
      = logDeriv (DirichletCharacter.gammaFactor χ) ((α : ℂ) + (t : ℂ) * Complex.I) *
        Φ ((α : ℂ) + (t : ℂ) * Complex.I)
      + logDeriv (DirichletCharacter.LFunction χ) ((α : ℂ) + (t : ℂ) * Complex.I) *
        Φ ((α : ℂ) + (t : ℂ) * Complex.I)
    have hs0 : ((α : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hre1 : -(1 : ℝ) < ((α : ℂ) + (t : ℂ) * Complex.I).re := by simp; linarith
    have hL0' : DirichletCharacter.LFunction χ ((α : ℂ) + (t : ℂ) * Complex.I) ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ) (Or.inl hχ) (by simp; linarith)
    have hsplit := logDeriv_completedL_eq_add χ hχ hs0 hre1 hL0'
    rw [hsplit]; ring
  have hsplitl : Bl = Ll + Il := by
    rw [hBldef, hLldef, hIldef, ← MeasureTheory.integral_add hIGl hILl]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    change logDeriv (DirichletCharacter.completedLFunction χ) (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I) *
        Φ (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I)
      = logDeriv (DirichletCharacter.gammaFactor χ) (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I) *
        Φ (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I)
      + logDeriv (DirichletCharacter.LFunction χ) (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I) *
        Φ (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I)
    have hs0 : (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this
    have hre1 : -(1 : ℝ) < (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I).re := by simp; norm_num
    have hL0' : DirichletCharacter.LFunction χ (((-1/2:ℝ):ℂ) + (t : ℂ) * Complex.I) ≠ 0 :=
      LFunction_ne_zero_of_re_eq_neg_half χ hχ hχprim t
    have hsplit := logDeriv_completedL_eq_add χ hχ hs0 hre1 hL0'
    rw [hsplit]; ring
  -- the explicit formula
  have hAZ : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) /
        (n : ℂ) ^ s * f (Real.log n / L)) + L * T
      = -(L / (2 * (Real.pi : ℂ))) * Il - L * (if χ.Even then Φ 0 else 0) := by
    rw [hP1']
    have hT : T = (1 / (2 * (Real.pi : ℂ))) * (Ba - Bl) := by
      rw [hP2a']
      field_simp
    have hkey : Ja + (Ba - Bl)
        = -((2 * (Real.pi : ℂ)) * (if χ.Even then Φ 0 else 0) + Il) := by
      have hb := hP2b'
      rw [hJa, hsplitα, hsplitl]
      linear_combination hb
    rw [hT, show (L / (2 * (Real.pi : ℂ))) * Ja + L * ((1 / (2 * (Real.pi : ℂ))) * (Ba - Bl))
        = (L / (2 * (Real.pi : ℂ))) * (Ja + (Ba - Bl)) from by ring, hkey]
    field_simp
    ring
  -- replace the divisor sum by `T`
  have htsum : (∑' u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) *
        (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * (L : ℂ)) * (t : ℂ))) * f t)) = T := by
    rw [hTdef]
    apply tsum_congr
    intro u
    rw [hΦdef]
    rfl
  rw [htsum, hAZ]
  -- the final numerical estimate
  have hfin : ‖Il‖ ≤ (3 * B * x₀ / L ^ 2) * 2000 * (Real.log (2 + ‖s‖) + 1) := by
    rw [hIldef]
    exact norm_integral_logDeriv_L_lefthalf_le hx₀ hB hcont hf2 hBnd hvanish hf0 χ hχ hχprim hL hs
  have hΦ0 : ‖(if χ.Even then Φ 0 else 0)‖ ≤ 3 * B * x₀ / (L ^ 2 * ‖s‖ ^ 2) := by
    by_cases hE : χ.Even
    · rw [if_pos hE]
      have hz : 0 < (s * (L : ℂ)).re := by
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        exact mul_pos (by linarith : 0 < s.re) hL0
      have h := lapX_norm_le hx₀ hB hcont hf2 hBnd hvanish hf0 hz
      have hnorm : ‖s * (L : ℂ)‖ ^ 2 = L ^ 2 * ‖s‖ ^ 2 := by
        rw [norm_mul, Complex.norm_of_nonneg hL0.le]; ring
      rw [hnorm] at h
      simpa only [hΦdef, sub_zero] using h
    · rw [if_neg hE, norm_zero]
      positivity
  have hsge : 1 ≤ ‖s‖ ^ 2 := by
    have h1 : 1 < ‖s‖ := lt_of_lt_of_le hs (Complex.re_le_norm s)
    nlinarith
  have hlog1 : (1:ℝ) ≤ Real.log (2 + ‖s‖) + 1 := by
    have := Real.log_nonneg (show (1:ℝ) ≤ 2 + ‖s‖ by linarith [norm_nonneg s])
    linarith
  have hlog0 : (0:ℝ) ≤ Real.log (2 + ‖s‖) + 1 := le_of_lt (lt_of_lt_of_le zero_lt_one hlog1)
  have hBx : (0:ℝ) ≤ 3 * B * x₀ := by positivity
  have hpi2 : (0:ℝ) < 2 * Real.pi := by positivity
  calc ‖-(L / (2 * (Real.pi : ℂ))) * Il - L * (if χ.Even then Φ 0 else 0)‖
      ≤ ‖-(L / (2 * (Real.pi : ℂ))) * Il‖ + ‖L * (if χ.Even then Φ 0 else 0)‖ :=
        norm_sub_le _ _
    _ = ‖(L / (2 * (Real.pi : ℂ))) * Il‖ + ‖L * (if χ.Even then Φ 0 else 0)‖ := by
        rw [neg_mul, norm_neg]
    _ ≤ (L / (2 * Real.pi)) * ((3 * B * x₀ / L ^ 2) * 2000 * (Real.log (2 + ‖s‖) + 1))
          + L * (3 * B * x₀ / (L ^ 2 * ‖s‖ ^ 2)) := by
        have h1 : ‖(L / (2 * (Real.pi : ℂ))) * Il‖ = (L / (2 * Real.pi)) * ‖Il‖ := by
          rw [norm_mul]
          congr 1
          rw [show (L : ℂ) / (2 * (Real.pi : ℂ)) = ((L / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring]
          exact Complex.norm_of_nonneg (by positivity : (0:ℝ) ≤ L / (2 * Real.pi))
        have h2 : ‖L * (if χ.Even then Φ 0 else 0)‖ = L * ‖(if χ.Even then Φ 0 else 0)‖ := by
          rw [show (L : ℂ) = ((L : ℝ) : ℂ) by rfl, norm_mul]
          rw [Complex.norm_of_nonneg hL0.le]
        rw [h1, h2]
        linarith [mul_le_mul_of_nonneg_left hfin (by positivity : (0:ℝ) ≤ L / (2 * Real.pi)),
          mul_le_mul_of_nonneg_left hΦ0 hL0.le]
    _ ≤ (3 * B * x₀ * (1 + 1000 / Real.pi) + 1) * (Real.log (2 + ‖s‖) + 1) / L :=
        final_estimate hB hx₀ hL0 hsge hlog1


end

end Commons.NumberTheory.DirichletCharacter
