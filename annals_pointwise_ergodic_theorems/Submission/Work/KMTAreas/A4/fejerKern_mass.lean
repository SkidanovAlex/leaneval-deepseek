import Mathlib
import Submission.Work.KMTAreas.A4.denseMultiples_kern

open MeasureTheory

/-!
# The mass of the Fejér kernel on its main window

`Work.KMTAreas.A4.fejerKern N` is the classical (mass one) Fejér kernel
`(N+1) * fejerWin N x`, whose closed form is `sin (π (N+1) x)² / ((N+1) sin (πx)²)`.

Here we prove that at least `3/4` of its mass lies on the window
`[-1/(2(N+1)), 1/(2(N+1))]`,

`3/4 ≤ ∫ x in (-(1/(2(N+1))))..(1/(2(N+1))), fejerKern N x`.

The proof is quantitative but completely elementary.  On the window we have
`|π (N+1) x| ≤ π/2`, so Taylor's inequality `sin t ≥ t - t³/6` (`Real.sin_ge_sub_cube`)
together with `sin t ≤ t` gives the pointwise bound

`fejerKern N x ≥ (N+1) * (1 - (π (N+1) x)² / 6)²`.

The right-hand side is a polynomial whose integral over the window is
`1 - π²/36 + π⁴/2880 ≈ 0.7597`, which exceeds `3/4`.
-/

namespace Work.KMTAreas.A4

noncomputable section

/-- Pointwise lower bound for the Fejér kernel on its main window: for
`|x| ≤ 1/(2(N+1))` the kernel dominates the polynomial
`(N+1) * (1 - (π (N+1) x)²/6)²`. -/
lemma fejerKern_pointwise (N : ℕ) {x : ℝ} (hx : |x| ≤ 1/(2*((N:ℝ)+1))) :
    ((N:ℝ)+1) * (1 - (Real.pi * ((N:ℝ)+1) * x)^2 / 6)^2 ≤ fejerKern N x := by
  set M : ℝ := (N:ℝ)+1 with hMdef
  have hM : 0 < M := by positivity
  have hMabs : M * |x| ≤ 1/2 := by
    have hc : (0:ℝ) < 2*M := by positivity
    have h := (le_div_iff₀ hc).mp hx
    nlinarith [abs_nonneg x]
  have habs : |Real.pi * M * x| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hM]
    calc Real.pi * M * |x| = Real.pi * (M * |x|) := by ring
      _ ≤ Real.pi * (1/2) := mul_le_mul_of_nonneg_left hMabs Real.pi_pos.le
      _ = Real.pi/2 := by ring
  rcases eq_or_ne (Real.sin (Real.pi * x)) 0 with hsin | hsin
  · have hfx : fejerKern N x = M := by
      unfold fejerKern Work.Analysis.Fourier.fejerWin
      rw [if_pos hsin, ← hMdef]
      ring
    rw [hfx]
    have hw2 : (Real.pi * M * x)^2 ≤ 12 := by
      rw [← sq_abs]
      nlinarith [habs, Real.pi_lt_four, Real.pi_pos, abs_nonneg (Real.pi*M*x)]
    have hle1 : (1 - (Real.pi*M*x)^2/6)^2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one, abs_le]
      constructor <;> nlinarith
    simpa using mul_le_mul_of_nonneg_left hle1 hM.le
  · have hxne : x ≠ 0 := by intro h0; rw [h0] at hsin; simp at hsin
    have hfx : fejerKern N x
        = (Real.sin (Real.pi*M*x))^2 / (M * (Real.sin (Real.pi*x))^2) := by
      unfold fejerKern Work.Analysis.Fourier.fejerWin
      rw [if_neg hsin, ← hMdef]
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp
    rw [hfx]
    have hnum : 0 ≤ (Real.sin (Real.pi*M*x))^2 := sq_nonneg _
    have hsin2pos : 0 < (Real.sin (Real.pi*x))^2 := sq_pos_of_ne_zero hsin
    have hden1 : 0 < M * (Real.sin (Real.pi*x))^2 := mul_pos hM hsin2pos
    have hden2 : 0 < M * (Real.pi*x)^2 :=
      mul_pos hM (sq_pos_of_ne_zero (mul_ne_zero Real.pi_ne_zero hxne))
    have hbc : M * (Real.sin (Real.pi*x))^2 ≤ M * (Real.pi*x)^2 :=
      mul_le_mul_of_nonneg_left Real.sin_sq_le_sq hM.le
    have step1 : (Real.sin (Real.pi*M*x))^2 / (M*(Real.pi*x)^2)
        ≤ (Real.sin (Real.pi*M*x))^2 / (M*(Real.sin (Real.pi*x))^2) :=
      div_le_div_of_nonneg_left hnum hden1 hbc
    have hw2 : (Real.pi*M*x)^2 ≤ 6 := by
      rw [← sq_abs]
      nlinarith [habs, Real.pi_lt_four, Real.pi_pos, abs_nonneg (Real.pi*M*x)]
    have hstep2 : (Real.pi*M*x)^2 * (1 - (Real.pi*M*x)^2/6)^2
        ≤ (Real.sin (Real.pi*M*x))^2 := by
      rcases lt_or_ge 0 (Real.pi*M*x) with hw | hw
      · have hle := Real.sin_ge_sub_cube (le_of_lt hw)
        have hnn : 0 ≤ Real.pi*M*x - (Real.pi*M*x)^3/6 := by
          have h1 : 0 ≤ Real.pi*M*x * (6 - (Real.pi*M*x)^2) :=
            mul_nonneg (le_of_lt hw) (by linarith)
          nlinarith [h1]
        calc (Real.pi*M*x)^2 * (1 - (Real.pi*M*x)^2/6)^2
            = (Real.pi*M*x - (Real.pi*M*x)^3/6)^2 := by ring
          _ ≤ (Real.sin (Real.pi*M*x))^2 := pow_le_pow_left₀ hnn hle 2
      · have hle := Real.sin_ge_sub_cube (x := -(Real.pi*M*x)) (by linarith)
        have hnn : 0 ≤ -(Real.pi*M*x) - (-(Real.pi*M*x))^3/6 := by
          have h1 : 0 ≤ -(Real.pi*M*x) * (6 - (-(Real.pi*M*x))^2) :=
            mul_nonneg (by linarith) (by nlinarith [hw2])
          nlinarith [h1]
        calc (Real.pi*M*x)^2 * (1 - (Real.pi*M*x)^2/6)^2
            = (-(Real.pi*M*x) - (-(Real.pi*M*x))^3/6)^2 := by ring
          _ ≤ (Real.sin (-(Real.pi*M*x)))^2 := pow_le_pow_left₀ hnn hle 2
          _ = (Real.sin (Real.pi*M*x))^2 := by rw [Real.sin_neg]; ring
    have hfinal : M * (1 - (Real.pi*M*x)^2/6)^2
        = (Real.pi*M*x)^2 * (1 - (Real.pi*M*x)^2/6)^2 / (M*(Real.pi*x)^2) := by
      have hM0 : M ≠ 0 := hM.ne'
      field_simp
    rw [hfinal]
    exact (div_le_div_of_nonneg_right hstep2 hden2.le).trans step1

/-- `∫ x in (-b)..b, (1 - c x²)² = 2b - (4c/3) b³ + (2c²/5) b⁵`. -/
lemma integral_one_sub_sq (b c : ℝ) :
    ∫ x in (-b)..b, (1 - c * x^2)^2 = 2*b - (4*c/3)*b^3 + (2*c^2/5)*b^5 := by
  have hderiv : ∀ x ∈ Set.uIcc (-b) b,
      HasDerivAt (fun y : ℝ => y - (2*c/3)*y^3 + (c^2/5)*y^5) ((1 - c*x^2)^2) x := by
    intro x _
    have h := ((hasDerivAt_id x).sub (((hasDerivAt_id x).pow 3).const_mul (2*c/3))).add
        (((hasDerivAt_id x).pow 5).const_mul (c^2/5))
    refine h.congr_deriv ?_
    simp only [id_eq]
    ring
  have hint : IntervalIntegrable (fun x : ℝ => (1 - c*x^2)^2) MeasureTheory.volume (-b) b := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

theorem fejerKern_mass (N : ℕ) : (3:ℝ)/4 ≤ ∫ x in (-(1/(2*((N:ℝ)+1))))..(1/(2*((N:ℝ)+1))), fejerKern N x := by
  set M : ℝ := (N:ℝ)+1 with hMdef
  have hM : 0 < M := by positivity
  have ha : (0:ℝ) < 1/(2*M) := by positivity
  have hpoint : ∀ x ∈ Set.Icc (-(1/(2*M))) (1/(2*M)),
      M * (1 - (Real.pi * M * x)^2 / 6)^2 ≤ fejerKern N x := by
    intro x hx
    exact fejerKern_pointwise N (abs_le.mpr ⟨hx.1, hx.2⟩)
  have hpoly_int : ∫ x in (-(1/(2*M)))..(1/(2*M)), M * (1 - (Real.pi*M*x)^2/6)^2
      = 1 - Real.pi^2/36 + Real.pi^4/2880 := by
    rw [show (fun x : ℝ => M * (1 - (Real.pi*M*x)^2/6)^2)
        = (fun x : ℝ => M * (1 - (Real.pi^2*M^2/6) * x^2)^2) from by
      funext x; ring]
    rw [intervalIntegral.integral_const_mul,
        integral_one_sub_sq (b := 1/(2*M)) (c := Real.pi^2*M^2/6)]
    have hM0 : M ≠ 0 := hM.ne'
    have hp0 : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  have hcont : Continuous (fun x : ℝ => fejerKern N x) := by
    have hpoly : Continuous fun θ : ℝ => Work.Analysis.Fourier.fejerPoly N θ := by
      unfold Work.Analysis.Fourier.fejerPoly
      fun_prop
    have hwin : Continuous fun θ : ℝ => Work.Analysis.Fourier.fejerWin N θ := by
      have h : Continuous fun θ : ℝ => (Work.Analysis.Fourier.fejerPoly N θ).re :=
        Complex.continuous_re.comp hpoly
      rwa [show (fun θ : ℝ => (Work.Analysis.Fourier.fejerPoly N θ).re)
          = (fun θ : ℝ => Work.Analysis.Fourier.fejerWin N θ) from by
        funext θ; rw [Work.Analysis.Fourier.fejer_poly_eq_win]; simp] at h
    unfold fejerKern
    exact continuous_const.mul hwin
  have hif : IntervalIntegrable (fun x : ℝ => fejerKern N x) volume (-(1/(2*M))) (1/(2*M)) :=
    hcont.intervalIntegrable _ _
  have hiip : IntervalIntegrable (fun x : ℝ => M * (1 - (Real.pi*M*x)^2/6)^2) volume
      (-(1/(2*M))) (1/(2*M)) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hle : -(1/(2*M)) ≤ 1/(2*M) := by linarith
  have hmono := intervalIntegral.integral_mono_on hle hiip hif hpoint
  have hnum : (3:ℝ)/4 ≤ 1 - Real.pi^2/36 + Real.pi^4/2880 := by
    have h2 : Real.pi^2 < 9.9225 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    have h3 : (9.8596:ℝ) < Real.pi^2 := by nlinarith [Real.pi_gt_d2]
    have h4 : (9.8596:ℝ)^2 < (Real.pi^2)^2 := by nlinarith [h3]
    nlinarith [h2, h4]
  calc (3:ℝ)/4 ≤ 1 - Real.pi^2/36 + Real.pi^4/2880 := hnum
    _ = ∫ x in (-(1/(2*M)))..(1/(2*M)), M * (1 - (Real.pi*M*x)^2/6)^2 := hpoly_int.symm
    _ ≤ ∫ x in (-(1/(2*M)))..(1/(2*M)), fejerKern N x := hmono
    _ = ∫ x in (-(1/(2*((N:ℝ)+1))))..(1/(2*((N:ℝ)+1))), fejerKern N x := by rfl

end

end Work.KMTAreas.A4
