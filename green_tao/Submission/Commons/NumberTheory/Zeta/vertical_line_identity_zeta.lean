import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_critical_poly
import Submission.Commons.NumberTheory.Zeta.rectBoundary_shifted_inv
import Submission.Commons.NumberTheory.Zeta.completedZeta_strip_growth_upper

open Complex MeasureTheory Filter
open scoped Real Topology BigOperators

namespace Commons.NumberTheory.Zeta

noncomputable section

/-! ## Norm computations for the Gaussian weight `g(u) = exp(u²)`

On the two vertical lines `Re u = ±1` we have `‖g(1+Iy)‖ = ‖g(-1+Iy)‖ = exp(1-y²)`,
and `‖(±1+Iy)⁻¹‖ ≤ 1`. -/

lemma norm_smoothing_one_add_mul_I (y : ℝ) :
    ‖PL.AFE.smoothingFunction (1 + (y : ℂ) * I)‖ = Real.exp (1 - y ^ 2) := by
  unfold PL.AFE.smoothingFunction
  rw [Complex.norm_exp]
  have h : ((1 + (y : ℂ) * I) ^ 2).re = 1 - y ^ 2 := by
    simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re,
      Complex.one_im]
    ring
  rw [h]

lemma norm_smoothing_neg_one_add_mul_I (y : ℝ) :
    ‖PL.AFE.smoothingFunction (-1 + (y : ℂ) * I)‖ = Real.exp (1 - y ^ 2) := by
  unfold PL.AFE.smoothingFunction
  rw [Complex.norm_exp]
  have h : ((-1 + (y : ℂ) * I) ^ 2).re = 1 - y ^ 2 := by
    simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re,
      Complex.neg_im, Complex.one_re, Complex.one_im]
    ring
  rw [h]

lemma norm_inv_one_add_mul_I_le (y : ℝ) : ‖(1 + (y : ℂ) * I)⁻¹‖ ≤ 1 := by
  rw [norm_inv]
  have hsq : ‖(1 : ℂ) + (y : ℂ) * I‖ ^ 2 = 1 + y ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simpa [pow_two, mul_comm, add_comm, add_left_comm, add_assoc] using
      (Complex.normSq_add_mul_I (1 : ℝ) y)
  have hnn : 0 ≤ ‖(1 : ℂ) + (y : ℂ) * I‖ := norm_nonneg _
  have hbig : 1 ≤ ‖(1 : ℂ) + (y : ℂ) * I‖ := by
    rw [← sq_le_sq₀ (by norm_num) hnn]
    nlinarith [hsq, sq_nonneg y]
  exact (inv_le_one₀ (lt_of_lt_of_le (by norm_num) hbig)).mpr hbig

lemma norm_inv_neg_one_add_mul_I_le (y : ℝ) : ‖(-1 + (y : ℂ) * I)⁻¹‖ ≤ 1 := by
  rw [norm_inv]
  have hsq : ‖(-1 : ℂ) + (y : ℂ) * I‖ ^ 2 = 1 + y ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simpa [pow_two, mul_comm, add_comm, add_left_comm, add_assoc] using
      (Complex.normSq_add_mul_I (-1 : ℝ) y)
  have hnn : 0 ≤ ‖(-1 : ℂ) + (y : ℂ) * I‖ := norm_nonneg _
  have hbig : 1 ≤ ‖(-1 : ℂ) + (y : ℂ) * I‖ := by
    rw [← sq_le_sq₀ (by norm_num) hnn]
    nlinarith [hsq, sq_nonneg y]
  exact (inv_le_one₀ (lt_of_lt_of_le (by norm_num) hbig)).mpr hbig

/-! ## Boundedness and polynomial growth of `Λ` on vertical lines -/

lemma term_norm_zeta (z : ℂ) (hzr : z.re ≠ 0) (n : ℕ) :
    ‖(1:ℂ) / ((n:ℕ):ℂ)^z‖ = ((n:ℕ):ℝ)^(-z.re) := by
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    have hz0 : z ≠ 0 := by intro h; apply hzr; rw [h]; simp
    have hc : ((0:ℕ):ℂ) = (0:ℂ) := by norm_num
    rw [hc, zero_cpow hz0, div_zero, norm_zero]
    have hzr' : -z.re ≠ 0 := by simpa using hzr
    show (0:ℝ) = ((0:ℕ):ℝ)^(-z.re)
    rw [show ((0:ℕ):ℝ) = (0:ℝ) by norm_num]
    exact (Real.zero_rpow hzr').symm
  · have hnpos : (0:ℝ) < ((n:ℕ):ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hcast : ((n:ℕ):ℂ) = ((((n:ℕ):ℝ)):ℂ) := by norm_cast
    rw [norm_div, norm_one, hcast, Complex.norm_cpow_eq_rpow_re_of_pos hnpos, one_div,
      ← Real.rpow_neg (le_of_lt hnpos)]

lemma norm_riemannZeta_le_tsum (z : ℂ) (hz : 1 < z.re) :
    ‖riemannZeta z‖ ≤ ∑' n : ℕ, ((n:ℕ):ℝ)^(-z.re) := by
  have hzr : z.re ≠ 0 := by linarith
  have hsummable : Summable (fun n : ℕ => ‖(1:ℂ) / ((n:ℕ):ℂ)^z‖) := by
    have h2 : Summable (fun n : ℕ => ((n:ℕ):ℝ)^(-z.re)) :=
      Real.summable_nat_rpow.mpr (by linarith : -z.re < -1)
    exact h2.congr (fun n => (term_norm_zeta z hzr n).symm)
  rw [zeta_eq_tsum_one_div_nat_cpow hz]
  calc ‖∑' n : ℕ, (1:ℂ)/((n:ℕ):ℂ)^z‖ ≤ ∑' n : ℕ, ‖(1:ℂ)/((n:ℕ):ℂ)^z‖ := norm_tsum_le_tsum_norm hsummable
    _ = ∑' n : ℕ, ((n:ℕ):ℝ)^(-z.re) := tsum_congr (fun n => term_norm_zeta z hzr n)

lemma norm_completedRiemannZeta_vertical_right_le (σ : ℝ) (hσ1 : 1 < σ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, ‖completedRiemannZeta ((σ:ℂ) + (t:ℂ)*I)‖ ≤ B := by
  let S : ℝ := ∑' n : ℕ, ((n:ℕ):ℝ)^(-σ)
  have hS0 : 0 ≤ S := tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  refine ⟨‖(σ:ℂ).Gammaℝ‖ * S, by positivity, ?_⟩
  intro t
  set z : ℂ := (σ:ℂ) + (t:ℂ)*I with hz
  have hzre : z.re = σ := by simp [hz]
  have hzpos : 0 < z.re := by rw [hzre]; linarith
  have hz0 : z ≠ 0 := by intro h; rw [h] at hzpos; simp at hzpos
  have hLam : completedRiemannZeta z = z.Gammaℝ * riemannZeta z := by
    have hG : z.Gammaℝ ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hzpos
    rw [riemannZeta_def_of_ne_zero hz0]
    field_simp
  calc ‖completedRiemannZeta z‖ = ‖z.Gammaℝ‖ * ‖riemannZeta z‖ := by rw [hLam, norm_mul]
    _ ≤ ‖(σ:ℂ).Gammaℝ‖ * S := by
        apply mul_le_mul
        · simpa only [hzre] using PL.GammaVertical.norm_Gammaℝ_le_norm_Gammaℝ_re z hzpos
        · simpa only [hzre] using norm_riemannZeta_le_tsum z (by rw [hzre]; linarith)
        · positivity
        · positivity

lemma norm_completedRiemannZeta_vertical_left_le (σ : ℝ) (hσ1 : σ < 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, ‖completedRiemannZeta ((σ:ℂ) + (t:ℂ)*I)‖ ≤ B := by
  rcases norm_completedRiemannZeta_vertical_right_le (1 - σ) (by linarith) with ⟨B, hB0, hB⟩
  refine ⟨B, hB0, ?_⟩
  intro t
  have hΛ : completedRiemannZeta ((σ:ℂ) + (t:ℂ)*I)
      = completedRiemannZeta ((((1-σ):ℝ):ℂ) + (((-t):ℝ):ℂ)*I) := by
    have h : (σ:ℂ) + (t:ℂ)*I = 1 - ((((1-σ):ℝ):ℂ) + (((-t):ℝ):ℂ)*I) := by
      apply Complex.ext <;> simp <;> ring
    calc completedRiemannZeta ((σ:ℂ) + (t:ℂ)*I)
        = completedRiemannZeta (1 - ((((1-σ):ℝ):ℂ) + (((-t):ℝ):ℂ)*I)) := by rw [h]
      _ = completedRiemannZeta ((((1-σ):ℝ):ℂ) + (((-t):ℝ):ℂ)*I) := completedRiemannZeta_one_sub _
  rw [hΛ]
  exact hB (-t)

lemma completedRiemannZeta_strip_poly_of_pos
    (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hC₀spec : ∀ σ t : ℝ, 0 < σ → σ ≤ 2 → 2 ≤ |t| →
      ‖(1 / 2 : ℂ) * ((σ:ℂ)+(t:ℂ)*I) * (((σ:ℂ)+(t:ℂ)*I) - 1)
          * completedRiemannZeta ((σ:ℂ)+(t:ℂ)*I)‖
        ≤ C₀ * (|t| + 3) ^ 7 * Real.exp (-(Real.pi / 4) * |t|))
    (σ t : ℝ) (hσ0 : 0 < σ) (hσ2 : σ < 2) (ht : 2 ≤ |t|) :
    ‖completedRiemannZeta ((σ:ℂ) + (t:ℂ)*I)‖ ≤ C₀ * (|t| + 3) ^ 7 := by
  set z : ℂ := (σ:ℂ) + (t:ℂ)*I with hz
  have hzim : z.im = t := by simp [hz]
  have hnorm : ‖(1/2:ℂ) * z * (z-1) * completedRiemannZeta z‖
      = (1/2) * ‖z‖ * ‖z-1‖ * ‖completedRiemannZeta z‖ := by
    rw [norm_mul, norm_mul, norm_mul]; norm_num
  have hz2 : 2 ≤ ‖z‖ := by
    have := Complex.abs_im_le_norm z; rw [hzim] at this; linarith
  have hz12 : 2 ≤ ‖z - 1‖ := by
    have h1 : (z-1).im = t := by simp [hz]
    have := Complex.abs_im_le_norm (z-1); rw [h1] at this; linarith
  have hprod : (1/2) * ‖z‖ * ‖z-1‖ ≥ 2 := by nlinarith [hz2, hz12]
  have hkey : 2 * ‖completedRiemannZeta z‖ ≤ ‖(1/2:ℂ) * z * (z-1) * completedRiemannZeta z‖ := by
    rw [hnorm]
    calc 2 * ‖completedRiemannZeta z‖ ≤ ((1/2) * ‖z‖ * ‖z-1‖) * ‖completedRiemannZeta z‖ :=
          mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
      _ = (1/2) * ‖z‖ * ‖z-1‖ * ‖completedRiemannZeta z‖ := by ring
  have he : Real.exp (-(Real.pi/4) * |t|) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [abs_nonneg t, Real.pi_pos]
  have hb := hC₀spec σ t hσ0 (le_of_lt hσ2) ht
  have hb' : ‖(1/2:ℂ) * z * (z-1) * completedRiemannZeta z‖ ≤ C₀ * (|t|+3)^7 := by
    have h1 : ‖(1/2:ℂ) * z * (z-1) * completedRiemannZeta z‖
        = ‖(fun s : ℂ => (1/2:ℂ)*s*(s-1)*completedRiemannZeta s) ((σ:ℂ)+(t:ℂ)*I)‖ := by
      rw [hz]
    rw [h1]
    calc ‖(fun s : ℂ => (1/2:ℂ)*s*(s-1)*completedRiemannZeta s) ((σ:ℂ)+(t:ℂ)*I)‖
        ≤ C₀ * (|t|+3)^7 * Real.exp (-(Real.pi/4)*|t|) := hb
      _ ≤ C₀ * (|t|+3)^7 := by
          have hc0 : 0 ≤ C₀ * (|t|+3)^7 := by positivity
          nlinarith [he, hc0, Real.exp_pos (-(Real.pi/4)*|t|)]
  have hfin : 0 ≤ C₀ * (|t|+3)^7 := by positivity
  calc ‖completedRiemannZeta z‖ = (1/2) * (2 * ‖completedRiemannZeta z‖) := by ring
    _ ≤ (1/2) * ‖(1/2:ℂ) * z * (z-1) * completedRiemannZeta z‖ := by linarith
    _ ≤ (1/2) * (C₀ * (|t|+3)^7) := by linarith
    _ ≤ C₀ * (|t|+3)^7 := by linarith

lemma exists_completedRiemannZeta_strip_poly :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, -1 < σ → σ < 2 → 2 ≤ |t| →
      ‖completedRiemannZeta ((σ:ℂ) + (t:ℂ)*I)‖ ≤ C * (|t| + 3) ^ 7 := by
  rcases Commons.NumberTheory.Zeta.completedZeta_strip_growth_upper with ⟨C₀, hC₀, hspec⟩
  refine ⟨C₀, hC₀, ?_⟩
  intro σ t h0 h2 ht
  by_cases hσpos : 0 < σ
  · exact completedRiemannZeta_strip_poly_of_pos C₀ hC₀ hspec σ t hσpos h2 ht
  · push_neg at hσpos
    have hΛ : completedRiemannZeta ((σ:ℂ) + (t:ℂ)*I)
        = completedRiemannZeta ((((1-σ):ℝ):ℂ) + (((-t):ℝ):ℂ)*I) := by
      have h : (σ:ℂ) + (t:ℂ)*I = 1 - ((((1-σ):ℝ):ℂ) + (((-t):ℝ):ℂ)*I) := by
        apply Complex.ext <;> simp <;> ring
      calc completedRiemannZeta ((σ:ℂ) + (t:ℂ)*I)
          = completedRiemannZeta (1 - ((((1-σ):ℝ):ℂ) + (((-t):ℝ):ℂ)*I)) := by rw [h]
        _ = completedRiemannZeta ((((1-σ):ℝ):ℂ) + (((-t):ℝ):ℂ)*I) := completedRiemannZeta_one_sub _
    rw [hΛ]
    have h1 : 0 < 1 - σ := by linarith [hσpos]
    have h2' : 1 - σ < 2 := by linarith [hσpos]
    have h3 : 2 ≤ |(-t)| := by simpa using ht
    have hb := completedRiemannZeta_strip_poly_of_pos C₀ hC₀ hspec (1-σ) (-t) h1 h2' h3
    simpa using hb



/-- The Mellin integrand `K(u) = Λ(s+u)·g(u)/u`. -/
def zetaK (s : ℂ) (u : ℂ) : ℂ :=
  completedRiemannZeta (s + u) * PL.AFE.smoothingFunction u / u

/-- `K` on the right vertical line `Re u = 1`. -/
def zetaLineR (s : ℂ) (y : ℝ) : ℂ :=
  completedRiemannZeta (s + 1 + (y : ℂ) * I) * PL.AFE.smoothingFunction (1 + (y : ℂ) * I)
    * (1 + (y : ℂ) * I)⁻¹

/-- `K` on the left vertical line `Re u = -1`. -/
def zetaLineL (s : ℂ) (y : ℝ) : ℂ :=
  completedRiemannZeta (s - 1 + (y : ℂ) * I) * PL.AFE.smoothingFunction (-1 + (y : ℂ) * I)
    * (-1 + (y : ℂ) * I)⁻¹

/-- `K` on a horizontal segment `u = x ± iT`. -/
def zetaHoriz (s : ℂ) (T x : ℝ) : ℂ :=
  completedRiemannZeta (s + ((x : ℂ) + (T : ℂ) * I))
    * PL.AFE.smoothingFunction ((x : ℂ) + (T : ℂ) * I) * ((x : ℂ) + (T : ℂ) * I)⁻¹

lemma zetaLineR_eq_zetaK (s : ℂ) (y : ℝ) : zetaLineR s y = zetaK s (1 + (y : ℂ) * I) := by
  simp only [zetaLineR, zetaK, div_eq_mul_inv]
  rw [show s + 1 + (y : ℂ) * I = s + (1 + (y : ℂ) * I) by ring]

lemma zetaLineL_eq_zetaK (s : ℂ) (y : ℝ) : zetaLineL s y = zetaK s (-1 + (y : ℂ) * I) := by
  simp only [zetaLineL, zetaK, div_eq_mul_inv]
  rw [show s - 1 + (y : ℂ) * I = s + (-1 + (y : ℂ) * I) by ring]

lemma zetaHoriz_eq_zetaK (s : ℂ) (T x : ℝ) :
    zetaHoriz s T x = zetaK s ((x : ℂ) + (T : ℂ) * I) := by
  simp only [zetaHoriz, zetaK, div_eq_mul_inv]

/-! ### Continuity and integrability of the vertical-line integrands -/

lemma continuous_zetaLineR (s : ℂ) (hs1 : s.re ≠ -1) (hs0 : s.re ≠ 0) :
    Continuous (fun y : ℝ => zetaLineR s y) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hne0 : s + 1 + (y : ℂ) * I ≠ 0 := by
    intro h
    exact hs1 (by have := congrArg Complex.re h; simp at this; linarith [this])
  have hne1 : s + 1 + (y : ℂ) * I ≠ 1 := by
    intro h
    exact hs0 (by have := congrArg Complex.re h; simp at this; linarith [this])
  have hd : DifferentiableAt ℂ completedRiemannZeta (s + 1 + (y : ℂ) * I) :=
    differentiableAt_completedZeta hne0 hne1
  have h1 : ContinuousAt (fun y : ℝ => completedRiemannZeta (s + 1 + (y : ℂ) * I)) y := by
    apply ContinuousAt.comp
    · exact hd.continuousAt
    · fun_prop
  have h2 : ContinuousAt (fun y : ℝ => PL.AFE.smoothingFunction (1 + (y : ℂ) * I)) y := by
    unfold PL.AFE.smoothingFunction
    apply ContinuousAt.comp
    · exact Complex.continuous_exp.continuousAt
    · fun_prop
  have h3 : ContinuousAt (fun y : ℝ => (1 + (y : ℂ) * I)⁻¹) y := by
    refine ContinuousAt.inv₀ (by fun_prop) ?_
    intro h
    have := congrArg Complex.re h; simp at this
  exact (h1.mul h2).mul h3

lemma continuous_zetaLineL (s : ℂ) (hs1 : s.re ≠ 1) (hs2 : s.re ≠ 2) :
    Continuous (fun y : ℝ => zetaLineL s y) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hne0 : s - 1 + (y : ℂ) * I ≠ 0 := by
    intro h
    exact hs1 (by have := congrArg Complex.re h; simp at this; linarith [this])
  have hne1 : s - 1 + (y : ℂ) * I ≠ 1 := by
    intro h
    exact hs2 (by have := congrArg Complex.re h; simp at this; linarith [this])
  have hd : DifferentiableAt ℂ completedRiemannZeta (s - 1 + (y : ℂ) * I) :=
    differentiableAt_completedZeta hne0 hne1
  have h1 : ContinuousAt (fun y : ℝ => completedRiemannZeta (s - 1 + (y : ℂ) * I)) y := by
    apply ContinuousAt.comp
    · exact hd.continuousAt
    · fun_prop
  have h2 : ContinuousAt (fun y : ℝ => PL.AFE.smoothingFunction (-1 + (y : ℂ) * I)) y := by
    unfold PL.AFE.smoothingFunction
    apply ContinuousAt.comp
    · exact Complex.continuous_exp.continuousAt
    · fun_prop
  have h3 : ContinuousAt (fun y : ℝ => (-1 + (y : ℂ) * I)⁻¹) y := by
    refine ContinuousAt.inv₀ (by fun_prop) ?_
    intro h
    have := congrArg Complex.re h; simp at this
  exact (h1.mul h2).mul h3

lemma integrable_zetaLineR (s : ℂ) (hs0 : 0 < s.re) :
    Integrable (fun y : ℝ => zetaLineR s y) := by
  rcases norm_completedRiemannZeta_vertical_right_le (s.re + 1) (by linarith) with ⟨B, hB0, hB⟩
  have hbound : ∀ y : ℝ, ‖zetaLineR s y‖ ≤ B * Real.exp 1 * Real.exp (-(y ^ 2)) := by
    intro y
    have harg : s + 1 + (y : ℂ) * I = (((s.re + 1 : ℝ)):ℂ) + (((s.im + y : ℝ)):ℂ) * I := by
      apply Complex.ext <;> simp <;> ring
    have hΛ : ‖completedRiemannZeta (s + 1 + (y : ℂ) * I)‖ ≤ B := by
      rw [harg]; exact hB (s.im + y)
    have hg := norm_smoothing_one_add_mul_I y
    have hi := norm_inv_one_add_mul_I_le y
    calc ‖zetaLineR s y‖
        = ‖completedRiemannZeta (s + 1 + (y : ℂ) * I)‖
            * ‖PL.AFE.smoothingFunction (1 + (y : ℂ) * I)‖ * ‖(1 + (y : ℂ) * I)⁻¹‖ := by
          simp only [zetaLineR, norm_mul]
      _ ≤ B * Real.exp (1 - y ^ 2) * 1 := by rw [hg]; gcongr
      _ = B * Real.exp 1 * Real.exp (-(y ^ 2)) := by
          have he : (1 - y ^ 2 : ℝ) = 1 + (-(y ^ 2)) := by ring
          rw [he, Real.exp_add]; ring
  have hInt : Integrable (fun y : ℝ => B * Real.exp 1 * Real.exp (-(y ^ 2))) := by
    have hbase : Integrable (fun y : ℝ => Real.exp (-(y ^ 2))) := by
      have h := integrable_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num)
      simpa using h
    exact hbase.const_mul (B * Real.exp 1)
  exact Integrable.mono' hInt (continuous_zetaLineR s (by linarith) (by linarith)).aestronglyMeasurable
    (ae_of_all _ hbound)

lemma integrable_zetaLineL (s : ℂ) (hs1 : s.re < 1) :
    Integrable (fun y : ℝ => zetaLineL s y) := by
  rcases norm_completedRiemannZeta_vertical_left_le (s.re - 1) (by linarith) with ⟨B, hB0, hB⟩
  have hbound : ∀ y : ℝ, ‖zetaLineL s y‖ ≤ B * Real.exp 1 * Real.exp (-(y ^ 2)) := by
    intro y
    have harg : s - 1 + (y : ℂ) * I = (((s.re - 1 : ℝ)):ℂ) + (((s.im + y : ℝ)):ℂ) * I := by
      apply Complex.ext <;> simp <;> ring
    have hΛ : ‖completedRiemannZeta (s - 1 + (y : ℂ) * I)‖ ≤ B := by
      rw [harg]; exact hB (s.im + y)
    have hg := norm_smoothing_neg_one_add_mul_I y
    have hi := norm_inv_neg_one_add_mul_I_le y
    calc ‖zetaLineL s y‖
        = ‖completedRiemannZeta (s - 1 + (y : ℂ) * I)‖
            * ‖PL.AFE.smoothingFunction (-1 + (y : ℂ) * I)‖ * ‖(-1 + (y : ℂ) * I)⁻¹‖ := by
          simp only [zetaLineL, norm_mul]
      _ ≤ B * Real.exp (1 - y ^ 2) * 1 := by rw [hg]; gcongr
      _ = B * Real.exp 1 * Real.exp (-(y ^ 2)) := by
          have he : (1 - y ^ 2 : ℝ) = 1 + (-(y ^ 2)) := by ring
          rw [he, Real.exp_add]; ring
  have hInt : Integrable (fun y : ℝ => B * Real.exp 1 * Real.exp (-(y ^ 2))) := by
    have hbase : Integrable (fun y : ℝ => Real.exp (-(y ^ 2))) := by
      have h := integrable_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num)
      simpa using h
    exact hbase.const_mul (B * Real.exp 1)
  exact Integrable.mono' hInt (continuous_zetaLineL s (by linarith) (by linarith)).aestronglyMeasurable
    (ae_of_all _ hbound)

lemma tendsto_truncated_zetaLineR (s : ℂ) (hs0 : 0 < s.re) :
    Tendsto (fun T : ℝ => ∫ y : ℝ in -T..T, zetaLineR s y) atTop
      (𝓝 (∫ y : ℝ, zetaLineR s y)) :=
  PL.VertLimit.tendsto_interval_vertical _ (integrable_zetaLineR s hs0)

lemma tendsto_truncated_zetaLineL (s : ℂ) (hs1 : s.re < 1) :
    Tendsto (fun T : ℝ => ∫ y : ℝ in -T..T, zetaLineL s y) atTop
      (𝓝 (∫ y : ℝ, zetaLineL s y)) :=
  PL.VertLimit.tendsto_interval_vertical _ (integrable_zetaLineL s hs1)



/-! ### Decay of `x^p * exp(-x²)` and the horizontal-edge bound -/

lemma tendsto_shifted_pow_exp_neg_sq (c : ℝ) :
    Tendsto (fun T : ℝ => (T + c) ^ 7 * Real.exp (-(T ^ 2))) atTop (𝓝 0) := by
  have hsqtop : Tendsto (fun T : ℝ => T ^ 2) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨max b 0 + 1, fun a ha => ?_⟩
    have hb : b ≤ max b 0 := le_max_left _ _
    have ha1 : 1 ≤ a := by nlinarith [le_max_left b 0, le_max_right b 0]
    nlinarith [sq_nonneg (a - 1), hb]
  have h4 : Tendsto (fun T : ℝ => (T ^ 2) ^ 4 * Real.exp (-(T ^ 2))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).comp hsqtop
  have hg : Tendsto (fun T : ℝ => 128 * ((T ^ 2) ^ 4 * Real.exp (-(T ^ 2)))) atTop (𝓝 0) := by
    simpa using h4.const_mul 128
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [eventually_ge_atTop (|c| + 1)] with T hT
    have h0 : 0 ≤ T + c := by nlinarith [neg_abs_le c, abs_nonneg c]
    positivity
  · filter_upwards [eventually_ge_atTop (|c| + 1)] with T hT
    have h1 : 1 ≤ T := by nlinarith [abs_nonneg c]
    have htc : T + c ≤ 2 * T := by nlinarith [le_abs_self c, abs_nonneg c]
    have h0 : 0 ≤ T + c := by nlinarith [neg_abs_le c]
    have hpow : (T + c) ^ 7 ≤ 128 * T ^ 8 := by
      have h2 : (T + c) ^ 7 ≤ (2 * T) ^ 7 := pow_le_pow_left₀ h0 htc 7
      have h3 : (2 * T) ^ 7 = 128 * T ^ 7 := by ring
      have h4' : T ^ 7 ≤ T ^ 8 := by
        calc T ^ 7 = T ^ 7 * 1 := by ring
          _ ≤ T ^ 7 * T := by exact mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = T ^ 8 := by ring
      calc (T + c) ^ 7 ≤ (2 * T) ^ 7 := h2
        _ = 128 * T ^ 7 := h3
        _ ≤ 128 * T ^ 8 := by linarith
    calc (T + c) ^ 7 * Real.exp (-(T ^ 2)) ≤ 128 * T ^ 8 * Real.exp (-(T ^ 2)) :=
          mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
      _ = 128 * ((T ^ 2) ^ 4 * Real.exp (-(T ^ 2))) := by ring

lemma zetaHoriz_norm_le (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T x : ℝ, 2 + |s.im| ≤ |T| → |x| ≤ 1 →
      ‖zetaHoriz s T x‖ ≤ C * (|T| + |s.im| + 3) ^ 7 * Real.exp (-(T ^ 2)) := by
  rcases exists_completedRiemannZeta_strip_poly with ⟨C, hC, hCs⟩
  refine ⟨C * Real.exp 1, by positivity, ?_⟩
  intro T x hT hx
  set u : ℂ := (x : ℂ) + (T : ℂ) * I with hu
  have hure : u.re = x := by simp [hu]
  have huim : u.im = T := by simp [hu]
  have hσre : (s + u).re = s.re + x := by rw [Complex.add_re, hure]
  have hσim : (s + u).im = s.im + T := by rw [Complex.add_im, huim]
  have h1 : -1 < (s + u).re := by rw [hσre]; linarith [(abs_le.mp hx).1, hs0]
  have h2 : (s + u).re < 2 := by rw [hσre]; linarith [(abs_le.mp hx).2, hs1]
  have h3 : 2 ≤ |(s + u).im| := by
    rw [hσim]
    have hTle : |T| ≤ |s.im + T| + |s.im| := by
      calc |T| = |(s.im + T) + (-s.im)| := by ring_nf
        _ ≤ |s.im + T| + |-s.im| := abs_add_le _ _
        _ = |s.im + T| + |s.im| := by rw [abs_neg]
    linarith [hTle, hT]
  have hΛb := hCs (s + u).re (s + u).im h1 h2 h3
  have hΛ : ‖completedRiemannZeta (s + u)‖ ≤ C * (|T| + |s.im| + 3) ^ 7 := by
    have hrew : (((s + u).re : ℝ) : ℂ) + (((s + u).im : ℝ) : ℂ) * I = s + u := by
      apply Complex.ext <;> simp
    rw [hrew] at hΛb
    refine le_trans hΛb (mul_le_mul_of_nonneg_left ?_ hC.le)
    apply pow_le_pow_left₀ (by positivity)
    rw [hσim]
    have hab : |s.im + T| ≤ |s.im| + |T| := abs_add_le s.im T
    linarith [hab]
  have hgn : ‖PL.AFE.smoothingFunction u‖ ≤ Real.exp 1 * Real.exp (-(T ^ 2)) := by
    have hge : ‖PL.AFE.smoothingFunction u‖ = Real.exp (x ^ 2 - T ^ 2) := by
      unfold PL.AFE.smoothingFunction
      rw [Complex.norm_exp]
      have hre : (u ^ 2).re = x ^ 2 - T ^ 2 := by
        simp only [hu, pow_two, Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        ring
      rw [hre]
    rw [hge]
    have hle : x ^ 2 - T ^ 2 ≤ 1 - T ^ 2 := by nlinarith [(abs_le.mp hx).1, (abs_le.mp hx).2]
    have he : (1 - T ^ 2 : ℝ) = 1 + (-(T ^ 2)) := by ring
    calc Real.exp (x ^ 2 - T ^ 2) ≤ Real.exp (1 - T ^ 2) := Real.exp_le_exp.mpr hle
      _ = Real.exp 1 * Real.exp (-(T ^ 2)) := by rw [he, Real.exp_add]
  have hinn : ‖u⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    have hsq : ‖u‖ ^ 2 = x ^ 2 + T ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, hu]
      simpa using Complex.normSq_add_mul_I x T
    have hsqT : 4 ≤ T ^ 2 := by
      have h2' : 2 ≤ |T| := by linarith [hT, abs_nonneg s.im]
      have hsq' : |T| ^ 2 = T ^ 2 := sq_abs T
      nlinarith [h2', hsq', abs_nonneg T]
    have hge1 : 1 ≤ ‖u‖ := by
      have h2u : 2 ≤ ‖u‖ := by nlinarith [hsq, norm_nonneg u, hsqT, sq_nonneg x]
      linarith
    exact (inv_le_one₀ (lt_of_lt_of_le (by norm_num) hge1)).mpr hge1
  calc ‖zetaHoriz s T x‖
      = ‖completedRiemannZeta (s + u)‖ * ‖PL.AFE.smoothingFunction u‖ * ‖u⁻¹‖ := by
        simp only [zetaHoriz, hu, norm_mul]
    _ ≤ (C * (|T| + |s.im| + 3) ^ 7) * (Real.exp 1 * Real.exp (-(T ^ 2))) * 1 := by gcongr
    _ = C * Real.exp 1 * (|T| + |s.im| + 3) ^ 7 * Real.exp (-(T ^ 2)) := by ring

lemma tendsto_zetaHoriz_id (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in (-1)..1, zetaHoriz s T x) atTop (𝓝 0) := by
  rcases zetaHoriz_norm_le s hs0 hs1 with ⟨C, hC, hCb⟩
  have hupper : Tendsto (fun T : ℝ => (2 * C) * ((T + (|s.im| + 3)) ^ 7 * Real.exp (-(T ^ 2))))
      atTop (𝓝 0) := by
    simpa using (tendsto_shifted_pow_exp_neg_sq (|s.im| + 3)).const_mul (2 * C)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall (fun T => norm_nonneg _)) ?_ hupper
  filter_upwards [eventually_ge_atTop (2 + |s.im|), eventually_ge_atTop 0] with T hT hT0
  have habs : |T| = T := abs_of_nonneg hT0
  have hb : ‖∫ x : ℝ in (-1)..1, zetaHoriz s T x‖
      ≤ (C * (|T| + |s.im| + 3) ^ 7 * Real.exp (-(T ^ 2))) * |(1 : ℝ) - (-1)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    have hx' : |x| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
    exact hCb T x (by rw [habs]; exact hT) hx'
  calc ‖∫ x : ℝ in (-1)..1, zetaHoriz s T x‖
      ≤ (C * (|T| + |s.im| + 3) ^ 7 * Real.exp (-(T ^ 2))) * |(1 : ℝ) - (-1)| := hb
    _ = (2 * C) * ((T + (|s.im| + 3)) ^ 7 * Real.exp (-(T ^ 2))) := by rw [habs]; norm_num; ring

lemma tendsto_zetaHoriz_neg (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in (-1)..1, zetaHoriz s (-T) x) atTop (𝓝 0) := by
  rcases zetaHoriz_norm_le s hs0 hs1 with ⟨C, hC, hCb⟩
  have hupper : Tendsto (fun T : ℝ => (2 * C) * ((T + (|s.im| + 3)) ^ 7 * Real.exp (-(T ^ 2))))
      atTop (𝓝 0) := by
    simpa using (tendsto_shifted_pow_exp_neg_sq (|s.im| + 3)).const_mul (2 * C)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall (fun T => norm_nonneg _)) ?_ hupper
  filter_upwards [eventually_ge_atTop (2 + |s.im|), eventually_ge_atTop 0] with T hT hT0
  have habs : |(-T)| = T := by rw [abs_neg, abs_of_nonneg hT0]
  have hb : ‖∫ x : ℝ in (-1)..1, zetaHoriz s (-T) x‖
      ≤ (C * (|(-T)| + |s.im| + 3) ^ 7 * Real.exp (-((-T) ^ 2))) * |(1 : ℝ) - (-1)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    have hx' : |x| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
    exact hCb (-T) x (by rw [habs]; exact hT) hx'
  calc ‖∫ x : ℝ in (-1)..1, zetaHoriz s (-T) x‖
      ≤ (C * (|(-T)| + |s.im| + 3) ^ 7 * Real.exp (-((-T) ^ 2))) * |(1 : ℝ) - (-1)| := hb
    _ = (2 * C) * ((T + (|s.im| + 3)) ^ 7 * Real.exp (-(T ^ 2))) := by rw [habs]; ring


def rectEdge (T : ℝ) : Set ℂ :=
  {u : ℂ | (u.re = -1 ∨ u.re = 1) ∧ |u.im| ≤ T}
    ∪ {u : ℂ | (u.im = -T ∨ u.im = T) ∧ |u.re| ≤ 1}

lemma rectEdge_bot (T : ℝ) : Set.MapsTo (fun x : ℝ => (x : ℂ) + (⟨-1, -T⟩ : ℂ).im * I)
    (Set.uIcc (-1) 1) (rectEdge T) := by
  intro x hx
  rw [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)] at hx
  right
  constructor
  · simp
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      sub_zero, Complex.ofReal_im, Complex.I_im, mul_one, add_zero]
    rw [abs_le]; exact ⟨hx.1, hx.2⟩

lemma rectEdge_top (T : ℝ) : Set.MapsTo (fun x : ℝ => (x : ℂ) + (⟨1, T⟩ : ℂ).im * I)
    (Set.uIcc (-1) 1) (rectEdge T) := by
  intro x hx
  rw [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)] at hx
  right
  constructor
  · simp
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      sub_zero, Complex.mul_im, Complex.ofReal_im, Complex.I_im, mul_one, add_zero]
    rw [abs_le]; exact ⟨hx.1, hx.2⟩

lemma rectEdge_right (T : ℝ) (hT : 0 < T) :
    Set.MapsTo (fun y : ℝ => (((⟨1, T⟩ : ℂ).re : ℝ) : ℂ) + (y : ℂ) * I)
    (Set.uIcc (-T) T) (rectEdge T) := by
  intro y hy
  rw [Set.uIcc_of_le (by linarith : -T ≤ T)] at hy
  left
  constructor
  · simp
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, mul_one,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero, add_zero, zero_add]
    rw [abs_le]; exact ⟨hy.1, hy.2⟩

lemma rectEdge_left (T : ℝ) (hT : 0 < T) :
    Set.MapsTo (fun y : ℝ => (((⟨-1, -T⟩ : ℂ).re : ℝ) : ℂ) + (y : ℂ) * I)
    (Set.uIcc (-T) T) (rectEdge T) := by
  intro y hy
  rw [Set.uIcc_of_le (by linarith : -T ≤ T)] at hy
  left
  constructor
  · simp
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, mul_one,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero, add_zero, zero_add]
    rw [abs_le]; exact ⟨hy.1, hy.2⟩

lemma rectBoundary_add (T : ℝ) (hT : 0 < T) (f g : ℂ → ℂ)
    (hf : ContinuousOn f (rectEdge T)) (hg : ContinuousOn g (rectEdge T)) :
    PL.AfeRect.rectBoundary (⟨-1,-T⟩ : ℂ) (⟨1,T⟩ : ℂ) (f + g)
      = PL.AfeRect.rectBoundary (⟨-1,-T⟩ : ℂ) (⟨1,T⟩ : ℂ) f
        + PL.AfeRect.rectBoundary (⟨-1,-T⟩ : ℂ) (⟨1,T⟩ : ℂ) g := by
  have hb_f : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (⟨-1,-T⟩ : ℂ).im * I)) volume (-1) 1 :=
    (hf.comp (by fun_prop : ContinuousOn (fun x : ℝ => (x : ℂ) + (⟨-1,-T⟩ : ℂ).im * I) (Set.uIcc (-1) 1)) (rectEdge_bot T)).intervalIntegrable
  have hb_g : IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + (⟨-1,-T⟩ : ℂ).im * I)) volume (-1) 1 :=
    (hg.comp (by fun_prop : ContinuousOn (fun x : ℝ => (x : ℂ) + (⟨-1,-T⟩ : ℂ).im * I) (Set.uIcc (-1) 1)) (rectEdge_bot T)).intervalIntegrable
  have ht_f : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (⟨1,T⟩ : ℂ).im * I)) volume (-1) 1 :=
    (hf.comp (by fun_prop : ContinuousOn (fun x : ℝ => (x : ℂ) + (⟨1,T⟩ : ℂ).im * I) (Set.uIcc (-1) 1)) (rectEdge_top T)).intervalIntegrable
  have ht_g : IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + (⟨1,T⟩ : ℂ).im * I)) volume (-1) 1 :=
    (hg.comp (by fun_prop : ContinuousOn (fun x : ℝ => (x : ℂ) + (⟨1,T⟩ : ℂ).im * I) (Set.uIcc (-1) 1)) (rectEdge_top T)).intervalIntegrable
  have hr_f : IntervalIntegrable (fun y : ℝ => f (Complex.re (⟨1,T⟩ : ℂ) + y * I)) volume (-T) T :=
    (hf.comp (by fun_prop : ContinuousOn (fun y : ℝ => (((⟨1,T⟩ : ℂ).re : ℝ) : ℂ) + (y : ℂ) * I) (Set.uIcc (-T) T)) (rectEdge_right T hT)).intervalIntegrable
  have hr_g : IntervalIntegrable (fun y : ℝ => g (Complex.re (⟨1,T⟩ : ℂ) + y * I)) volume (-T) T :=
    (hg.comp (by fun_prop : ContinuousOn (fun y : ℝ => (((⟨1,T⟩ : ℂ).re : ℝ) : ℂ) + (y : ℂ) * I) (Set.uIcc (-T) T)) (rectEdge_right T hT)).intervalIntegrable
  have hl_f : IntervalIntegrable (fun y : ℝ => f (Complex.re (⟨-1,-T⟩ : ℂ) + y * I)) volume (-T) T :=
    (hf.comp (by fun_prop : ContinuousOn (fun y : ℝ => (((⟨-1,-T⟩ : ℂ).re : ℝ) : ℂ) + (y : ℂ) * I) (Set.uIcc (-T) T)) (rectEdge_left T hT)).intervalIntegrable
  have hl_g : IntervalIntegrable (fun y : ℝ => g (Complex.re (⟨-1,-T⟩ : ℂ) + y * I)) volume (-T) T :=
    (hg.comp (by fun_prop : ContinuousOn (fun y : ℝ => (((⟨-1,-T⟩ : ℂ).re : ℝ) : ℂ) + (y : ℂ) * I) (Set.uIcc (-T) T)) (rectEdge_left T hT)).intervalIntegrable
  unfold PL.AfeRect.rectBoundary
  simp only [Pi.add_apply]
  rw [intervalIntegral.integral_add hb_f hb_g, intervalIntegral.integral_add ht_f ht_g,
      intervalIntegral.integral_add hr_f hr_g, intervalIntegral.integral_add hl_f hl_g]
  simp only [smul_add]
  ring

lemma rectBoundary_const_mul (T : ℝ) (hT : 0 < T) (a : ℂ) (f : ℂ → ℂ)
    (hf : ContinuousOn f (rectEdge T)) :
    PL.AfeRect.rectBoundary (⟨-1,-T⟩ : ℂ) (⟨1,T⟩ : ℂ) (fun u => a * f u)
      = a * PL.AfeRect.rectBoundary (⟨-1,-T⟩ : ℂ) (⟨1,T⟩ : ℂ) f := by
  have hb : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (⟨-1,-T⟩ : ℂ).im * I)) volume (-1) 1 :=
    (hf.comp (by fun_prop : ContinuousOn (fun x : ℝ => (x : ℂ) + (⟨-1,-T⟩ : ℂ).im * I) (Set.uIcc (-1) 1)) (rectEdge_bot T)).intervalIntegrable
  have ht : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (⟨1,T⟩ : ℂ).im * I)) volume (-1) 1 :=
    (hf.comp (by fun_prop : ContinuousOn (fun x : ℝ => (x : ℂ) + (⟨1,T⟩ : ℂ).im * I) (Set.uIcc (-1) 1)) (rectEdge_top T)).intervalIntegrable
  have hr : IntervalIntegrable (fun y : ℝ => f (Complex.re (⟨1,T⟩ : ℂ) + y * I)) volume (-T) T :=
    (hf.comp (by fun_prop : ContinuousOn (fun y : ℝ => (((⟨1,T⟩ : ℂ).re : ℝ) : ℂ) + (y : ℂ) * I) (Set.uIcc (-T) T)) (rectEdge_right T hT)).intervalIntegrable
  have hl : IntervalIntegrable (fun y : ℝ => f (Complex.re (⟨-1,-T⟩ : ℂ) + y * I)) volume (-T) T :=
    (hf.comp (by fun_prop : ContinuousOn (fun y : ℝ => (((⟨-1,-T⟩ : ℂ).re : ℝ) : ℂ) + (y : ℂ) * I) (Set.uIcc (-T) T)) (rectEdge_left T hT)).intervalIntegrable
  unfold PL.AfeRect.rectBoundary
  simp only []
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

lemma not_mem_rectEdge (T : ℝ) (hT : 0 < T) {α : ℂ} (h0 : -1 < α.re) (h1 : α.re < 1)
    (h2 : |α.im| < T) : α ∉ rectEdge T := by
  intro h
  rcases h with ⟨hre, _⟩ | ⟨him, _⟩
  · rcases hre with h | h <;> linarith
  · rcases him with h | h
    · rw [h] at h2; rw [abs_neg, abs_of_pos hT] at h2; exact lt_irrefl _ h2
    · rw [h] at h2; rw [abs_of_pos hT] at h2; exact lt_irrefl _ h2

lemma continuousOn_inv_sub_of_not_mem (T : ℝ) {α : ℂ} (hα : α ∉ rectEdge T) :
    ContinuousOn (fun u : ℂ => (u - α)⁻¹) (rectEdge T) := by
  apply ContinuousOn.inv₀
  · exact continuousOn_id.sub continuousOn_const
  · intro u hu h
    rw [sub_eq_zero] at h; exact hα (h ▸ hu)

lemma rectBoundary_congr_of_eqOn (T : ℝ) (hT : 0 < T) {f g : ℂ → ℂ}
    (h : ∀ u ∈ rectEdge T, f u = g u) :
    PL.AfeRect.rectBoundary (⟨-1,-T⟩ : ℂ) (⟨1,T⟩ : ℂ) f
      = PL.AfeRect.rectBoundary (⟨-1,-T⟩ : ℂ) (⟨1,T⟩ : ℂ) g := by
  unfold PL.AfeRect.rectBoundary
  have e1 : (∫ x : ℝ in (-1)..1, f ((x : ℂ) + (⟨-1,-T⟩ : ℂ).im * I))
      = ∫ x : ℝ in (-1)..1, g ((x : ℂ) + (⟨-1,-T⟩ : ℂ).im * I) := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact h _ (rectEdge_bot T hx)
  have e2 : (∫ x : ℝ in (-1)..1, f ((x : ℂ) + (⟨1,T⟩ : ℂ).im * I))
      = ∫ x : ℝ in (-1)..1, g ((x : ℂ) + (⟨1,T⟩ : ℂ).im * I) := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact h _ (rectEdge_top T hx)
  have e3 : (∫ y : ℝ in (-T)..T, f (Complex.re (⟨1,T⟩ : ℂ) + y * I))
      = ∫ y : ℝ in (-T)..T, g (Complex.re (⟨1,T⟩ : ℂ) + y * I) := by
    apply intervalIntegral.integral_congr
    intro y hy
    exact h _ (rectEdge_right T hT hy)
  have e4 : (∫ y : ℝ in (-T)..T, f (Complex.re (⟨-1,-T⟩ : ℂ) + y * I))
      = ∫ y : ℝ in (-T)..T, g (Complex.re (⟨-1,-T⟩ : ℂ) + y * I) := by
    apply intervalIntegral.integral_congr
    intro y hy
    exact h _ (rectEdge_left T hT hy)
  rw [e1, e2, e3, e4]


lemma differentiable_smoothingFunction : Differentiable ℂ PL.AFE.smoothingFunction := by
  unfold PL.AFE.smoothingFunction
  fun_prop

lemma rectBoundary_zetaK (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) (T : ℝ) (hT : |s.im| < T) :
    PL.AfeRect.rectBoundary (⟨-1,-T⟩ : ℂ) (⟨1,T⟩ : ℂ) (zetaK s)
      = 2 * Real.pi * I * (completedRiemannZeta s + PL.AFE.smoothingFunction (1 - s) / (1 - s)
          + PL.AFE.smoothingFunction s / s) := by
  have hTpos : 0 < T := lt_of_le_of_lt (abs_nonneg s.im) hT
  have hs0' : s ≠ 0 := by intro h; rw [h] at hs0; simp at hs0
  have hbne : (1 - s) ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith [hs1]
  have hb0 : -1 < (1-s).re := by simp [Complex.sub_re, Complex.one_re]; linarith [hs1]
  have hb1 : (1-s).re < 1 := by simp [Complex.sub_re, Complex.one_re]; linarith [hs0]
  have hbT : |(1-s).im| < T := by
    have h : (1-s).im = -s.im := by simp
    rw [h, abs_neg]; exact hT
  have hg0 : -1 < (-s).re := by simp [Complex.neg_re]; linarith [hs0]
  have hg1 : (-s).re < 1 := by simp [Complex.neg_re]; linarith [hs1]
  have hgT : |(-s).im| < T := by
    have h : (-s).im = -s.im := by simp
    rw [h, abs_neg]; exact hT
  have h0mem : (0:ℂ) ∉ rectEdge T := not_mem_rectEdge T hTpos (by norm_num) (by norm_num) (by simpa using hTpos)
  have hbmem : (1-s) ∉ rectEdge T := not_mem_rectEdge T hTpos hb0 hb1 hbT
  have hgmem : (-s) ∉ rectEdge T := not_mem_rectEdge T hTpos hg0 hg1 hgT
  let Φ : ℂ → ℂ := fun u => ((u - (1-s)) * (u + s) * completedRiemannZeta₀ (s + u) + 1) * PL.AFE.smoothingFunction u
  have hΦ : Differentiable ℂ Φ := by
    change Differentiable ℂ (fun u => ((u - (1-s)) * (u + s) * completedRiemannZeta₀ (s + u) + 1) * PL.AFE.smoothingFunction u)
    have hΛ : Differentiable ℂ (fun u : ℂ => completedRiemannZeta₀ (s + u)) := by
      have h1 : Differentiable ℂ (fun u : ℂ => s + u) := (differentiable_const s).add differentiable_id
      exact differentiable_completedZeta₀.comp h1
    exact (((differentiable_id.sub (differentiable_const (1-s))).mul
      (differentiable_id.add (differentiable_const s))).mul hΛ).add
      (differentiable_const 1) |>.mul differentiable_smoothingFunction
  have hΦds : ∀ c : ℂ, Differentiable ℂ (dslope Φ c) := by
    intro c
    rw [← differentiableOn_univ]
    exact (differentiableOn_dslope (s := Set.univ) (by simp)).mpr hΦ.differentiableOn
  let A : ℂ := -(s * (1-s))⁻¹
  let B : ℂ := (1-s)⁻¹
  let C : ℂ := s⁻¹
  let Ψ : ℂ → ℂ := fun u => A * dslope Φ 0 u + B * dslope Φ (1-s) u + C * dslope Φ (-s) u
  have hΨ : Differentiable ℂ Ψ := by
    dsimp only [Ψ]
    exact (((hΦds 0).const_mul A).add ((hΦds (1-s)).const_mul B)).add ((hΦds (-s)).const_mul C)
  have hsplit : ∀ u : ℂ, u ≠ 0 → u ≠ (1-s) → u ≠ (-s) →
      zetaK s u = (A * Φ 0) * u⁻¹ + ((B * Φ (1-s)) * (u - (1-s))⁻¹
        + ((C * Φ (-s)) * (u + s)⁻¹ + Ψ u)) := by
    intro u hu0 hub hug
    have hsN : s + u ≠ 0 := by intro h; exact hug (by linear_combination h)
    have hu1s : u - (1-s) ≠ 0 := sub_ne_zero.mpr hub
    have hus : u + s ≠ 0 := by intro h; exact hug (by linear_combination h)
    have huNs : u - (-s) ≠ 0 := by rw [sub_eq_add_neg, neg_neg]; exact hus
    have h1 : (u - (1-s)) * (u + s) * completedRiemannZeta (s + u)
        = (u - (1-s)) * (u + s) * completedRiemannZeta₀ (s + u) + 1 := by
      rw [completedRiemannZeta_eq (s + u)]
      rw [show 1 - (s + u) = -(u - (1-s)) by ring, show s + u = u + s by ring]
      field_simp [hus, hu1s]
      ring
    have hPhi_u : Φ u = (u - (1-s)) * (u + s) * completedRiemannZeta (s + u) * PL.AFE.smoothingFunction u := by
      change ((u - (1-s)) * (u + s) * completedRiemannZeta₀ (s + u) + 1) * PL.AFE.smoothingFunction u = _
      rw [← h1]
    have hK : zetaK s u = Φ u / (u * (u - (1-s)) * (u + s)) := by
      rw [hPhi_u]
      dsimp only [zetaK]
      field_simp [hu0, hu1s, hus]
    have hPf : (u * (u - (1-s)) * (u + s))⁻¹ = A / u + B / (u - (1-s)) + C / (u + s) := by
      dsimp only [A, B, C]
      field_simp [hu0, hu1s, hus, hs0', hbne]
      ring
    have hd0 : dslope Φ 0 u = (Φ u - Φ 0) / u := by
      rw [dslope_of_ne Φ (a := (0:ℂ)) (b := u) hu0, slope, smul_eq_mul, sub_zero, vsub_eq_sub, div_eq_mul_inv]; ring
    have hd1 : dslope Φ (1-s) u = (Φ u - Φ (1-s)) / (u - (1-s)) := by
      rw [dslope_of_ne Φ (a := (1-s)) (b := u) (sub_ne_zero.mp hu1s), slope, smul_eq_mul, vsub_eq_sub, div_eq_mul_inv]; ring
    have hdn : dslope Φ (-s) u = (Φ u - Φ (-s)) / (u - (-s)) := by
      rw [dslope_of_ne Φ (a := (-s)) (b := u) (sub_ne_zero.mp huNs), slope, smul_eq_mul, vsub_eq_sub, div_eq_mul_inv]; ring
    rw [hK, div_eq_mul_inv, hPf]
    dsimp only [Ψ]
    rw [hd0, hd1, hdn, show u - (-s) = u + s by ring]
    field_simp [hu0, hu1s, hus]
    ring
  let G1 : ℂ → ℂ := fun u => (A * Φ 0) * u⁻¹
  let G2 : ℂ → ℂ := fun u => (B * Φ (1-s)) * (u - (1-s))⁻¹
  let G3 : ℂ → ℂ := fun u => (C * Φ (-s)) * (u + s)⁻¹
  have hInv0c : ContinuousOn (fun u : ℂ => u⁻¹) (rectEdge T) := by
    simpa using continuousOn_inv_sub_of_not_mem T h0mem
  have hG1 : ContinuousOn G1 (rectEdge T) := hInv0c.const_mul _
  have hG2 : ContinuousOn G2 (rectEdge T) := (continuousOn_inv_sub_of_not_mem T hbmem).const_mul _
  have hG3 : ContinuousOn G3 (rectEdge T) := by
    have h := (continuousOn_inv_sub_of_not_mem T hgmem).const_mul (C * Φ (-s))
    have hh : (fun u : ℂ => (C * Φ (-s)) * (u - (-s))⁻¹) = G3 := by
      funext u; dsimp only [G3]; rw [sub_eq_add_neg, neg_neg]
    rwa [hh] at h
  have hΨc : ContinuousOn Ψ (rectEdge T) := hΨ.continuous.continuousOn
  have hcomp : PL.AfeRect.rectBoundary (⟨-1,-T⟩ : ℂ) (⟨1,T⟩ : ℂ) (zetaK s)
      = PL.AfeRect.rectBoundary (⟨-1,-T⟩ : ℂ) (⟨1,T⟩ : ℂ) (G1 + (G2 + (G3 + Ψ))) := by
    apply rectBoundary_congr_of_eqOn T hTpos
    intro u hu
    have hu0 : u ≠ 0 := fun h => h0mem (h ▸ hu)
    have hub : u ≠ (1-s) := fun h => hbmem (h ▸ hu)
    have hug : u ≠ (-s) := fun h => hgmem (h ▸ hu)
    have hh := hsplit u hu0 hub hug
    simpa only [Pi.add_apply, G1, G2, G3] using hh
  have hV1 : PL.AfeRect.rectBoundary (⟨-1,-T⟩ : ℂ) (⟨1,T⟩ : ℂ) G1 = (A * Φ 0) * (2 * Real.pi * I) := by
    have := rectBoundary_const_mul T hTpos (A * Φ 0) (fun u : ℂ => u⁻¹) hInv0c
    rw [this, show PL.AfeRect.rectBoundary (⟨-1,-T⟩ : ℂ) (⟨1,T⟩ : ℂ) (fun u : ℂ => u⁻¹)
        = 2 * Real.pi * I by
      simpa using rectBoundary_shifted_inv 0 T (by norm_num) (by norm_num) (by simpa using hTpos)]
  have hV2 : PL.AfeRect.rectBoundary (⟨-1,-T⟩ : ℂ) (⟨1,T⟩ : ℂ) G2 = (B * Φ (1-s)) * (2 * Real.pi * I) := by
    have hc : ContinuousOn (fun u : ℂ => (u - (1-s))⁻¹) (rectEdge T) :=
      continuousOn_inv_sub_of_not_mem T hbmem
    have := rectBoundary_const_mul T hTpos (B * Φ (1-s)) (fun u : ℂ => (u - (1-s))⁻¹) hc
    rw [this, show PL.AfeRect.rectBoundary (⟨-1,-T⟩ : ℂ) (⟨1,T⟩ : ℂ) (fun u : ℂ => (u - (1-s))⁻¹)
        = 2 * Real.pi * I by exact rectBoundary_shifted_inv (1-s) T hb0 hb1 hbT]
  have hV3 : PL.AfeRect.rectBoundary (⟨-1,-T⟩ : ℂ) (⟨1,T⟩ : ℂ) G3 = (C * Φ (-s)) * (2 * Real.pi * I) := by
    have hc : ContinuousOn (fun u : ℂ => (u + s)⁻¹) (rectEdge T) := by
      have h := continuousOn_inv_sub_of_not_mem T hgmem
      have hh : (fun u : ℂ => (u - (-s))⁻¹) = (fun u : ℂ => (u + s)⁻¹) := by
        funext u; rw [sub_eq_add_neg, neg_neg]
      rwa [hh] at h
    have := rectBoundary_const_mul T hTpos (C * Φ (-s)) (fun u : ℂ => (u + s)⁻¹) hc
    rw [this]
    congr 1
    have h := rectBoundary_shifted_inv (-s) T hg0 hg1 hgT
    have hh : (fun u : ℂ => (u - (-s))⁻¹) = (fun u : ℂ => (u + s)⁻¹) := by
      funext u; rw [sub_eq_add_neg, neg_neg]
    rwa [hh] at h
  have hVΨ : PL.AfeRect.rectBoundary (⟨-1,-T⟩ : ℂ) (⟨1,T⟩ : ℂ) Ψ = 0 :=
    PL.AfeRect.rectBoundary_eq_zero_of_differentiableOn Ψ (⟨-1,-T⟩ : ℂ) (⟨1,T⟩ : ℂ)
      hΨ.differentiableOn
  rw [hcomp, rectBoundary_add T hTpos G1 (G2 + (G3 + Ψ)) hG1 (hG2.add (hG3.add hΨc)),
      rectBoundary_add T hTpos G2 (G3 + Ψ) hG2 (hG3.add hΨc),
      rectBoundary_add T hTpos G3 Ψ hG3 hΨc, hV1, hV2, hV3, hVΨ]
  have hΦ0 : Φ 0 = ((s - 1) * s * completedRiemannZeta₀ s + 1) := by
    have hg0 : PL.AFE.smoothingFunction (0:ℂ) = 1 := by unfold PL.AFE.smoothingFunction; simp
    simp only [Φ, hg0, mul_one]
    rw [show (0:ℂ) + s = s by ring, show (0:ℂ) - (1-s) = s - 1 by ring, add_zero]
  have hΦb : Φ (1-s) = PL.AFE.smoothingFunction (1-s) := by
    simp only [Φ]
    rw [show (1-s:ℂ) - (1-s) = 0 by ring, show (1-s:ℂ) + s = 1 by ring]
    simp only [zero_mul, mul_zero, zero_add, one_mul]
  have hΦg : Φ (-s) = PL.AFE.smoothingFunction s := by
    simp only [Φ]
    rw [show (-s:ℂ) + s = 0 by ring, show (-s:ℂ) - (1-s) = -1 by ring]
    simp only [zero_mul, mul_zero, zero_add, one_mul]
    exact PL.AFE.Structural.smoothingFunction_even s
  have hAc : A * Φ 0 = completedRiemannZeta s := by
    rw [hΦ0]; dsimp only [A]; rw [completedRiemannZeta_eq s]
    field_simp [hs0', hbne]; ring
  have hBc : B * Φ (1-s) = PL.AFE.smoothingFunction (1-s) / (1-s) := by
    rw [hΦb]; dsimp only [B]; field_simp
  have hCc : C * Φ (-s) = PL.AFE.smoothingFunction s / s := by
    rw [hΦg]; dsimp only [C]; field_simp
  rw [hAc, hBc, hCc]; ring


theorem vertical_line_identity_zeta (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    completedRiemannZeta s
      = (1 / (2 * Real.pi)) *
          ( (∫ y : ℝ, completedRiemannZeta (s + 1 + (y : ℂ) * Complex.I)
                * PL.AFE.smoothingFunction (1 + (y : ℂ) * Complex.I) * (1 + (y : ℂ) * Complex.I)⁻¹)
          - (∫ y : ℝ, completedRiemannZeta (s - 1 + (y : ℂ) * Complex.I)
                * PL.AFE.smoothingFunction (-1 + (y : ℂ) * Complex.I) * (-1 + (y : ℂ) * Complex.I)⁻¹) )
        - (PL.AFE.smoothingFunction (1 - s) / (1 - s) + PL.AFE.smoothingFunction s / s) := by
  let X : ℂ := (∫ y : ℝ, completedRiemannZeta (s + 1 + (y : ℂ) * Complex.I)
                * PL.AFE.smoothingFunction (1 + (y : ℂ) * Complex.I) * (1 + (y : ℂ) * Complex.I)⁻¹)
          - (∫ y : ℝ, completedRiemannZeta (s - 1 + (y : ℂ) * Complex.I)
                * PL.AFE.smoothingFunction (-1 + (y : ℂ) * Complex.I) * (-1 + (y : ℂ) * Complex.I)⁻¹)
  let C : ℂ := PL.AFE.smoothingFunction (1 - s) / (1 - s) + PL.AFE.smoothingFunction s / s
  change completedRiemannZeta s = (1 / (2 * Real.pi)) * X - C
  have hXeq : (∫ y : ℝ, zetaLineR s y) - (∫ y : ℝ, zetaLineL s y) = X := rfl
  have hEdge : ∀ T : ℝ, PL.AfeRect.rectBoundary (⟨-1,-T⟩ : ℂ) (⟨1,T⟩ : ℂ) (zetaK s)
      = (∫ x : ℝ in (-1)..1, zetaHoriz s (-T) x) - (∫ x : ℝ in (-1)..1, zetaHoriz s T x)
        + Complex.I • (∫ y : ℝ in -T..T, zetaLineR s y)
        - Complex.I • (∫ y : ℝ in -T..T, zetaLineL s y) := by
    intro T
    unfold PL.AfeRect.rectBoundary
    have hb : (∫ x : ℝ in (-1)..1, zetaK s ((x : ℂ) + (⟨-1,-T⟩ : ℂ).im * I))
        = ∫ x : ℝ in (-1)..1, zetaHoriz s (-T) x := by
      apply intervalIntegral.integral_congr
      intro x _
      exact (zetaHoriz_eq_zetaK s (-T) x).symm
    have ht : (∫ x : ℝ in (-1)..1, zetaK s ((x : ℂ) + (⟨1,T⟩ : ℂ).im * I))
        = ∫ x : ℝ in (-1)..1, zetaHoriz s T x := by
      apply intervalIntegral.integral_congr
      intro x _
      exact (zetaHoriz_eq_zetaK s T x).symm
    have hr : (∫ y : ℝ in -T..T, zetaK s (((⟨1,T⟩ : ℂ).re : ℝ) + y * I))
        = ∫ y : ℝ in -T..T, zetaLineR s y := by
      apply intervalIntegral.integral_congr
      intro y _
      simpa using (zetaLineR_eq_zetaK s y).symm
    have hl : (∫ y : ℝ in -T..T, zetaK s (((⟨-1,-T⟩ : ℂ).re : ℝ) + y * I))
        = ∫ y : ℝ in -T..T, zetaLineL s y := by
      apply intervalIntegral.integral_congr
      intro y _
      simpa using (zetaLineL_eq_zetaK s y).symm
    rw [hb, ht, hr, hl]
  have hlimR : Tendsto (fun T : ℝ => PL.AfeRect.rectBoundary (⟨-1,-T⟩ : ℂ) (⟨1,T⟩ : ℂ) (zetaK s))
      atTop (𝓝 (Complex.I * X)) := by
    have h1 : Tendsto (fun T : ℝ => ∫ x : ℝ in (-1)..1, zetaHoriz s (-T) x) atTop (𝓝 0) :=
      tendsto_zetaHoriz_neg s hs0 hs1
    have h2 : Tendsto (fun T : ℝ => ∫ x : ℝ in (-1)..1, zetaHoriz s T x) atTop (𝓝 0) :=
      tendsto_zetaHoriz_id s hs0 hs1
    have h3 : Tendsto (fun T : ℝ => ∫ y : ℝ in -T..T, zetaLineR s y) atTop
        (𝓝 (∫ y : ℝ, zetaLineR s y)) := tendsto_truncated_zetaLineR s hs0
    have h4 : Tendsto (fun T : ℝ => ∫ y : ℝ in -T..T, zetaLineL s y) atTop
        (𝓝 (∫ y : ℝ, zetaLineL s y)) := tendsto_truncated_zetaLineL s hs1
    have hcomb : Tendsto (fun T : ℝ => (∫ x : ℝ in (-1)..1, zetaHoriz s (-T) x)
        - (∫ x : ℝ in (-1)..1, zetaHoriz s T x)
        + Complex.I • (∫ y : ℝ in -T..T, zetaLineR s y)
        - Complex.I • (∫ y : ℝ in -T..T, zetaLineL s y)) atTop
        (𝓝 (Complex.I * (∫ y : ℝ, zetaLineR s y) - Complex.I * (∫ y : ℝ, zetaLineL s y))) := by
      have hA : Tendsto (fun T : ℝ => (∫ x : ℝ in (-1)..1, zetaHoriz s (-T) x)
          - (∫ x : ℝ in (-1)..1, zetaHoriz s T x)) atTop (𝓝 0) := by
        simpa using h1.sub h2
      have hB : Tendsto (fun T : ℝ => Complex.I • (∫ y : ℝ in -T..T, zetaLineR s y)) atTop
          (𝓝 (Complex.I * (∫ y : ℝ, zetaLineR s y))) := by
        have := h3.const_smul Complex.I
        simpa [smul_eq_mul] using this
      have hC' : Tendsto (fun T : ℝ => Complex.I • (∫ y : ℝ in -T..T, zetaLineL s y)) atTop
          (𝓝 (Complex.I * (∫ y : ℝ, zetaLineL s y))) := by
        have := h4.const_smul Complex.I
        simpa [smul_eq_mul] using this
      have hAB : Tendsto (fun T : ℝ => (∫ x : ℝ in (-1)..1, zetaHoriz s (-T) x)
          - (∫ x : ℝ in (-1)..1, zetaHoriz s T x)
          + Complex.I • (∫ y : ℝ in -T..T, zetaLineR s y)) atTop
          (𝓝 (Complex.I * (∫ y : ℝ, zetaLineR s y))) := by
        simpa using hA.add hB
      simpa using hAB.sub hC'
    have := Tendsto.congr' (Eventually.of_forall (fun T => (hEdge T).symm)) hcomb
    have htarget : Complex.I * (∫ y : ℝ, zetaLineR s y) - Complex.I * (∫ y : ℝ, zetaLineL s y)
        = Complex.I * X := by rw [← hXeq]; ring
    rwa [htarget] at this
  have hconstR : Tendsto (fun T : ℝ => PL.AfeRect.rectBoundary (⟨-1,-T⟩ : ℂ) (⟨1,T⟩ : ℂ) (zetaK s))
      atTop (𝓝 (2 * Real.pi * I * (completedRiemannZeta s
        + PL.AFE.smoothingFunction (1 - s) / (1 - s) + PL.AFE.smoothingFunction s / s))) := by
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [eventually_gt_atTop |s.im|] with T hT
    exact (rectBoundary_zetaK s hs0 hs1 T hT).symm
  have heq := tendsto_nhds_unique hlimR hconstR
  have hX : X = (2 * Real.pi) * (completedRiemannZeta s + C) := by
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have h2 : Complex.I * X = Complex.I * ((2 * Real.pi) * (completedRiemannZeta s + C)) := by
      dsimp only [C]; rw [heq]; ring
    exact mul_left_cancel₀ hI h2
  rw [hX]
  field_simp
  ring


end

end Commons.NumberTheory.Zeta