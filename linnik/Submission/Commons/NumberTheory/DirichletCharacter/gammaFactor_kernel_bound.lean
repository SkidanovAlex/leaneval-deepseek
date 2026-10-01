import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Gamma.psi_kernel_bound_minus
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound
import Submission.Commons.Analysis.SpecialFunctions.Gamma.logDeriv_GammaR_off_pole
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_le
import Submission.Commons.NumberTheory.DirichletCharacter.Even_inv
import Submission.Commons.NumberTheory.DirichletCharacter.Odd_inv
import Submission.Commons.NumberTheory.DirichletCharacter.chebyshevPsiChi_explicit_formula_mult

open MeasureTheory Complex
open scoped Real Topology

noncomputable section

namespace Commons.NumberTheory.DirichletCharacter

/-!
## The gamma-factor kernel bound

We bound the integral over `u : ℝ` of `(logDeriv (gammaFactor χ⁻¹) (3/2 - i(b-u)) +
logDeriv (gammaFactor χ) (-1/2 + i(b-u)))` against the kernel
`(exp (-((a+iu)λ)) - 1)/(a+iu)²` by `400`.

The Archimedean gamma factor is `Gammaℝ s` (χ even) or `Gammaℝ (s+1)` (χ odd); its logarithmic
derivative is `-log π/2 + ψ(s/2)/2` (`logDeriv_GammaR_off_pole`).  Hence the two terms become
digammas at `3/4 ∓ i(b-u)/2` (χ even) or `5/4, 1/4` (χ odd), and the result follows from the
commons kernel bounds `psi_kernel_bound` (`≤ 200`), `psi_kernel_bound_minus` (`= 0`) and the
vanishing `∫ gK u / (u - c) = 0` for `Im c > 0` proved below.
-/

/-- A point of the complex plane with positive real part is not a pole of `Γ`. -/
private lemma ne_neg_nat_of_re_pos' {z : ℂ} (h : 0 < z.re) : ∀ m : ℕ, z ≠ -(m : ℂ) := by
  intro m hz
  have h1 := congrArg Complex.re hz
  simp only [Complex.neg_re, Complex.natCast_re] at h1
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

/-- A complex point with real part `-1/4` is not a pole of `Γ`. -/
private lemma ne_neg_nat_of_re_eq_neg_quarter {z : ℂ} (h : z.re = -1/4) : ∀ m : ℕ, z ≠ -(m : ℂ) := by
  intro m hm
  have h1 := congrArg Complex.re hm
  rw [h] at h1
  have h2 : ((-(m:ℂ))).re = -(m:ℝ) := by simp
  rw [h2] at h1
  have hm4' : ((4*m : ℕ) : ℝ) = 1 := by push_cast; linarith
  have : (4*m : ℕ) = 1 := by exact_mod_cast hm4'
  omega

/-! ### The logarithmic derivative of the shifted gamma factor -/

private lemma logDeriv_shift_GammaR (s : ℂ) (hs : 0 < (s + 1).re) :
    logDeriv (fun z : ℂ => Complex.Gammaℝ (z + 1)) s = logDeriv Complex.Gammaℝ (s + 1) := by
  have hf : DifferentiableAt ℂ Complex.Gammaℝ (s + 1) := differentiableAt_Gammaℝ (s + 1) hs
  have hg : DifferentiableAt ℂ (fun z : ℂ => z + 1) s := by fun_prop
  have h := logDeriv_comp (f := Complex.Gammaℝ) (g := fun z : ℂ => z + 1) (x := s) hf hg
  have hder : deriv (fun z : ℂ => z + 1) s = 1 := by simp
  rw [hder, mul_one] at h
  simpa [Function.comp_def] using h

/-! ### Integrability and vanishing of `∫ gK u / (u - c)` for `Im c > 0` -/

private lemma integrable_gK_div_sub_I_of_im_pos (a lam : ℝ) (ha : 0 < a) (c : ℂ)
    (hc : 0 < c.im) :
    Integrable (fun u : ℝ => PsiKernelBound.gK a lam u / ((u : ℂ) - c)) (volume : Measure ℝ) := by
  have hle : ∀ u : ℝ, c.im ≤ ‖((u : ℂ) - c)‖ := by
    intro u
    have h := Complex.abs_im_le_norm ((u : ℂ) - c)
    rw [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg, abs_of_pos hc] at h
    exact h
  refine Integrable.mono' ((PsiKernelBound.integrable_gK a lam ha).norm.const_mul (1 / c.im)) ?_ ?_
  · apply Continuous.aestronglyMeasurable
    exact (PsiKernelBound.continuous_gK a lam ha).div (by fun_prop) (fun u => by
      intro h
      have h2 := congrArg Complex.im h
      rw [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im] at h2
      linarith)
  · filter_upwards with u
    rw [norm_div]
    have h1 : 1 / ‖((u : ℂ) - c)‖ ≤ 1 / c.im :=
      one_div_le_one_div_of_le hc (hle u)
    calc ‖PsiKernelBound.gK a lam u‖ / ‖((u : ℂ) - c)‖
        = ‖PsiKernelBound.gK a lam u‖ * (1 / ‖((u : ℂ) - c)‖) := by
          rw [div_eq_mul_inv, one_div]
      _ ≤ ‖PsiKernelBound.gK a lam u‖ * (1 / c.im) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = (1 / c.im) * ‖PsiKernelBound.gK a lam u‖ := by ring

private lemma integral_gK_div_sub_I_of_im_pos (a lam : ℝ) (ha : 0 < a) (hlam : 0 < lam)
    (c : ℂ) (hc : 0 < c.im) :
    (∫ u : ℝ, PsiKernelBound.gK a lam u / ((u : ℂ) - c)) = 0 := by
  set P : ℂ := -(Complex.I) * c with hP
  have hPre : 0 < P.re := by
    rw [hP]
    rw [show (-Complex.I * c).re = c.im by simp [Complex.mul_re]]
    exact hc
  have hkey : ∀ u : ℝ, PsiKernelBound.gK a lam u / ((u : ℂ) - c)
      = Complex.I * (PsiKernelBound.gK a lam u / (P + (u : ℂ) * Complex.I)) := by
    intro u
    have hz : (u : ℂ) - c = -(Complex.I) * (P + (u : ℂ) * Complex.I) := by
      rw [hP]
      simp only [Complex.I_mul_I, mul_add, neg_mul, mul_assoc, mul_neg, neg_neg, mul_one,
        mul_comm Complex.I]
      ring
    have hInv : ((u : ℂ) - c)⁻¹ = (P + (u : ℂ) * Complex.I)⁻¹ * Complex.I := by
      rw [hz, mul_inv_rev, inv_neg, Complex.inv_I]
      ring
    rw [div_eq_mul_inv, hInv, div_eq_mul_inv]
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hkey),
    MeasureTheory.integral_const_mul]
  rw [PsiKernelMinus.integral_gK_div_add_I a lam ha hlam P hPre, mul_zero]

/-! ### The specific inverse `(-1/4 + i(b-u)/2)⁻¹` -/

private lemma inv_neg_quarter_eq (b u : ℝ) :
    ((((-1/4:ℝ):ℂ) + (((b - u)/2:ℝ):ℂ) * Complex.I))⁻¹
      = (2 * Complex.I) * ((u : ℂ) - ((b:ℂ) + Complex.I/2))⁻¹ := by
  have h1 : (((-1/4:ℝ):ℂ) + (((b - u)/2:ℝ):ℂ) * Complex.I)
      = -(Complex.I/2) * ((u : ℂ) - ((b:ℂ) + Complex.I/2)) := by
    apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im] <;>
    ring
  have h2 : (-(Complex.I/2):ℂ)⁻¹ = 2 * Complex.I := by
    have h : ((2:ℂ) * Complex.I)⁻¹ = -(Complex.I/2) := by
      rw [mul_inv_rev, Complex.inv_I]; ring
    rw [← h, inv_inv]
  rw [h1, mul_inv_rev, h2]
  ring

private lemma integrable_gK_inv_neg_quarter (a lam b : ℝ) (ha : 0 < a) :
    Integrable (fun u : ℝ =>
      ((((-1/4:ℝ):ℂ) + (((b - u)/2:ℝ):ℂ) * Complex.I))⁻¹ * PsiKernelBound.gK a lam u)
      (volume : Measure ℝ) := by
  have hc0 : 0 < ((b:ℂ) + Complex.I/2).im := by simp
  refine (integrable_gK_div_sub_I_of_im_pos a lam ha _ hc0).const_mul (2 * Complex.I) |>.congr ?_
  filter_upwards with u
  rw [inv_neg_quarter_eq b u, div_eq_mul_inv]
  ring

private lemma integral_gK_inv_neg_quarter (a lam b : ℝ) (ha : 0 < a) (hlam : 0 < lam) :
    (∫ u : ℝ,
      ((((-1/4:ℝ):ℂ) + (((b - u)/2:ℝ):ℂ) * Complex.I))⁻¹ * PsiKernelBound.gK a lam u) = 0 := by
  have hc0 : 0 < ((b:ℂ) + Complex.I/2).im := by simp
  have hpt : ∀ u : ℝ,
      ((((-1/4:ℝ):ℂ) + (((b - u)/2:ℝ):ℂ) * Complex.I))⁻¹ * PsiKernelBound.gK a lam u
        = (2 * Complex.I) * (PsiKernelBound.gK a lam u / ((u : ℂ) - ((b:ℂ) + Complex.I/2))) := by
    intro u
    rw [inv_neg_quarter_eq b u, div_eq_mul_inv]
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_const_mul,
    integral_gK_div_sub_I_of_im_pos a lam ha hlam _ hc0, mul_zero]

/-! ### Integrability of `ψ(·) · gK` on the strip `1/4 ≤ Re ≤ 8` -/

private lemma continuousAt_digamma_of_re_pos {w : ℂ} (hw : 0 < w.re) :
    ContinuousAt Complex.digamma w :=
  (differentiableAt_digamma_of_pos hw).continuousAt

private lemma integrable_digamma_plus_mul_gK (a lam b x : ℝ) (ha : 0 < a)
    (hx1 : (1 : ℝ) / 4 ≤ x) (hx2 : x ≤ 8) :
    Integrable (fun u : ℝ =>
      Complex.digamma ((x : ℂ) + (((b - u) / 2 : ℝ) : ℂ) * Complex.I) *
        PsiKernelBound.gK a lam u) (volume : Measure ℝ) := by
  refine Integrable.mono' ((PsiKernelBound.integrable_log_gK a lam b ha).add
    ((PsiKernelBound.integrable_gK a lam ha).norm)) ?_ ?_
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul ?_ (PsiKernelBound.continuous_gK a lam ha)
    rw [continuous_iff_continuousAt]
    intro u
    have harg : ContinuousAt (fun v : ℝ => (x : ℂ) + (((b - v) / 2 : ℝ) : ℂ) * Complex.I) u := by
      fun_prop
    have hre : 0 < (((x : ℂ) + (((b - u) / 2 : ℝ) : ℂ) * Complex.I)).re := by
      have h : (((x : ℂ) + (((b - u) / 2 : ℝ) : ℂ) * Complex.I)).re = x := by simp
      rw [h]; linarith
    exact (continuousAt_digamma_of_re_pos hre).comp
      (f := fun v : ℝ => (x : ℂ) + (((b - v) / 2 : ℝ) : ℂ) * Complex.I) harg
  · filter_upwards with u
    rw [norm_mul]
    have hb := Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound x ((b - u) / 2)
      hx1 hx2
    have hy : |((b - u) / 2 : ℝ)| = |b - u| / 2 := by rw [abs_div]; norm_num
    calc ‖Complex.digamma ((x : ℂ) + (((b - u) / 2 : ℝ) : ℂ) * Complex.I)‖ *
          ‖PsiKernelBound.gK a lam u‖
        ≤ (Real.log (2 + |((b - u) / 2 : ℝ)|) + 8) * ‖PsiKernelBound.gK a lam u‖ :=
          mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ = (Real.log (2 + |b - u| / 2) + 7) * ‖PsiKernelBound.gK a lam u‖ +
            ‖PsiKernelBound.gK a lam u‖ := by rw [hy]; ring

private lemma integrable_digamma_minus_mul_gK (a lam b x : ℝ) (ha : 0 < a)
    (hx1 : (1 : ℝ) / 4 ≤ x) (hx2 : x ≤ 8) :
    Integrable (fun u : ℝ =>
      Complex.digamma ((x : ℂ) - (((b - u) / 2 : ℝ) : ℂ) * Complex.I) *
        PsiKernelBound.gK a lam u) (volume : Measure ℝ) := by
  refine Integrable.mono' ((PsiKernelBound.integrable_log_gK a lam b ha).add
    ((PsiKernelBound.integrable_gK a lam ha).norm)) ?_ ?_
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul ?_ (PsiKernelBound.continuous_gK a lam ha)
    rw [continuous_iff_continuousAt]
    intro u
    have harg : ContinuousAt (fun v : ℝ => (x : ℂ) - (((b - v) / 2 : ℝ) : ℂ) * Complex.I) u := by
      fun_prop
    have hre : 0 < (((x : ℂ) - (((b - u) / 2 : ℝ) : ℂ) * Complex.I)).re := by
      have h : (((x : ℂ) - (((b - u) / 2 : ℝ) : ℂ) * Complex.I)).re = x := by simp
      rw [h]; linarith
    exact (continuousAt_digamma_of_re_pos hre).comp
      (f := fun v : ℝ => (x : ℂ) - (((b - v) / 2 : ℝ) : ℂ) * Complex.I) harg
  · filter_upwards with u
    rw [norm_mul]
    set y : ℝ := -((b - u) / 2) with hydef
    have harg2 : ((x : ℂ) + (y : ℂ) * Complex.I)
        = ((x : ℂ) - (((b - u) / 2 : ℝ) : ℂ) * Complex.I) := by
      rw [hydef]; push_cast; ring
    have hb := Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound x y hx1 hx2
    rw [harg2] at hb
    have hy : |y| = |b - u| / 2 := by rw [hydef, abs_neg, abs_div]; norm_num
    calc ‖Complex.digamma ((x : ℂ) - (((b - u) / 2 : ℝ) : ℂ) * Complex.I)‖ *
          ‖PsiKernelBound.gK a lam u‖
        ≤ (Real.log (2 + |y|) + 8) * ‖PsiKernelBound.gK a lam u‖ :=
          mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ = (Real.log (2 + |b - u| / 2) + 7) * ‖PsiKernelBound.gK a lam u‖ +
            ‖PsiKernelBound.gK a lam u‖ := by rw [hy]; ring

/-! ## The main theorem -/

theorem gammaFactor_kernel_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχprim : χ.IsPrimitive) (a lam b : ℝ) (ha : 0 < a) (hlam : 0 < lam) :
    ‖∫ u : ℝ, (logDeriv (DirichletCharacter.gammaFactor χ⁻¹) ((3/2:ℝ) - ((b - u : ℝ) : ℂ) * Complex.I)
        + logDeriv (DirichletCharacter.gammaFactor χ) (((-1/2:ℝ):ℂ) + ((b - u : ℝ) : ℂ) * Complex.I)) *
      ((Complex.exp (-(((a : ℂ) + (u : ℂ) * Complex.I) * (lam : ℂ))) - 1) /
        (((a : ℂ) + (u : ℂ) * Complex.I)^2))‖ ≤ 400 := by
  have hker : ∀ u : ℝ,
      (Complex.exp (-(((a : ℂ) + (u : ℂ) * Complex.I) * (lam : ℂ))) - 1) /
        (((a : ℂ) + (u : ℂ) * Complex.I)^2) = PsiKernelBound.gK a lam u := by
    intro u
    simp only [PsiKernelBound.gK, div_eq_mul_inv]
  rcases χ.even_or_odd with hE | hO
  · -- ================= even case =================
    have hEinv : (χ⁻¹).Even := Even_inv hE
    have hgχ : DirichletCharacter.gammaFactor χ = Complex.Gammaℝ := funext hE.gammaFactor_def
    have hgχinv : DirichletCharacter.gammaFactor χ⁻¹ = Complex.Gammaℝ :=
      funext hEinv.gammaFactor_def
    have hA : ∀ u : ℝ, logDeriv (DirichletCharacter.gammaFactor χ⁻¹)
          ((3/2:ℝ) - ((b - u : ℝ) : ℂ) * Complex.I)
        = -(Complex.log (Real.pi : ℂ))/2
            + Complex.digamma (((3/4:ℝ):ℂ) - (((b - u)/2:ℝ):ℂ)*Complex.I)/2 := by
      intro u
      have hno : ∀ m : ℕ, (((3/2:ℝ):ℂ) - ((b - u : ℝ):ℂ)*Complex.I)/2 ≠ -(m:ℂ) :=
        neq_neg_nat_of_re_pos (by
          have h : (((3/2:ℝ):ℂ) - ((b - u : ℝ):ℂ)*Complex.I).re = 3/2 := by simp
          rw [h]; norm_num)
      have hdiv : (((3/2:ℝ):ℂ) - ((b - u : ℝ):ℂ)*Complex.I)/2
          = (((3/4:ℝ):ℂ) - (((b - u)/2:ℝ):ℂ)*Complex.I) := by push_cast; ring
      rw [hgχinv, Commons.Analysis.SpecialFunctions.Gamma.logDeriv_GammaR_off_pole _ hno, hdiv]
    have hB : ∀ u : ℝ, logDeriv (DirichletCharacter.gammaFactor χ)
          (((-1/2:ℝ):ℂ) + ((b - u : ℝ) : ℂ) * Complex.I)
        = -(Complex.log (Real.pi : ℂ))/2
            + Complex.digamma (((-1/4:ℝ):ℂ) + (((b - u)/2:ℝ):ℂ)*Complex.I)/2 := by
      intro u
      have hno : ∀ m : ℕ, (((-1/2:ℝ):ℂ) + ((b - u : ℝ):ℂ)*Complex.I)/2 ≠ -(m:ℂ) := by
        apply ne_neg_nat_of_re_eq_neg_quarter
        rw [re_div_two]
        have h : (((-1/2:ℝ):ℂ) + ((b - u : ℝ):ℂ)*Complex.I).re = -1/2 := by simp
        rw [h]; norm_num
      have hdiv : (((-1/2:ℝ):ℂ) + ((b - u : ℝ):ℂ)*Complex.I)/2
          = (((-1/4:ℝ):ℂ) + (((b - u)/2:ℝ):ℂ)*Complex.I) := by push_cast; ring
      rw [hgχ, Commons.Analysis.SpecialFunctions.Gamma.logDeriv_GammaR_off_pole _ hno, hdiv]
    have hB' : ∀ u : ℝ, Complex.digamma (((-1/4:ℝ):ℂ) + (((b - u)/2:ℝ):ℂ)*Complex.I)
        = Complex.digamma (((3/4:ℝ):ℂ) + (((b - u)/2:ℝ):ℂ)*Complex.I)
          - ((((-1/4:ℝ):ℂ) + (((b - u)/2:ℝ):ℂ)*Complex.I))⁻¹ := by
      intro u
      have hno : ∀ m : ℕ, (((-1/4:ℝ):ℂ) + (((b - u)/2:ℝ):ℂ)*Complex.I) ≠ -(m:ℂ) :=
        ne_neg_nat_of_re_eq_neg_quarter (by simp)
      have hs1 : (((-1/4:ℝ):ℂ) + (((b - u)/2:ℝ):ℂ)*Complex.I) + 1
          = (((3/4:ℝ):ℂ) + (((b - u)/2:ℝ):ℂ)*Complex.I) := by push_cast; ring
      have hrec := Complex.digamma_apply_add_one
        (((-1/4:ℝ):ℂ) + (((b - u)/2:ℝ):ℂ)*Complex.I) hno
      rw [hs1] at hrec
      rw [hrec]; ring
    set A1 : ℝ → ℂ := fun u => (-(Complex.log (Real.pi : ℂ))) * PsiKernelBound.gK a lam u with hA1
    set A2 : ℝ → ℂ := fun u => (1/2) *
      (Complex.digamma (((3/4:ℝ):ℂ) - (((b - u)/2:ℝ):ℂ)*Complex.I) *
        PsiKernelBound.gK a lam u) with hA2
    set A3 : ℝ → ℂ := fun u => (1/2) *
      (Complex.digamma (((3/4:ℝ):ℂ) + (((b - u)/2:ℝ):ℂ)*Complex.I) *
        PsiKernelBound.gK a lam u) with hA3
    set A4 : ℝ → ℂ := fun u => (1/2) *
      (((((-1/4:ℝ):ℂ) + (((b - u)/2:ℝ):ℂ)*Complex.I))⁻¹ * PsiKernelBound.gK a lam u) with hA4
    have hpt : ∀ u : ℝ,
        (logDeriv (DirichletCharacter.gammaFactor χ⁻¹)
              ((3/2:ℝ) - ((b - u : ℝ) : ℂ) * Complex.I)
          + logDeriv (DirichletCharacter.gammaFactor χ)
              (((-1/2:ℝ):ℂ) + ((b - u : ℝ) : ℂ) * Complex.I)) *
          ((Complex.exp (-(((a : ℂ) + (u : ℂ) * Complex.I) * (lam : ℂ))) - 1) /
            (((a : ℂ) + (u : ℂ) * Complex.I)^2))
        = A1 u + A2 u + A3 u - A4 u := by
      intro u
      rw [hA u, hB u, hB' u, hker u]
      simp only [hA1, hA2, hA3, hA4]
      ring
    have hstep : (∫ u : ℝ,
        (logDeriv (DirichletCharacter.gammaFactor χ⁻¹)
              ((3/2:ℝ) - ((b - u : ℝ) : ℂ) * Complex.I)
          + logDeriv (DirichletCharacter.gammaFactor χ)
              (((-1/2:ℝ):ℂ) + ((b - u : ℝ) : ℂ) * Complex.I)) *
          ((Complex.exp (-(((a : ℂ) + (u : ℂ) * Complex.I) * (lam : ℂ))) - 1) /
            (((a : ℂ) + (u : ℂ) * Complex.I)^2)))
        = ∫ u : ℝ, A1 u + A2 u + A3 u - A4 u := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with u
      exact hpt u
    have iA1 : Integrable A1 := by
      rw [hA1]
      exact (PsiKernelBound.integrable_gK a lam ha).const_mul _
    have iA2 : Integrable A2 := by
      rw [hA2]
      exact (integrable_digamma_minus_mul_gK a lam b (3/4) ha (by norm_num) (by norm_num)).const_mul _
    have iA3 : Integrable A3 := by
      rw [hA3]
      exact (integrable_digamma_plus_mul_gK a lam b (3/4) ha (by norm_num) (by norm_num)).const_mul _
    have iA4 : Integrable A4 := by
      rw [hA4]
      exact (integrable_gK_inv_neg_quarter a lam b ha).const_mul _
    have hsplit : (∫ u : ℝ, A1 u + A2 u + A3 u - A4 u)
        = (∫ u, A1 u) + (∫ u, A2 u) + (∫ u, A3 u) - (∫ u, A4 u) := by
      rw [MeasureTheory.integral_sub (f := fun u => A1 u + A2 u + A3 u) (g := A4)
            ((iA1.add iA2).add iA3) iA4,
        MeasureTheory.integral_add (f := fun u => A1 u + A2 u) (g := A3) (iA1.add iA2) iA3,
        MeasureTheory.integral_add (f := A1) (g := A2) iA1 iA2]
    have eA1 : (∫ u, A1 u) = 0 := by
      simp only [hA1]
      rw [MeasureTheory.integral_const_mul, PsiKernelBound.integral_gK_zero a lam ha hlam, mul_zero]
    have eA2 : (∫ u, A2 u) = 0 := by
      simp only [hA2]
      rw [MeasureTheory.integral_const_mul]
      have h := PsiKernelMinus.digamma_minus_integral_zero a lam (3/4) b ha hlam (by norm_num)
      simp only [PsiKernelMinus.wminus] at h
      rw [h, mul_zero]
    have eA4 : (∫ u, A4 u) = 0 := by
      simp only [hA4]
      rw [MeasureTheory.integral_const_mul, integral_gK_inv_neg_quarter a lam b ha hlam, mul_zero]
    have eA3 : ‖∫ u, A3 u‖ ≤ 100 := by
      simp only [hA3]
      rw [MeasureTheory.integral_const_mul, norm_mul, show ‖(1/2:ℂ)‖ = (1/2:ℝ) by norm_num]
      have hconv : (∫ u : ℝ, Complex.digamma (((3/4:ℝ):ℂ) + (((b - u)/2:ℝ):ℂ)*Complex.I) *
            PsiKernelBound.gK a lam u)
          = ∫ u : ℝ, Complex.digamma (((3/4:ℝ):ℂ) + (((b - u)/2:ℝ):ℂ)*Complex.I) *
              ((Complex.exp (-(((a : ℂ) + (u : ℂ) * Complex.I) * (lam : ℂ))) - 1) /
                (((a : ℂ) + (u : ℂ) * Complex.I)^2)) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with u
        simp only [PsiKernelBound.gK, div_eq_mul_inv]
      rw [hconv]
      have hb := Commons.Analysis.SpecialFunctions.Gamma.psi_kernel_bound a lam (3/4) b ha hlam
        (by norm_num)
      linarith
    rw [hstep]
    calc ‖∫ u : ℝ, A1 u + A2 u + A3 u - A4 u‖
        = ‖(∫ u, A1 u) + (∫ u, A2 u) + (∫ u, A3 u) - (∫ u, A4 u)‖ := by rw [hsplit]
      _ = ‖∫ u, A3 u‖ := by rw [eA1, eA2, eA4]; simp
      _ ≤ 100 := eA3
      _ ≤ 400 := by norm_num
  · -- ================= odd case =================
    have hOinv : (χ⁻¹).Odd := Odd_inv hO
    have hgχ : DirichletCharacter.gammaFactor χ = (fun z : ℂ => Complex.Gammaℝ (z + 1)) :=
      funext hO.gammaFactor_def
    have hgχinv : DirichletCharacter.gammaFactor χ⁻¹ = (fun z : ℂ => Complex.Gammaℝ (z + 1)) :=
      funext hOinv.gammaFactor_def
    have hA : ∀ u : ℝ, logDeriv (DirichletCharacter.gammaFactor χ⁻¹)
          ((3/2:ℝ) - ((b - u : ℝ) : ℂ) * Complex.I)
        = -(Complex.log (Real.pi : ℂ))/2
            + Complex.digamma (((5/4:ℝ):ℂ) - (((b - u)/2:ℝ):ℂ)*Complex.I)/2 := by
      intro u
      have hre : 0 < ((((3/2:ℝ):ℂ) - ((b - u : ℝ):ℂ)*Complex.I) + 1).re := by
        have h1 : (((3/2:ℝ):ℂ) - ((b - u : ℝ):ℂ)*Complex.I).re = 3/2 := by simp
        have h : ((((3/2:ℝ):ℂ) - ((b - u : ℝ):ℂ)*Complex.I) + 1).re = 5/2 := by
          rw [Complex.add_re, h1, Complex.one_re]; norm_num
        rw [h]; norm_num
      have hno : ∀ m : ℕ, ((((3/2:ℝ):ℂ) - ((b - u : ℝ):ℂ)*Complex.I) + 1)/2 ≠ -(m:ℂ) :=
        neq_neg_nat_of_re_pos hre
      have hdiv : ((((3/2:ℝ):ℂ) - ((b - u : ℝ):ℂ)*Complex.I) + 1)/2
          = (((5/4:ℝ):ℂ) - (((b - u)/2:ℝ):ℂ)*Complex.I) := by push_cast; ring
      rw [hgχinv, logDeriv_shift_GammaR _ hre,
        Commons.Analysis.SpecialFunctions.Gamma.logDeriv_GammaR_off_pole _ hno, hdiv]
    have hB : ∀ u : ℝ, logDeriv (DirichletCharacter.gammaFactor χ)
          (((-1/2:ℝ):ℂ) + ((b - u : ℝ) : ℂ) * Complex.I)
        = -(Complex.log (Real.pi : ℂ))/2
            + Complex.digamma (((1/4:ℝ):ℂ) + (((b - u)/2:ℝ):ℂ)*Complex.I)/2 := by
      intro u
      have hre : 0 < ((((-1/2:ℝ):ℂ) + ((b - u : ℝ):ℂ)*Complex.I) + 1).re := by
        have h1 : (((-1/2:ℝ):ℂ) + ((b - u : ℝ):ℂ)*Complex.I).re = -1/2 := by simp
        have h : ((((-1/2:ℝ):ℂ) + ((b - u : ℝ):ℂ)*Complex.I) + 1).re = 1/2 := by
          rw [Complex.add_re, h1, Complex.one_re]; norm_num
        rw [h]; norm_num
      have hno : ∀ m : ℕ, ((((-1/2:ℝ):ℂ) + ((b - u : ℝ):ℂ)*Complex.I) + 1)/2 ≠ -(m:ℂ) :=
        neq_neg_nat_of_re_pos hre
      have hdiv : ((((-1/2:ℝ):ℂ) + ((b - u : ℝ):ℂ)*Complex.I) + 1)/2
          = (((1/4:ℝ):ℂ) + (((b - u)/2:ℝ):ℂ)*Complex.I) := by push_cast; ring
      rw [hgχ, logDeriv_shift_GammaR _ hre,
        Commons.Analysis.SpecialFunctions.Gamma.logDeriv_GammaR_off_pole _ hno, hdiv]
    set B1 : ℝ → ℂ := fun u => (-(Complex.log (Real.pi : ℂ))) * PsiKernelBound.gK a lam u with hB1
    set B2 : ℝ → ℂ := fun u => (1/2) *
      (Complex.digamma (((5/4:ℝ):ℂ) - (((b - u)/2:ℝ):ℂ)*Complex.I) *
        PsiKernelBound.gK a lam u) with hB2
    set B3 : ℝ → ℂ := fun u => (1/2) *
      (Complex.digamma (((1/4:ℝ):ℂ) + (((b - u)/2:ℝ):ℂ)*Complex.I) *
        PsiKernelBound.gK a lam u) with hB3
    have hpt : ∀ u : ℝ,
        (logDeriv (DirichletCharacter.gammaFactor χ⁻¹)
              ((3/2:ℝ) - ((b - u : ℝ) : ℂ) * Complex.I)
          + logDeriv (DirichletCharacter.gammaFactor χ)
              (((-1/2:ℝ):ℂ) + ((b - u : ℝ) : ℂ) * Complex.I)) *
          ((Complex.exp (-(((a : ℂ) + (u : ℂ) * Complex.I) * (lam : ℂ))) - 1) /
            (((a : ℂ) + (u : ℂ) * Complex.I)^2))
        = B1 u + B2 u + B3 u := by
      intro u
      rw [hA u, hB u, hker u]
      simp only [hB1, hB2, hB3]
      ring
    have hstep : (∫ u : ℝ,
        (logDeriv (DirichletCharacter.gammaFactor χ⁻¹)
              ((3/2:ℝ) - ((b - u : ℝ) : ℂ) * Complex.I)
          + logDeriv (DirichletCharacter.gammaFactor χ)
              (((-1/2:ℝ):ℂ) + ((b - u : ℝ) : ℂ) * Complex.I)) *
          ((Complex.exp (-(((a : ℂ) + (u : ℂ) * Complex.I) * (lam : ℂ))) - 1) /
            (((a : ℂ) + (u : ℂ) * Complex.I)^2)))
        = ∫ u : ℝ, B1 u + B2 u + B3 u := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with u
      exact hpt u
    have iB1 : Integrable B1 := by
      rw [hB1]
      exact (PsiKernelBound.integrable_gK a lam ha).const_mul _
    have iB2 : Integrable B2 := by
      rw [hB2]
      exact (integrable_digamma_minus_mul_gK a lam b (5/4) ha (by norm_num) (by norm_num)).const_mul _
    have iB3 : Integrable B3 := by
      rw [hB3]
      exact (integrable_digamma_plus_mul_gK a lam b (1/4) ha (by norm_num) (by norm_num)).const_mul _
    have hsplit : (∫ u : ℝ, B1 u + B2 u + B3 u)
        = (∫ u, B1 u) + (∫ u, B2 u) + (∫ u, B3 u) := by
      rw [MeasureTheory.integral_add (f := fun u => B1 u + B2 u) (g := B3) (iB1.add iB2) iB3,
        MeasureTheory.integral_add (f := B1) (g := B2) iB1 iB2]
    have eB1 : (∫ u, B1 u) = 0 := by
      simp only [hB1]
      rw [MeasureTheory.integral_const_mul, PsiKernelBound.integral_gK_zero a lam ha hlam, mul_zero]
    have eB2 : (∫ u, B2 u) = 0 := by
      simp only [hB2]
      rw [MeasureTheory.integral_const_mul]
      have h := PsiKernelMinus.digamma_minus_integral_zero a lam (5/4) b ha hlam (by norm_num)
      simp only [PsiKernelMinus.wminus] at h
      rw [h, mul_zero]
    have eB3 : ‖∫ u, B3 u‖ ≤ 100 := by
      simp only [hB3]
      rw [MeasureTheory.integral_const_mul, norm_mul, show ‖(1/2:ℂ)‖ = (1/2:ℝ) by norm_num]
      have hconv : (∫ u : ℝ, Complex.digamma (((1/4:ℝ):ℂ) + (((b - u)/2:ℝ):ℂ)*Complex.I) *
            PsiKernelBound.gK a lam u)
          = ∫ u : ℝ, Complex.digamma (((1/4:ℝ):ℂ) + (((b - u)/2:ℝ):ℂ)*Complex.I) *
              ((Complex.exp (-(((a : ℂ) + (u : ℂ) * Complex.I) * (lam : ℂ))) - 1) /
                (((a : ℂ) + (u : ℂ) * Complex.I)^2)) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with u
        simp only [PsiKernelBound.gK, div_eq_mul_inv]
      rw [hconv]
      have hb := Commons.Analysis.SpecialFunctions.Gamma.psi_kernel_bound a lam (1/4) b ha hlam
        (by norm_num)
      linarith
    rw [hstep]
    calc ‖∫ u : ℝ, B1 u + B2 u + B3 u‖
        = ‖(∫ u, B1 u) + (∫ u, B2 u) + (∫ u, B3 u)‖ := by rw [hsplit]
      _ = ‖∫ u, B3 u‖ := by rw [eB1, eB2]; simp
      _ ≤ 100 := eB3
      _ ≤ 400 := by norm_num

end Commons.NumberTheory.DirichletCharacter
