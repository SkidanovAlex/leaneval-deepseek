import Mathlib
import Submission.Commons.NumberTheory.Zeta.chebyshevPsi_truncatedPerron
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Submission.Commons.NumberTheory.Zeta.zeta_strip_polyGrowth
import Submission.Commons.NumberTheory.Zeta.zeta_norm_le_const_of_three_le_re
import Submission.Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound
import Submission.Commons.Analysis.Complex.rectIntegral_sub_inv_inside
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.NormNum.RealSqrt

open Complex Filter Set MeasureTheory intervalIntegral
open scoped Real Topology BigOperators

namespace Commons.NumberTheory.Zeta

noncomputable section

def psiIntF (x : ℝ) (s : ℂ) : ℂ :=
  -(deriv riemannZeta s) / riemannZeta s * (x : ℂ) ^ s / s

def rectInt (z w : ℂ) (f : ℂ → ℂ) : ℂ :=
  (∫ (x : ℝ) in z.re..w.re, f (x + z.im * Complex.I)) -
    (∫ (x : ℝ) in z.re..w.re, f (x + w.im * Complex.I)) +
    Complex.I • (∫ (y : ℝ) in z.im..w.im, f (w.re + y * Complex.I)) -
    Complex.I • (∫ (y : ℝ) in z.im..w.im, f (z.re + y * Complex.I))

def zeta1LogDeriv (s : ℂ) : ℂ := deriv riemannZeta₁ s / riemannZeta₁ s

def hFunc (x : ℝ) (s : ℂ) : ℂ :=
  dslope (fun w : ℂ => (x : ℂ) ^ w) 1 s - (x : ℂ) ^ s / s - zeta1LogDeriv s * ((x : ℂ) ^ s / s)

lemma cpow_eq_exp_log_mul {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x : ℂ) ^ s = Complex.exp ((Real.log x : ℂ) * s) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
  rw [Complex.cpow_def_of_ne_zero hx0]
  congr 1
  rw [Complex.ofReal_log (le_of_lt hx)]

lemma cpow_differentiable {x : ℝ} (hx : 0 < x) : Differentiable ℂ (fun s : ℂ => (x : ℂ) ^ s) := by
  have heq : (fun s : ℂ => (x : ℂ) ^ s) = fun s : ℂ => Complex.exp ((Real.log x : ℂ) * s) := by
    funext s
    exact cpow_eq_exp_log_mul hx s
  rw [heq]
  fun_prop

lemma cpow_div_self_differentiableOn {x : ℝ} (hx : 0 < x) :
    DifferentiableOn ℂ (fun s : ℂ => (x : ℂ) ^ s / s) {s : ℂ | s ≠ 0} := by
  refine DifferentiableOn.div (c := fun s : ℂ => (x : ℂ) ^ s) (d := fun s : ℂ => s)
    (s := {s : ℂ | s ≠ 0}) ?_ ?_ ?_
  · intro z hz
    exact ((cpow_differentiable hx).differentiableAt (x := z)).differentiableWithinAt
  · exact differentiableOn_id
  · intro s hs
    exact hs

lemma cpow_dslope_differentiable {x : ℝ} (hx : 0 < x) :
    Differentiable ℂ (dslope (fun s : ℂ => (x : ℂ) ^ s) 1) := by
  have hd : DifferentiableOn ℂ (fun s : ℂ => (x : ℂ) ^ s) univ := by
    intro s hs
    exact ((cpow_differentiable hx).differentiableAt (x := s)).differentiableWithinAt
  have hd' : DifferentiableOn ℂ (dslope (fun s : ℂ => (x : ℂ) ^ s) 1) univ := by
    exact (Complex.differentiableOn_dslope (f := (fun s : ℂ => (x : ℂ) ^ s)) (c := (1 : ℂ))
      (s := univ) (by simp : univ ∈ 𝓝 (1 : ℂ))).mpr hd
  intro s
  exact hd'.differentiableAt (x := s) (by simp)

lemma dslope_cpow_eq_div {x : ℝ} {s : ℂ} (hs : s ≠ 1) :
    dslope (fun w : ℂ => (x : ℂ) ^ w) 1 s = ((x : ℂ) ^ s - (x : ℂ)) / (s - 1) := by
  rw [dslope_of_ne (fun w : ℂ => (x : ℂ) ^ w) hs]
  rw [slope_def_module]
  simp [div_eq_mul_inv, mul_comm]

/-! ## algebraic identity ζ'/ζ = −(s−1)⁻¹ + ζ₁'/ζ₁ -/

lemma deriv_zeta_div_zeta_eq (s : ℂ) (hs : s ≠ 1) (hz1 : riemannZeta₁ s ≠ 0) :
    deriv riemannZeta s / riemannZeta s = -(s - 1)⁻¹ + deriv riemannZeta₁ s / riemannZeta₁ s := by
  have hζ : riemannZeta s ≠ 0 := by
    rw [riemannZeta_eq_inv_sub_mul hs]
    exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hs)) hz1
  have hderiv : deriv riemannZeta s = -(s - 1)⁻¹ ^ 2 * riemannZeta₁ s + (s - 1)⁻¹ * deriv riemannZeta₁ s :=
    deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs
  rw [hderiv]
  rw [riemannZeta_eq_inv_sub_mul hs]
  field_simp [hζ, hz1, sub_ne_zero.mpr hs]

lemma ne_zero_of_half_lt_re {s : ℂ} (hs : (1 / 2 : ℝ) < s.re) : s ≠ 0 := by
  intro hs0
  have hre : s.re = 0 := congrArg Complex.re hs0
  linarith

lemma cpow_div_self_differentiableOn_re_gt (x : ℝ) (hx : 0 < x) :
    DifferentiableOn ℂ (fun s : ℂ => (x : ℂ) ^ s / s) {s : ℂ | (1 / 2 : ℝ) < s.re} := by
  intro s hs
  exact ((cpow_div_self_differentiableOn (x := x) hx).differentiableAt (x := s)
    (isOpen_ne.mem_nhds (ne_zero_of_half_lt_re hs))).differentiableWithinAt

lemma rectInt_congr_boundary {z w : ℂ} {f g : ℂ → ℂ}
    (h1 : ∀ x ∈ Set.uIcc z.re w.re, f (x + z.im * Complex.I) = g (x + z.im * Complex.I))
    (h2 : ∀ x ∈ Set.uIcc z.re w.re, f (x + w.im * Complex.I) = g (x + w.im * Complex.I))
    (h3 : ∀ y ∈ Set.uIcc z.im w.im, f (w.re + y * Complex.I) = g (w.re + y * Complex.I))
    (h4 : ∀ y ∈ Set.uIcc z.im w.im, f (z.re + y * Complex.I) = g (z.re + y * Complex.I)) :
    rectInt z w f = rectInt z w g := by
  unfold rectInt
  have e1 : (∫ (x : ℝ) in z.re..w.re, f (x + z.im * Complex.I)) =
      (∫ (x : ℝ) in z.re..w.re, g (x + z.im * Complex.I)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact h1 x hx
  have e2 : (∫ (x : ℝ) in z.re..w.re, f (x + w.im * Complex.I)) =
      (∫ (x : ℝ) in z.re..w.re, g (x + w.im * Complex.I)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact h2 x hx
  have e3 : (∫ (y : ℝ) in z.im..w.im, f (w.re + y * Complex.I)) =
      (∫ (y : ℝ) in z.im..w.im, g (w.re + y * Complex.I)) := by
    apply intervalIntegral.integral_congr
    intro y hy
    exact h3 y hy
  have e4 : (∫ (y : ℝ) in z.im..w.im, f (z.re + y * Complex.I)) =
      (∫ (y : ℝ) in z.im..w.im, g (z.re + y * Complex.I)) := by
    apply intervalIntegral.integral_congr
    intro y hy
    exact h4 y hy
  rw [e1, e2, e3, e4]

lemma rectInt_add {z w : ℂ} {f g : ℂ → ℂ}
    (hf : IntervalIntegrable (fun x : ℝ => f (x + z.im * Complex.I)) volume z.re w.re)
    (hg : IntervalIntegrable (fun x : ℝ => g (x + z.im * Complex.I)) volume z.re w.re)
    (hf2 : IntervalIntegrable (fun x : ℝ => f (x + w.im * Complex.I)) volume z.re w.re)
    (hg2 : IntervalIntegrable (fun x : ℝ => g (x + w.im * Complex.I)) volume z.re w.re)
    (hf3 : IntervalIntegrable (fun y : ℝ => f (w.re + y * Complex.I)) volume z.im w.im)
    (hg3 : IntervalIntegrable (fun y : ℝ => g (w.re + y * Complex.I)) volume z.im w.im)
    (hf4 : IntervalIntegrable (fun y : ℝ => f (z.re + y * Complex.I)) volume z.im w.im)
    (hg4 : IntervalIntegrable (fun y : ℝ => g (z.re + y * Complex.I)) volume z.im w.im) :
    rectInt z w (fun s => f s + g s) = rectInt z w f + rectInt z w g := by
  unfold rectInt
  have e1 : (∫ (x : ℝ) in z.re..w.re, (f (x + z.im * Complex.I) + g (x + z.im * Complex.I))) =
      (∫ (x : ℝ) in z.re..w.re, f (x + z.im * Complex.I)) + (∫ (x : ℝ) in z.re..w.re, g (x + z.im * Complex.I)) := by
    simpa only [Pi.add_apply, add_comm, add_left_comm, add_assoc] using
      (intervalIntegral.integral_add hf hg)
  have e2 : (∫ (x : ℝ) in z.re..w.re, (f (x + w.im * Complex.I) + g (x + w.im * Complex.I))) =
      (∫ (x : ℝ) in z.re..w.re, f (x + w.im * Complex.I)) + (∫ (x : ℝ) in z.re..w.re, g (x + w.im * Complex.I)) := by
    simpa using (intervalIntegral.integral_add hf2 hg2)
  have e3 : (∫ (y : ℝ) in z.im..w.im, (f (w.re + y * Complex.I) + g (w.re + y * Complex.I))) =
      (∫ (y : ℝ) in z.im..w.im, f (w.re + y * Complex.I)) + (∫ (y : ℝ) in z.im..w.im, g (w.re + y * Complex.I)) := by
    simpa using (intervalIntegral.integral_add hf3 hg3)
  have e4 : (∫ (y : ℝ) in z.im..w.im, (f (z.re + y * Complex.I) + g (z.re + y * Complex.I))) =
      (∫ (y : ℝ) in z.im..w.im, f (z.re + y * Complex.I)) + (∫ (y : ℝ) in z.im..w.im, g (z.re + y * Complex.I)) := by
    simpa using (intervalIntegral.integral_add hf4 hg4)
  rw [e1, e2, e3, e4]
  simp only [smul_eq_mul]
  ring

lemma rectInt_const_mul {z w : ℂ} (c : ℂ) (f : ℂ → ℂ) :
    rectInt z w (fun s : ℂ => c * f s) = c * rectInt z w f := by
  unfold rectInt
  have e1 : (∫ (x : ℝ) in z.re..w.re, c * f (x + z.im * Complex.I)) =
      c * (∫ (x : ℝ) in z.re..w.re, f (x + z.im * Complex.I)) := by
    simpa using (intervalIntegral.integral_const_mul c (fun x : ℝ => f (x + z.im * Complex.I)))
  have e2 : (∫ (x : ℝ) in z.re..w.re, c * f (x + w.im * Complex.I)) =
      c * (∫ (x : ℝ) in z.re..w.re, f (x + w.im * Complex.I)) := by
    simpa using (intervalIntegral.integral_const_mul c (fun x : ℝ => f (x + w.im * Complex.I)))
  have e3 : (∫ (y : ℝ) in z.im..w.im, c * f (w.re + y * Complex.I)) =
      c * (∫ (y : ℝ) in z.im..w.im, f (w.re + y * Complex.I)) := by
    simpa using (intervalIntegral.integral_const_mul c (fun y : ℝ => f (w.re + y * Complex.I)))
  have e4 : (∫ (y : ℝ) in z.im..w.im, c * f (z.re + y * Complex.I)) =
      c * (∫ (y : ℝ) in z.im..w.im, f (z.re + y * Complex.I)) := by
    simpa using (intervalIntegral.integral_const_mul c (fun y : ℝ => f (z.re + y * Complex.I)))
  rw [e1, e2, e3, e4]
  simp only [smul_eq_mul]
  ring

lemma exp8_gt_one : (1 : ℝ) < Real.exp 8 := by
  have h := (Real.exp_lt_exp (x := 0) (y := 8)).2 (by norm_num : (0 : ℝ) < 8)
  simpa using h

lemma logx_pos_of_exp_eight_le {x : ℝ} (hx : Real.exp 8 ≤ x) : 0 < Real.log x := by
  have h1 : 1 < x := lt_of_lt_of_le exp8_gt_one hx
  exact Real.log_pos h1

lemma logx_ge_eight_of_exp_eight_le {x : ℝ} (hx : Real.exp 8 ≤ x) : (8 : ℝ) ≤ Real.log x := by
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 8) hx
  have hle : Real.log (Real.exp 8) ≤ Real.log x := Real.log_le_log (Real.exp_pos 8) hx
  rwa [Real.log_exp] at hle

lemma one_div_logx_pos {x : ℝ} (hx : Real.exp 8 ≤ x) : 0 < 1 / Real.log x := by
  exact one_div_pos.mpr (logx_pos_of_exp_eight_le hx)

lemma one_div_logx_lt_half {x : ℝ} (hx : Real.exp 8 ≤ x) : 1 / Real.log x < 1 / 2 := by
  have hlog : 8 ≤ Real.log x := logx_ge_eight_of_exp_eight_le hx
  have hL : (0 : ℝ) < Real.log x := by linarith
  exact (div_lt_div_iff₀ hL (by norm_num : (0:ℝ) < 2)).2 (by nlinarith)

lemma leftRe_gt_half {x : ℝ} (hx : Real.exp 8 ≤ x) : (1 / 2 : ℝ) < 1 / 2 + 1 / Real.log x := by
  exact lt_add_of_pos_right (1 / 2 : ℝ) (one_div_logx_pos hx)

lemma leftRe_lt_one {x : ℝ} (hx : Real.exp 8 ≤ x) : 1 / 2 + 1 / Real.log x < 1 := by
  linarith [one_div_logx_lt_half hx]

lemma rightRe_gt_one {x : ℝ} (hx : Real.exp 8 ≤ x) : (1 : ℝ) < 1 + 1 / Real.log x := by
  exact lt_add_of_pos_right (1 : ℝ) (one_div_logx_pos hx)

lemma perronRe_le_two {x : ℝ} (hx : Real.exp 8 ≤ x) : 1 + 1 / Real.log x ≤ 2 := by
  have hlog : 8 ≤ Real.log x := logx_ge_eight_of_exp_eight_le hx
  have h : (1 / Real.log x : ℝ) ≤ 1 / 8 := by
    have hL : (0:ℝ) < Real.log x := by linarith
    rw [div_le_div_iff₀ hL (by norm_num : (0:ℝ) < 8)]
    nlinarith
  linarith

lemma ne_one_of_re_ne_one {s : ℂ} (h : s.re ≠ 1) : s ≠ 1 := by
  intro hs
  apply h
  rw [hs]
  simp

lemma ne_one_of_im_ne_zero {s : ℂ} (h : s.im ≠ 0) : s ≠ 1 := by
  intro hs
  apply h
  rw [hs]
  simp

def perronRe (x : ℝ) : ℝ := 1 + 1 / Real.log x
def leftRe (x : ℝ) : ℝ := 1 / 2 + 1 / Real.log x

def zetaRectZ (x : ℝ) (T : ℝ) : ℂ := ((leftRe x : ℝ) : ℂ) - Complex.I * (T : ℂ)
def zetaRectW (x : ℝ) (T : ℝ) : ℂ := ((perronRe x : ℝ) : ℂ) + Complex.I * (T : ℂ)

lemma zetaRectZ_re (x T : ℝ) : (zetaRectZ x T).re = leftRe x := by
  simp [zetaRectZ, leftRe]
lemma zetaRectZ_im (x T : ℝ) : (zetaRectZ x T).im = -T := by
  simp [zetaRectZ]
lemma zetaRectW_re (x T : ℝ) : (zetaRectW x T).re = perronRe x := by
  simp [zetaRectW, perronRe]
lemma zetaRectW_im (x T : ℝ) : (zetaRectW x T).im = T := by
  simp [zetaRectW]

lemma leftRe_lt_perronRe (x : ℝ) : leftRe x < perronRe x := by
  dsimp [leftRe, perronRe]
  linarith

lemma zetaRect_re_lt (x T : ℝ) : (zetaRectZ x T).re < (zetaRectW x T).re := by
  rw [zetaRectZ_re, zetaRectW_re]
  exact leftRe_lt_perronRe x

lemma zetaRect_im_lt {T : ℝ} (hT : 0 < T) (x : ℝ) : (zetaRectZ x T).im < (zetaRectW x T).im := by
  rw [zetaRectZ_im, zetaRectW_im]
  linarith

lemma rectInt_sub_inv_one {z w : ℂ} (hzre : z.re < w.re) (hzim : z.im < w.im)
    (huin : z.re < (1 : ℂ).re ∧ (1 : ℂ).re < w.re ∧ z.im < (1 : ℂ).im ∧ (1 : ℂ).im < w.im) :
    rectInt z w (fun s : ℂ => (s - (1 : ℂ))⁻¹) = (2 : ℂ) * (Real.pi : ℂ) * Complex.I := by
  simpa [rectInt] using (Commons.Analysis.Complex.rectIntegral_sub_inv_inside (z := z) (w := w) (u := (1 : ℂ)) hzre hzim huin)

lemma rectInt_polar_residue {z w : ℂ} (c : ℂ) (hzre : z.re < w.re) (hzim : z.im < w.im)
    (huin : z.re < (1 : ℂ).re ∧ (1 : ℂ).re < w.re ∧ z.im < (1 : ℂ).im ∧ (1 : ℂ).im < w.im) :
    rectInt z w (fun s : ℂ => c / (s - (1 : ℂ))) =
      c * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
  calc
    rectInt z w (fun s : ℂ => c / (s - (1 : ℂ)))
        = rectInt z w (fun s : ℂ => c * (s - (1 : ℂ))⁻¹) := by
          apply congrArg (rectInt z w)
          funext s
          exact div_eq_mul_inv c (s - (1 : ℂ))
    _ = c * rectInt z w (fun s : ℂ => (s - (1 : ℂ))⁻¹) := rectInt_const_mul c (fun s : ℂ => (s - (1 : ℂ))⁻¹)
    _ = c * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by rw [rectInt_sub_inv_one hzre hzim huin]

lemma edge_cont_horiz {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hcont : ContinuousOn f U)
    {a b r : ℝ} (hU' : ∀ u : ℝ, u ∈ Set.uIcc a b → (u : ℂ) + (r : ℂ) * Complex.I ∈ U) :
    ContinuousOn (fun u : ℝ => f ((u : ℂ) + (r : ℂ) * Complex.I)) (Set.uIcc a b) := by
  intro u0 hu0
  have hpt : (u0 : ℂ) + (r : ℂ) * Complex.I ∈ U := hU' u0 hu0
  have hc : ContinuousAt (fun u : ℝ => (u : ℂ) + (r : ℂ) * Complex.I) u0 := by fun_prop
  have hf : ContinuousAt f ((u0 : ℂ) + (r : ℂ) * Complex.I) := hcont.continuousAt (hU.mem_nhds hpt)
  have hg : ContinuousAt (fun u : ℝ => f ((u : ℂ) + (r : ℂ) * Complex.I)) u0 := by
    exact ContinuousAt.comp (f := fun u : ℝ => (u : ℂ) + (r : ℂ) * Complex.I) (x := u0) (g := f) hf hc
  exact hg.continuousWithinAt

lemma edge_integrable_horiz {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hcont : ContinuousOn f U)
    {a b r : ℝ} (hU' : ∀ u : ℝ, u ∈ Set.uIcc a b → (u : ℂ) + (r : ℂ) * Complex.I ∈ U) :
    IntervalIntegrable (fun u : ℝ => f ((u : ℂ) + (r : ℂ) * Complex.I)) volume a b := by
  exact (ContinuousOn.intervalIntegrable (edge_cont_horiz (U := U) hU hcont hU'))

lemma edge_cont_vert {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hcont : ContinuousOn f U)
    {c d a : ℝ} (hU' : ∀ v : ℝ, v ∈ Set.uIcc c d → (a : ℂ) + (v : ℂ) * Complex.I ∈ U) :
    ContinuousOn (fun v : ℝ => f ((a : ℂ) + (v : ℂ) * Complex.I)) (Set.uIcc c d) := by
  intro v0 hv0
  have hpt : (a : ℂ) + (v0 : ℂ) * Complex.I ∈ U := hU' v0 hv0
  have hc : ContinuousAt (fun v : ℝ => (a : ℂ) + (v : ℂ) * Complex.I) v0 := by fun_prop
  have hf : ContinuousAt f ((a : ℂ) + (v0 : ℂ) * Complex.I) := hcont.continuousAt (hU.mem_nhds hpt)
  have hg : ContinuousAt (fun v : ℝ => f ((a : ℂ) + (v : ℂ) * Complex.I)) v0 := by
    exact ContinuousAt.comp (f := fun v : ℝ => (a : ℂ) + (v : ℂ) * Complex.I) (x := v0) (g := f) hf hc
  exact hg.continuousWithinAt

lemma edge_integrable_vert {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hcont : ContinuousOn f U)
    {c d a : ℝ} (hU' : ∀ v : ℝ, v ∈ Set.uIcc c d → (a : ℂ) + (v : ℂ) * Complex.I ∈ U) :
    IntervalIntegrable (fun v : ℝ => f ((a : ℂ) + (v : ℂ) * Complex.I)) volume c d := by
  exact (ContinuousOn.intervalIntegrable (edge_cont_vert (U := U) hU hcont hU'))
lemma continuousOn_polar (x : ℝ) : ContinuousOn (fun s : ℂ => (x : ℂ) / (s - (1 : ℂ))) {s : ℂ | s ≠ 1} := by
  intro s hs
  have hc_sub : ContinuousAt (fun w : ℂ => w - (1 : ℂ)) s := by fun_prop
  have hc_inv : ContinuousAt (fun w : ℂ => (w - (1 : ℂ))⁻¹) s := (hc_sub.inv₀ (sub_ne_zero.mpr hs))
  have hc : ContinuousAt (fun w : ℂ => (x : ℂ) * (w - (1 : ℂ))⁻¹) s := by
    exact hc_inv.const_mul (x : ℂ)
  have hEq : (fun w : ℂ => (x : ℂ) * (w - (1 : ℂ))⁻¹) = fun w : ℂ => (x : ℂ) / (w - (1 : ℂ)) := by
    funext w
    exact div_eq_mul_inv (x : ℂ) (w - (1 : ℂ))
  simpa [hEq] using hc.continuousWithinAt

lemma mem_rect_ge_left {x T : ℝ} (hx : Real.exp 8 ≤ x) {s : ℂ}
    (hs : s ∈ (Set.uIcc (zetaRectZ x T).re (zetaRectW x T).re ×ℂ
                Set.uIcc (zetaRectZ x T).im (zetaRectW x T).im)) :
    (1 / 2 : ℝ) < s.re := by
  have hsreI := (Complex.mem_reProdIm.mp hs).1
  have hle : (zetaRectZ x T).re ≤ (zetaRectW x T).re := le_of_lt (zetaRect_re_lt x T)
  have hsre' : s.re ∈ Set.Icc (zetaRectZ x T).re (zetaRectW x T).re := by
    rw [Set.uIcc_of_le hle] at hsreI
    exact hsreI
  have hge : (zetaRectZ x T).re ≤ s.re := (Set.mem_Icc.mp hsre').1
  have hzr : (zetaRectZ x T).re = leftRe x := zetaRectZ_re x T
  rw [hzr] at hge
  have hle2 : (1 / 2 : ℝ) < leftRe x := leftRe_gt_half hx
  linarith

/-- The right-edge (Perron) vertical integral `∫_{−T}^{T} f(σ₁ + it) dt`. -/
def perronRight (x T : ℝ) : ℂ :=
  (∫ (t : ℝ) in -T..T, psiIntF x ((perronRe x : ℂ) + (t : ℂ) * Complex.I))

/-- The truncated Perron integral with the `−ζ'/ζ` integrand at `Re = perronRe x`. -/
def perronZeta (x T : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) * perronRight x T

/-- Top horizontal edge integral: `∫_{β}^{σ₁} f(u + iT) du`. -/
def topInt (x T : ℝ) : ℂ :=
  (∫ (u : ℝ) in leftRe x..perronRe x, psiIntF x ((u : ℂ) + (T : ℂ) * Complex.I))

/-- Bottom horizontal edge integral: `∫_{β}^{σ₁} f(u − iT) du`. -/
def botInt (x T : ℝ) : ℂ :=
  (∫ (u : ℝ) in leftRe x..perronRe x, psiIntF x ((u : ℂ) - (T : ℂ) * Complex.I))

/-- Left vertical edge integral: `∫_{−T}^{T} f(β + it) dt`. -/
def leftInt (x T : ℝ) : ℂ :=
  (∫ (t : ℝ) in -T..T, psiIntF x ((leftRe x : ℂ) + (t : ℂ) * Complex.I))

/-- Norm of the integrand `f(s) = −ζ'/ζ(s)·x^s/s`. -/
lemma psiIntF_norm {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ‖psiIntF x s‖ = ‖deriv riemannZeta s / riemannZeta s‖ * (x : ℝ) ^ s.re / ‖s‖ := by
  dsimp [psiIntF]
  have h1 : ‖(-(deriv riemannZeta s)) / riemannZeta s‖ = ‖deriv riemannZeta s / riemannZeta s‖ := by
    rw [norm_div, norm_div, norm_neg]
  calc
    ‖(-(deriv riemannZeta s)) / riemannZeta s * (x : ℂ) ^ s / s‖
        = ‖(-(deriv riemannZeta s)) / riemannZeta s‖ * ‖(x : ℂ) ^ s‖ / ‖s‖ := by
          rw [norm_div, norm_mul]
    _ = ‖deriv riemannZeta s / riemannZeta s‖ * ‖(x : ℂ) ^ s‖ / ‖s‖ := by rw [h1]
    _ = ‖deriv riemannZeta s / riemannZeta s‖ * (x : ℝ) ^ s.re / ‖s‖ := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx s]



lemma psiIntF_horiz_le (h : RiemannHypothesis) {C : ℝ} (hC0 : 0 < C)
    (hC : ∀ (δ σ t : ℝ), 0 < δ → δ ≤ 1 → (1 / 2 + δ) ≤ σ → σ ≤ 2 →
      (1 / 4 ≤ ‖(((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) - 1‖) →
      ‖(deriv riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)) /
          riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)‖ ≤
        C * (1 + 1 / δ) ^ 3 * (Real.log (|t| + 3) + 1) ^ 3)
    {x : ℝ} (hx : Real.exp 8 ≤ x) {T : ℝ} (hT : 2 ≤ T) {u r : ℝ}
    (hu1 : leftRe x ≤ u) (hu2 : u ≤ perronRe x) (hr : |r| = T) :
    ‖psiIntF x ((u : ℂ) + Complex.I * (r : ℂ))‖ ≤
      C * (1 + Real.log x) ^ 3 * (Real.log (T + 3) + 1) ^ 3 * (x : ℝ) ^ u / T := by
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 8) hx
  have hTpos : 0 < T := by linarith
  have hlog1 : 1 ≤ Real.log x := by linarith [logx_ge_eight_of_exp_eight_le hx]
  let δ : ℝ := 1 / Real.log x
  let s : ℂ := (u : ℂ) + Complex.I * (r : ℂ)
  have hδ0 : 0 < δ := by dsimp [δ]; exact one_div_logx_pos hx
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    have hL : 0 < Real.log x := by linarith
    exact (div_le_one hL).2 hlog1
  have hσ1 : (1 / 2 + δ) ≤ u := by
    dsimp [δ]
    simpa [leftRe] using hu1
  have hσ2 : u ≤ 2 := le_trans hu2 (perronRe_le_two hx)
  have him : |r| ≤ ‖s - 1‖ := by
    have himv : (s - 1).im = r := by dsimp [s]; simp
    calc
      |r| = |(s - 1).im| := by rw [himv]
      _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm (s - 1)
  have hdist : (1 / 4 : ℝ) ≤ ‖s - 1‖ := by
    calc
      (1 / 4 : ℝ) ≤ T := by linarith
      _ = |r| := hr.symm
      _ ≤ ‖s - 1‖ := him
  have hstrip := hC δ u r hδ0 hδ1 hσ1 hσ2 hdist
  have hnorm : T ≤ ‖s‖ := by
    calc
      T = |r| := hr.symm
      _ ≤ ‖s‖ := by
        have himv : s.im = r := by dsimp [s]; simp
        calc |r| = |s.im| := by rw [himv]
             _ ≤ ‖s‖ := Complex.abs_im_le_norm s
  have h1δ : 1 + 1 / δ = 1 + Real.log x := by
    dsimp [δ]
    field_simp [logx_pos_of_exp_eight_le hx]
  have hlogr : Real.log (|r| + 3) = Real.log (T + 3) := by
    have habs : |r| + 3 = T + 3 := by linarith
    rw [habs]
  have hsre : s.re = u := by dsimp [s]; simp
  have hnonneg1 : 0 ≤ (x : ℝ) ^ s.re / ‖s‖ := by
    exact div_nonneg (Real.rpow_nonneg (le_of_lt hxpos) s.re) (norm_nonneg s)
  have hnonneg2 : 0 ≤ (1 + 1 / δ) ^ 3 := by positivity
  have hnonneg3 : 0 ≤ (Real.log (|r| + 3) + 1) ^ 3 := by
    exact pow_nonneg (by have hlogarg : 0 ≤ Real.log (|r| + 3) := Real.log_nonneg (by linarith : (1 : ℝ) ≤ |r| + 3); linarith) 3
  have hfac : 0 ≤ C * (1 + 1 / δ) ^ 3 * (Real.log (|r| + 3) + 1) ^ 3 * (x : ℝ) ^ u := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hC0) hnonneg2) hnonneg3)
      (Real.rpow_nonneg (le_of_lt hxpos) u)
  calc
    ‖psiIntF x s‖ = ‖deriv riemannZeta s / riemannZeta s‖ * (x : ℝ) ^ s.re / ‖s‖ := psiIntF_norm hxpos s
    _ ≤ (C * (1 + 1 / δ) ^ 3 * (Real.log (|r| + 3) + 1) ^ 3) * (x : ℝ) ^ s.re / ‖s‖ := by
          have hb : 0 ≤ (x : ℝ) ^ s.re := Real.rpow_nonneg (le_of_lt hxpos) s.re
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hstrip hb) (norm_nonneg s)
    _ = (C * (1 + 1 / δ) ^ 3 * (Real.log (|r| + 3) + 1) ^ 3) * (x : ℝ) ^ u / ‖s‖ := by rw [hsre]
    _ ≤ (C * (1 + 1 / δ) ^ 3 * (Real.log (|r| + 3) + 1) ^ 3) * (x : ℝ) ^ u / T := by
          exact div_le_div_of_nonneg_left hfac hTpos hnorm
    _ ≤ C * (1 + Real.log x) ^ 3 * (Real.log (T + 3) + 1) ^ 3 * (x : ℝ) ^ u / T := by
          have hrepl : C * (1 + 1 / δ) ^ 3 * (Real.log (|r| + 3) + 1) ^ 3 * (x : ℝ) ^ u / T =
              C * (1 + Real.log x) ^ 3 * (Real.log (T + 3) + 1) ^ 3 * (x : ℝ) ^ u / T := by
            rw [h1δ, hlogr]
          rw [hrepl]

lemma psiIntF_left_le (h : RiemannHypothesis) {C : ℝ} (hC0 : 0 < C)
    (hC : ∀ (δ σ t : ℝ), 0 < δ → δ ≤ 1 → (1 / 2 + δ) ≤ σ → σ ≤ 2 →
      (1 / 4 ≤ ‖(((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) - 1‖) →
      ‖(deriv riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)) /
          riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)‖ ≤
        C * (1 + 1 / δ) ^ 3 * (Real.log (|t| + 3) + 1) ^ 3)
    {x : ℝ} (hx : Real.exp 8 ≤ x) {t : ℝ} :
    ‖psiIntF x ((leftRe x : ℂ) + Complex.I * (t : ℂ))‖ ≤
      C * (1 + Real.log x) ^ 3 * (Real.log (|t| + 3) + 1) ^ 3 *
        (x : ℝ) ^ leftRe x / ‖((leftRe x : ℂ) + Complex.I * (t : ℂ))‖ := by
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 8) hx
  have hlog1 : 1 ≤ Real.log x := by linarith [logx_ge_eight_of_exp_eight_le hx]
  have hlog4 : 4 ≤ Real.log x := by linarith [logx_ge_eight_of_exp_eight_le hx]
  let δ : ℝ := 1 / Real.log x
  let s : ℂ := (leftRe x : ℂ) + Complex.I * (t : ℂ)
  have hδ0 : 0 < δ := by dsimp [δ]; exact one_div_logx_pos hx
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    have hL : 0 < Real.log x := by linarith
    exact (div_le_one hL).2 hlog1
  have hσ1 : (1 / 2 + δ) ≤ leftRe x := by
    dsimp [δ]
    simp [leftRe]
  have hσ2 : leftRe x ≤ 2 := by
    have h : leftRe x < 1 := leftRe_lt_one hx
    linarith
  have hfrac : 1 / Real.log x ≤ 1 / 4 := by
    have hL : 0 < Real.log x := by linarith
    rw [div_le_iff₀ hL]
    nlinarith [hlog4]
  have hbase : (1 / 4 : ℝ) ≤ 1 / 2 - 1 / Real.log x := by nlinarith [hfrac]
  have hdist : (1 / 4 : ℝ) ≤ ‖s - 1‖ := by
    have hreabs : |(s - 1).re| = 1 / 2 - 1 / Real.log x := by
      have hval : (s - 1).re = leftRe x - 1 := by dsimp [s]; simp
      rw [hval]
      have hnonpos : leftRe x - 1 ≤ 0 := by
        dsimp [leftRe]
        have h12 : 1 / Real.log x ≤ 1 / 2 := by nlinarith [hfrac]
        linarith
      have habs : |leftRe x - 1| = -(leftRe x - 1) := abs_of_nonpos hnonpos
      rw [habs]
      dsimp [leftRe]
      ring
    calc
      (1 / 4 : ℝ) ≤ 1 / 2 - 1 / Real.log x := hbase
      _ = |(s - 1).re| := hreabs.symm
      _ ≤ ‖s - 1‖ := Complex.abs_re_le_norm (s - 1)
  have hstrip := hC δ (leftRe x) t hδ0 hδ1 hσ1 hσ2 hdist
  have h1δ : 1 + 1 / δ = 1 + Real.log x := by
    dsimp [δ]
    field_simp [logx_pos_of_exp_eight_le hx]
  have hsre : s.re = leftRe x := by dsimp [s]; simp
  have hb : 0 ≤ (x : ℝ) ^ leftRe x / ‖s‖ := by
    exact div_nonneg (Real.rpow_nonneg (le_of_lt hxpos) (leftRe x)) (norm_nonneg s)
  calc
    ‖psiIntF x s‖ = ‖deriv riemannZeta s / riemannZeta s‖ * (x : ℝ) ^ s.re / ‖s‖ := psiIntF_norm hxpos s
    _ = ‖deriv riemannZeta s / riemannZeta s‖ * ((x : ℝ) ^ leftRe x / ‖s‖) := by
          rw [hsre]
          have hsne : s ≠ 0 := by
            intro hs0
            have hre : s.re = 0 := congrArg Complex.re hs0
            have hre' : s.re = leftRe x := by dsimp [s]; simp
            have hgt : (1 / 2 : ℝ) < leftRe x := leftRe_gt_half hx
            linarith
          field_simp [norm_ne_zero_iff.mpr hsne] <;> ring
    _ ≤ (C * (1 + 1 / δ) ^ 3 * (Real.log (|t| + 3) + 1) ^ 3) * ((x : ℝ) ^ leftRe x / ‖s‖) := by
          exact mul_le_mul_of_nonneg_right hstrip hb
    _ = C * (1 + Real.log x) ^ 3 * (Real.log (|t| + 3) + 1) ^ 3 * (x : ℝ) ^ leftRe x / ‖s‖ := by
          have hrepl : (C * (1 + 1 / δ) ^ 3 * (Real.log (|t| + 3) + 1) ^ 3) * ((x : ℝ) ^ leftRe x / ‖s‖) =
              C * (1 + Real.log x) ^ 3 * (Real.log (|t| + 3) + 1) ^ 3 * (x : ℝ) ^ leftRe x / ‖s‖ := by
            rw [h1δ]
            ring
          rw [hrepl]


/-- The bound function `t ↦ (log(|t|+3)+1)³/√(β²+t²)` is continuous for `0 < β`. -/
lemma logWeightBound_continuous {β : ℝ} (hβ0 : 0 < β) :
    Continuous (fun t : ℝ => (Real.log (|t| + 3) + 1) ^ 3 / Real.sqrt (β ^ 2 + t ^ 2)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have harg : |t| + 3 ≠ 0 := by positivity
  have hsqrt : Real.sqrt (β ^ 2 + t ^ 2) ≠ 0 := by
    have hpos : 0 < β ^ 2 + t ^ 2 := by positivity
    exact (Real.sqrt_pos.2 hpos).ne'
  have hnum : ContinuousAt (fun u : ℝ => (Real.log (|u| + 3) + 1) ^ 3) t := by
    have habs : ContinuousAt (fun u : ℝ => |u|) t := ContinuousAt.abs continuousAt_id
    have h3 : ContinuousAt (fun u : ℝ => |u| + 3) t := habs.add continuousAt_const
    have hlog : ContinuousAt (fun u : ℝ => Real.log (|u| + 3)) t := by
      exact ContinuousAt.comp (f := (fun u : ℝ => |u| + 3)) (x := t) (g := Real.log)
        (Real.continuousAt_log harg)
        (by fun_prop : ContinuousAt (fun u : ℝ => |u| + 3) t)
    have hp1 : ContinuousAt (fun u : ℝ => Real.log (|u| + 3) + 1) t := hlog.add continuousAt_const
    exact hp1.pow 3
  have hden : ContinuousAt (fun u : ℝ => Real.sqrt (β ^ 2 + u ^ 2)) t := by
    have hin : ContinuousAt (fun u : ℝ => β ^ 2 + u ^ 2) t := by fun_prop
    exact ContinuousAt.comp (f := (fun u : ℝ => β ^ 2 + u ^ 2)) (x := t) (g := Real.sqrt)
      (Real.continuous_sqrt.continuousAt (x := β ^ 2 + t ^ 2)) hin
  exact hnum.div hden hsqrt


/-- `2 ≤ √x` for `x ≥ e^16`. -/
lemma sqrt_ge_two_of_exp_sixteen_le {x : ℝ} (hx : Real.exp 16 ≤ x) : (2 : ℝ) ≤ Real.sqrt x := by
  have hle : Real.sqrt (Real.exp 16) ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
  have hsq : Real.sqrt (Real.exp 16) = Real.exp 8 := by
    have hpow : Real.exp 16 = (Real.exp 8) ^ 2 := by
      have h := Real.exp_nat_mul (8 : ℝ) 2
      norm_num at h ⊢
      exact h
    rw [hpow]
    exact Real.sqrt_sq (Real.exp_pos 8).le
  rw [hsq] at hle
  have he : 2 < Real.exp 8 := by
    have h1 : Real.exp 1 ≤ Real.exp 8 := (Real.exp_le_exp).2 (by norm_num)
    have h2 : 2 < Real.exp 1 := Real.exp_one_gt_two
    linarith
  linarith

/-- Swap the two point orderings of the top edge integrand. -/
lemma topIntegral_swap {x T : ℝ} :
    (∫ (u : ℝ) in leftRe x..perronRe x, ‖psiIntF x ((u : ℂ) + (T : ℂ) * Complex.I)‖) =
      (∫ (u : ℝ) in leftRe x..perronRe x, ‖psiIntF x ((u : ℂ) + Complex.I * (T : ℂ))‖) := by
  apply intervalIntegral.integral_congr
  intro u hu
  change ‖psiIntF x ((u : ℂ) + (T : ℂ) * Complex.I)‖ =
      ‖psiIntF x ((u : ℂ) + Complex.I * (T : ℂ))‖
  have hp : ((u : ℂ) + (T : ℂ) * Complex.I) = ((u : ℂ) + Complex.I * (T : ℂ)) := by ring
  rw [hp]

/-- The truncated-Perron error constant from `chebyshevPsi_truncatedPerron`. -/
noncomputable def perronErrC : ℝ := Classical.choose chebyshevPsi_truncatedPerron

lemma perronErrC_pos : 0 < perronErrC := (Classical.choose_spec chebyshevPsi_truncatedPerron).1

/-- `3 < e^16` (used to verify the truncated-Perron hypotheses). -/
lemma exp16_gt_three : (3 : ℝ) < Real.exp 16 := by
  have hpow : Real.exp 16 = Real.exp 1 ^ 16 := by
    simpa using (Real.exp_nat_mul (1 : ℝ) 16)
  have h1 : (2 : ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_two
  have hpowle : (2 : ℝ) ^ 16 ≤ Real.exp 1 ^ 16 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h1 16
  have h3 : (3 : ℝ) < (2 : ℝ) ^ 16 := by norm_num
  calc
    (3 : ℝ) < (2 : ℝ) ^ 16 := h3
    _ ≤ Real.exp 1 ^ 16 := hpowle
    _ = Real.exp 16 := hpow.symm

end
end Commons.NumberTheory.Zeta
