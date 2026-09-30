import Mathlib
import Submission.Commons.NumberTheory.Zeta.chebyshevPsi_truncatedPerron
import Submission.Commons.NumberTheory.Zeta.lSeries_mangoldt_integral_eq_zeta_logDeriv
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_strip_bound_rh
import Submission.Commons.NumberTheory.Zeta.zeta_ne_zero_of_rh_gt_half
import Submission.Commons.Analysis.Complex.rectIntegral_sub_inv_inside
import Submission.Commons.Analysis.Real.verticalLogWeight_integral_le
import Submission.Commons.Analysis.Real.combinedBound_domination
import Submission.Commons.Analysis.Real.combinedBound_domination_full

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

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

lemma zeta1LogDeriv_differentiableOn (h : RiemannHypothesis) :
    DifferentiableOn ℂ zeta1LogDeriv {s : ℂ | (1 / 2 : ℝ) < s.re} := by
  refine DifferentiableOn.div (c := fun s : ℂ => deriv riemannZeta₁ s) (d := fun s : ℂ => riemannZeta₁ s)
    (s := {s : ℂ | (1 / 2 : ℝ) < s.re}) ?_ ?_ ?_
  · have hd : Differentiable ℂ (fun s : ℂ => deriv riemannZeta₁ s) :=
      (Differentiable.deriv differentiable_riemannZeta₁)
    intro s hs
    exact (hd.differentiableAt (x := s)).differentiableWithinAt
  · intro s hs
    exact (differentiable_riemannZeta₁.differentiableAt (x := s)).differentiableWithinAt
  · intro s hs
    exact Commons.NumberTheory.Zeta.zeta1_ne_zero_of_rh_gt_half h hs

lemma cpow_div_self_differentiableOn_re_gt (x : ℝ) (hx : 0 < x) :
    DifferentiableOn ℂ (fun s : ℂ => (x : ℂ) ^ s / s) {s : ℂ | (1 / 2 : ℝ) < s.re} := by
  intro s hs
  exact ((cpow_div_self_differentiableOn (x := x) hx).differentiableAt (x := s)
    (isOpen_ne.mem_nhds (ne_zero_of_half_lt_re hs))).differentiableWithinAt

lemma hFunc_differentiableOn (h : RiemannHypothesis) (x : ℝ) (hx : 0 < x) :
    DifferentiableOn ℂ (hFunc x) {s : ℂ | (1 / 2 : ℝ) < s.re} := by
  have h1 : DifferentiableOn ℂ (fun s : ℂ => dslope (fun w : ℂ => (x : ℂ) ^ w) 1 s)
      {s : ℂ | (1 / 2 : ℝ) < s.re} := by
    intro s hs
    exact ((cpow_dslope_differentiable hx).differentiableAt (x := s)).differentiableWithinAt
  have h2 : DifferentiableOn ℂ (fun s : ℂ => (x : ℂ) ^ s / s) {s : ℂ | (1 / 2 : ℝ) < s.re} :=
    cpow_div_self_differentiableOn_re_gt x hx
  have h3 : DifferentiableOn ℂ (fun s : ℂ => zeta1LogDeriv s * ((x : ℂ) ^ s / s))
      {s : ℂ | (1 / 2 : ℝ) < s.re} := by
    exact DifferentiableOn.mul (zeta1LogDeriv_differentiableOn h) h2
  change DifferentiableOn ℂ (fun s : ℂ =>
      dslope (fun w : ℂ => (x : ℂ) ^ w) 1 s - (x : ℂ) ^ s / s - zeta1LogDeriv s * ((x : ℂ) ^ s / s))
      {s : ℂ | (1 / 2 : ℝ) < s.re}
  exact (h1.sub h2).sub h3

lemma psiIntF_eq_polar_add_hFunc (h : RiemannHypothesis) {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hs1 : s ≠ 1) (hsRe : (1 / 2 : ℝ) < s.re) :
    psiIntF x s = (x : ℂ) / (s - 1) + hFunc x s := by
  have hs0 : s ≠ 0 := ne_zero_of_half_lt_re hsRe
  have hz1 : riemannZeta₁ s ≠ 0 := Commons.NumberTheory.Zeta.zeta1_ne_zero_of_rh_gt_half h hsRe
  have hid : -(deriv riemannZeta s / riemannZeta s) = (s - 1)⁻¹ - zeta1LogDeriv s := by
    have h := deriv_zeta_div_zeta_eq s hs1 hz1
    rw [h]
    dsimp [zeta1LogDeriv]
    ring
  have hslope : dslope (fun w : ℂ => (x : ℂ) ^ w) 1 s = ((x : ℂ) ^ s - (x : ℂ)) / (s - 1) :=
    dslope_cpow_eq_div hs1
  calc
    psiIntF x s = (-(deriv riemannZeta s / riemannZeta s)) * (x : ℂ) ^ s / s := by
      dsimp [psiIntF]
      ring
    _ = ((s - 1)⁻¹ - zeta1LogDeriv s) * (x : ℂ) ^ s / s := by rw [hid]
    _ = (x : ℂ) ^ s / ((s - 1) * s) - zeta1LogDeriv s * ((x : ℂ) ^ s / s) := by
      field_simp [hs0, sub_ne_zero.mpr hs1] <;> ring
    _ = (x : ℂ) / (s - 1) + hFunc x s := by
      dsimp [hFunc, zeta1LogDeriv]
      rw [hslope]
      field_simp [hs0, sub_ne_zero.mpr hs1] <;> ring

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

lemma rectInt_hFunc_zero (h : RiemannHypothesis) (x : ℝ) (hx : 0 < x) {z w : ℂ}
    (hrect : Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im ⊆ {s : ℂ | (1 / 2 : ℝ) < s.re}) :
    rectInt z w (hFunc x) = 0 := by
  have H : DifferentiableOn ℂ (hFunc x) (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
    exact (hFunc_differentiableOn h x hx).mono hrect
  have hc := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (hFunc x) z w H
  simpa [rectInt] using hc

lemma rectInt_psiIntF_decomp (h : RiemannHypothesis) {x : ℝ} (hx : 0 < x) {z w : ℂ}
    (hre1 : ∀ s ∈ (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im), (1 / 2 : ℝ) < s.re)
    (hn1a : ∀ u ∈ Set.uIcc z.re w.re, (u : ℂ) + z.im * Complex.I ≠ 1)
    (hn1b : ∀ u ∈ Set.uIcc z.re w.re, (u : ℂ) + w.im * Complex.I ≠ 1)
    (hn1c : ∀ v ∈ Set.uIcc z.im w.im, (w.re : ℂ) + v * Complex.I ≠ 1)
    (hn1d : ∀ v ∈ Set.uIcc z.im w.im, (z.re : ℂ) + v * Complex.I ≠ 1) :
    rectInt z w (psiIntF x) =
      rectInt z w (fun s : ℂ => (x : ℂ) / (s - 1) + hFunc x s) := by
  let P : ℂ → ℂ := fun s : ℂ => (x : ℂ) / (s - 1) + hFunc x s
  have h_eq : ∀ s : ℂ, s ∈ (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) → s ≠ 1 →
      psiIntF x s = P s := by
    intro s hs hs1
    dsimp [P]
    exact psiIntF_eq_polar_add_hFunc h hx hs1 (hre1 s hs)
  apply rectInt_congr_boundary
  · intro u hu
    have hmem : (u : ℂ) + z.im * Complex.I ∈ (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
      exact Complex.mem_reProdIm.mpr ⟨by simpa using hu, by simp⟩
    exact h_eq ((u : ℂ) + z.im * Complex.I) hmem (hn1a u hu)
  · intro u hu
    have hmem : (u : ℂ) + w.im * Complex.I ∈ (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
      exact Complex.mem_reProdIm.mpr ⟨by simpa using hu, by simp⟩
    exact h_eq ((u : ℂ) + w.im * Complex.I) hmem (hn1b u hu)
  · intro v hv
    have hmem : (w.re : ℂ) + v * Complex.I ∈ (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
      exact Complex.mem_reProdIm.mpr ⟨by simp, by simpa using hv⟩
    exact h_eq ((w.re : ℂ) + v * Complex.I) hmem (hn1c v hv)
  · intro v hv
    have hmem : (z.re : ℂ) + v * Complex.I ∈ (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
      exact Complex.mem_reProdIm.mpr ⟨by simp, by simpa using hv⟩
    exact h_eq ((z.re : ℂ) + v * Complex.I) hmem (hn1d v hv)

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

lemma hFunc_continuousOn (h : RiemannHypothesis) (x : ℝ) (hx : 0 < x) :
    ContinuousOn (hFunc x) {s : ℂ | (1 / 2 : ℝ) < s.re} := by
  exact (hFunc_differentiableOn h x hx).continuousOn

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

lemma psiIntF_rectInt_eq (h : RiemannHypothesis) {x : ℝ} (hx : Real.exp 8 ≤ x) {T : ℝ}
    (hT : 2 ≤ T) :
    rectInt (zetaRectZ x T) (zetaRectW x T) (psiIntF x) =
      (x : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
  let z : ℂ := zetaRectZ x T
  let w : ℂ := zetaRectW x T
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 8) hx
  have hTpos : 0 < T := by linarith
  have hzre : z.re < w.re := by
    dsimp [z, w]
    exact zetaRect_re_lt x T
  have hzim : z.im < w.im := by
    dsimp [z, w]
    exact zetaRect_im_lt hTpos x
  have hu1 : z.re < (1 : ℂ).re := by
    dsimp [z]
    rw [zetaRectZ_re]
    simpa [leftRe] using (leftRe_lt_one hx)
  have hu2 : (1 : ℂ).re < w.re := by
    dsimp [w]
    rw [zetaRectW_re]
    simpa [perronRe] using (rightRe_gt_one hx)
  have hu3 : z.im < (1 : ℂ).im := by
    dsimp [z]
    rw [zetaRectZ_im]
    simpa using (neg_lt_zero.mpr hTpos)
  have hu4 : (1 : ℂ).im < w.im := by
    dsimp [w]
    rw [zetaRectW_im]
    simpa using hTpos
  have huin : z.re < (1 : ℂ).re ∧ (1 : ℂ).re < w.re ∧ z.im < (1 : ℂ).im ∧ (1 : ℂ).im < w.im := by
    exact ⟨hu1, hu2, hu3, hu4⟩
  -- rectangle inside {1/2 < re}
  have hrect : (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) ⊆ {s : ℂ | (1 / 2 : ℝ) < s.re} := by
    intro s hs
    dsimp [z, w] at hs ⊢
    exact mem_rect_ge_left hx hs
  have hzr : z.re = leftRe x := by dsimp [z]; exact zetaRectZ_re x T
  have hwr : w.re = perronRe x := by dsimp [w]; exact zetaRectW_re x T
  have hzi : z.im = -T := by dsimp [z]; exact zetaRectZ_im x T
  have hwi : w.im = T := by dsimp [w]; exact zetaRectW_im x T
  -- boundary points are not 1
  have hn1a : ∀ u : ℝ, u ∈ Set.uIcc z.re w.re → (u : ℂ) + z.im * Complex.I ≠ 1 := by
    intro u hu
    apply ne_one_of_im_ne_zero
    rw [hzi]
    norm_num [hTpos.ne']
  have hn1b : ∀ u : ℝ, u ∈ Set.uIcc z.re w.re → (u : ℂ) + w.im * Complex.I ≠ 1 := by
    intro u hu
    apply ne_one_of_im_ne_zero
    rw [hwi]
    norm_num [hTpos.ne']
  have hn1c : ∀ v : ℝ, v ∈ Set.uIcc z.im w.im → (w.re : ℂ) + v * Complex.I ≠ 1 := by
    intro v hv
    apply ne_one_of_re_ne_one
    rw [hwr]
    have hre : ((perronRe x : ℂ) + ↑v * Complex.I).re = perronRe x := by simp
    rw [hre]
    exact (ne_of_gt (rightRe_gt_one hx))
  have hn1d : ∀ v : ℝ, v ∈ Set.uIcc z.im w.im → (z.re : ℂ) + v * Complex.I ≠ 1 := by
    intro v hv
    apply ne_one_of_re_ne_one
    rw [hzr]
    have hre : ((leftRe x : ℂ) + ↑v * Complex.I).re = leftRe x := by simp
    rw [hre]
    exact (ne_of_lt (leftRe_lt_one hx))
  -- integrability of the polar summand along the four edges
  let polar : ℂ → ℂ := fun s : ℂ => (x : ℂ) / (s - (1 : ℂ))
  have ipol1 : IntervalIntegrable (fun u : ℝ => polar ((u : ℂ) + z.im * Complex.I)) volume z.re w.re := by
    exact edge_integrable_horiz (f := polar) (U := {s : ℂ | s ≠ 1}) isOpen_compl_singleton
      (continuousOn_polar x) (by intro u hu; dsimp [polar]; exact hn1a u hu)
  have ipol2 : IntervalIntegrable (fun u : ℝ => polar ((u : ℂ) + w.im * Complex.I)) volume z.re w.re := by
    exact edge_integrable_horiz (f := polar) (U := {s : ℂ | s ≠ 1}) isOpen_compl_singleton
      (continuousOn_polar x) (by intro u hu; dsimp [polar]; exact hn1b u hu)
  have ipol3 : IntervalIntegrable (fun v : ℝ => polar ((w.re : ℂ) + v * Complex.I)) volume z.im w.im := by
    exact edge_integrable_vert (f := polar) (U := {s : ℂ | s ≠ 1}) isOpen_compl_singleton
      (continuousOn_polar x) (by intro v hv; dsimp [polar]; exact hn1c v hv)
  have ipol4 : IntervalIntegrable (fun v : ℝ => polar ((z.re : ℂ) + v * Complex.I)) volume z.im w.im := by
    exact edge_integrable_vert (f := polar) (U := {s : ℂ | s ≠ 1}) isOpen_compl_singleton
      (continuousOn_polar x) (by intro v hv; dsimp [polar]; exact hn1d v hv)
  -- integrability of hFunc along the four edges
  have ih1 : IntervalIntegrable (fun u : ℝ => hFunc x ((u : ℂ) + z.im * Complex.I)) volume z.re w.re := by
    exact edge_integrable_horiz (f := hFunc x) (U := {s : ℂ | (1 / 2 : ℝ) < s.re}) (Complex.isOpen_re_gt (1/2))
      (hFunc_continuousOn h x hxpos) (by
        intro u hu
        have hs : (u : ℂ) + z.im * Complex.I ∈ (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
          exact Complex.mem_reProdIm.mpr ⟨by simpa using hu, by simp⟩
        exact hrect hs)
  have ih2 : IntervalIntegrable (fun u : ℝ => hFunc x ((u : ℂ) + w.im * Complex.I)) volume z.re w.re := by
    exact edge_integrable_horiz (f := hFunc x) (U := {s : ℂ | (1 / 2 : ℝ) < s.re}) (Complex.isOpen_re_gt (1/2))
      (hFunc_continuousOn h x hxpos) (by
        intro u hu
        have hs : (u : ℂ) + w.im * Complex.I ∈ (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
          exact Complex.mem_reProdIm.mpr ⟨by simpa using hu, by simp⟩
        exact hrect hs)
  have ih3 : IntervalIntegrable (fun v : ℝ => hFunc x ((w.re : ℂ) + v * Complex.I)) volume z.im w.im := by
    exact edge_integrable_vert (f := hFunc x) (U := {s : ℂ | (1 / 2 : ℝ) < s.re}) (Complex.isOpen_re_gt (1/2))
      (hFunc_continuousOn h x hxpos) (by
        intro v hv
        have hs : (w.re : ℂ) + v * Complex.I ∈ (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
          exact Complex.mem_reProdIm.mpr ⟨by simp, by simpa using hv⟩
        exact hrect hs)
  have ih4 : IntervalIntegrable (fun v : ℝ => hFunc x ((z.re : ℂ) + v * Complex.I)) volume z.im w.im := by
    exact edge_integrable_vert (f := hFunc x) (U := {s : ℂ | (1 / 2 : ℝ) < s.re}) (Complex.isOpen_re_gt (1/2))
      (hFunc_continuousOn h x hxpos) (by
        intro v hv
        have hs : (z.re : ℂ) + v * Complex.I ∈ (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
          exact Complex.mem_reProdIm.mpr ⟨by simp, by simpa using hv⟩
        exact hrect hs)
  -- rectInt of psiIntF decomposes
  have hdecomp := rectInt_psiIntF_decomp h hxpos (z := z) (w := w) (by intro s hs; exact hrect hs)
      (by intro u hu; exact hn1a u hu) (by intro u hu; exact hn1b u hu)
      (by intro v hv; exact hn1c v hv) (by intro v hv; exact hn1d v hv)
  have hsplit : rectInt z w (fun s : ℂ => polar s + hFunc x s) = rectInt z w polar + rectInt z w (hFunc x) := by
    exact rectInt_add (f := polar) (g := hFunc x) ipol1 ih1 ipol2 ih2 ipol3 ih3 ipol4 ih4
  have hzero : rectInt z w (hFunc x) = 0 := by
    exact rectInt_hFunc_zero h x hxpos (z := z) (w := w) hrect
  have hres : rectInt z w polar = (x : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
    dsimp [polar]
    exact rectInt_polar_residue (x : ℂ) hzre hzim huin
  calc
    rectInt (zetaRectZ x T) (zetaRectW x T) (psiIntF x)
        = rectInt z w (psiIntF x) := by rfl
    _ = rectInt z w (fun s : ℂ => (x : ℂ) / (s - 1) + hFunc x s) := by
          simpa [polar] using hdecomp
    _ = rectInt z w (fun s : ℂ => polar s + hFunc x s) := by
          rfl
    _ = rectInt z w polar + rectInt z w (hFunc x) := hsplit
    _ = (x : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by rw [hzero, hres, add_zero]



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

lemma perronZeta_sub_id (h : RiemannHypothesis) {x : ℝ} (hx : Real.exp 8 ≤ x) {T : ℝ}
    (hT : 2 ≤ T) :
    perronZeta x T - (x : ℂ) =
      (((1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) * (topInt x T - botInt x T)) +
        (((1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ)))) * leftInt x T := by
  let z : ℂ := zetaRectZ x T
  let w : ℂ := zetaRectW x T
  have hz0 : rectInt z w (psiIntF x) = (x : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
    dsimp [z, w]
    exact psiIntF_rectInt_eq h hx hT
  have hzr : z.re = leftRe x := by dsimp [z]; exact zetaRectZ_re x T
  have hwr : w.re = perronRe x := by dsimp [w]; exact zetaRectW_re x T
  have hzi : z.im = -T := by dsimp [z]; exact zetaRectZ_im x T
  have hwi : w.im = T := by dsimp [w]; exact zetaRectW_im x T
  -- re-express the rectangle identity in terms of `botInt`, `topInt`, `perronRight`, `leftInt`
  have hz1 : botInt x T - topInt x T + Complex.I * perronRight x T - Complex.I * leftInt x T =
      (x : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
    have hb : (∫ (u : ℝ) in z.re..w.re, psiIntF x ((u : ℂ) + (z.im : ℂ) * Complex.I)) = botInt x T := by
      dsimp [botInt]
      rw [hzr, hzi]
      -- interval z.re..w.re = leftRe..perronRe already; and point u + (-T)*I = u - T*I
      congr 1
      funext u
      congr 1
      -- u + (-T : ℂ) * I  vs  u - (T:ℂ) * I
      have h : (u : ℂ) + ((-T : ℝ) : ℂ) * Complex.I = (u : ℂ) - (T : ℂ) * Complex.I := by
        norm_num
        ring
      simpa using h
    have ht : (∫ (u : ℝ) in z.re..w.re, psiIntF x ((u : ℂ) + (w.im : ℂ) * Complex.I)) = topInt x T := by
      simpa [topInt, hzr, hwr, hwi]
    have hr : (∫ (t : ℝ) in z.im..w.im, psiIntF x ((w.re : ℂ) + (t : ℂ) * Complex.I)) = perronRight x T := by
      simpa [perronRight, hwr, hzi, hwi]
    have hl : (∫ (t : ℝ) in z.im..w.im, psiIntF x ((z.re : ℂ) + (t : ℂ) * Complex.I)) = leftInt x T := by
      simpa [leftInt, hzr, hzi, hwi]
    -- unfold rectInt in hz0 and rewrite with the four equalities
    have hz0' : (∫ (u : ℝ) in z.re..w.re, psiIntF x ((u : ℂ) + (z.im : ℂ) * Complex.I)) -
          (∫ (u : ℝ) in z.re..w.re, psiIntF x ((u : ℂ) + (w.im : ℂ) * Complex.I)) +
          Complex.I * (∫ (t : ℝ) in z.im..w.im, psiIntF x ((w.re : ℂ) + (t : ℂ) * Complex.I)) -
          Complex.I * (∫ (t : ℝ) in z.im..w.im, psiIntF x ((z.re : ℂ) + (t : ℂ) * Complex.I)) =
          (x : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
        simpa [rectInt, smul_eq_mul] using hz0
    simpa [hb, ht, hr, hl] using hz0'
  let c : ℂ := (1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)
  let r : ℂ := (1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ))
  have hP : perronZeta x T = r * perronRight x T := by
    rfl
  have hcI : c * Complex.I = r := by
    dsimp [c, r]
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp [hI, hπ] <;> ring
  have hc2 : c * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) = 1 := by
    dsimp [c]
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp [hI, hπ]
  have hIR : Complex.I * perronRight x T =
      (x : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) + (topInt x T - botInt x T) +
        Complex.I * leftInt x T := by
    linear_combination hz1
  have h1 : c * ((x : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) = (x : ℂ) := by
    calc c * (x * ((2:ℂ)*(Real.pi:ℂ)*Complex.I)) = x * (c * ((2:ℂ)*(Real.pi:ℂ)*Complex.I)) := by ring
         _ = x := by rw [hc2, mul_one]
  have h2 : c * (Complex.I * leftInt x T) = r * leftInt x T := by
    calc c * (Complex.I * leftInt x T) = (c * Complex.I) * leftInt x T := by ring
         _ = r * leftInt x T := by rw [hcI]
  have h1n : c * (x : ℂ) * (Real.pi : ℂ) * Complex.I * 2 = (x : ℂ) := by
    calc c * (x:ℂ) * (Real.pi:ℂ) * Complex.I * 2 = c * ((x:ℂ) * ((2:ℂ)*(Real.pi:ℂ)*Complex.I)) := by ring
         _ = (x:ℂ) := h1
  have h2n : c * Complex.I * leftInt x T = r * leftInt x T := by
    calc c * Complex.I * leftInt x T = c * (Complex.I * leftInt x T) := by ring
         _ = r * leftInt x T := h2
  have hmain : c * (Complex.I * perronRight x T) = (x : ℂ) + c * (topInt x T - botInt x T) + r * leftInt x T := by
    rw [hIR]
    ring_nf
    rw [h1n, h2n]
    ring
  calc
    perronZeta x T - (x : ℂ) = r * perronRight x T - (x : ℂ) := by rw [hP]
    _ = c * (Complex.I * perronRight x T) - (x : ℂ) := by
      have hsub : r * perronRight x T = c * (Complex.I * perronRight x T) := by
        calc r * perronRight x T = (c * Complex.I) * perronRight x T := by rw [hcI]
             _ = c * (Complex.I * perronRight x T) := by ring
      rw [hsub]
    _ = ((x : ℂ) + c * (topInt x T - botInt x T) + r * leftInt x T) - (x : ℂ) := by rw [hmain]
    _ = c * (topInt x T - botInt x T) + r * leftInt x T := by
      rw [show c = (1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) by rfl]
      rw [show r = (1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ)) by rfl]
      ring


/-- Bound `‖perronZeta − x‖` by the three edge integrals (up to `1/2π`). -/
lemma perronZeta_sub_id_norm_le (h : RiemannHypothesis) {x : ℝ} (hx : Real.exp 8 ≤ x) {T : ℝ}
    (hT : 2 ≤ T) :
    ‖perronZeta x T - (x : ℂ)‖ ≤
      (1 / (2 * Real.pi)) *
        ((∫ (u : ℝ) in leftRe x..perronRe x, ‖psiIntF x ((u : ℂ) + (T : ℂ) * Complex.I)‖) +
         (∫ (u : ℝ) in leftRe x..perronRe x, ‖psiIntF x ((u : ℂ) - (T : ℂ) * Complex.I)‖) +
         (∫ (t : ℝ) in -T..T, ‖psiIntF x ((leftRe x : ℂ) + (t : ℂ) * Complex.I)‖)) := by
  have hleA : leftRe x ≤ perronRe x := le_of_lt (leftRe_lt_perronRe x)
  have hleT : -T ≤ T := by linarith
  have htopb : ‖topInt x T‖ ≤ (∫ (u : ℝ) in leftRe x..perronRe x, ‖psiIntF x ((u : ℂ) + (T : ℂ) * Complex.I)‖) := by
    dsimp [topInt]
    exact intervalIntegral.norm_integral_le_integral_norm hleA
  have hbotb : ‖botInt x T‖ ≤ (∫ (u : ℝ) in leftRe x..perronRe x, ‖psiIntF x ((u : ℂ) - (T : ℂ) * Complex.I)‖) := by
    dsimp [botInt]
    exact intervalIntegral.norm_integral_le_integral_norm hleA
  have hleftb : ‖leftInt x T‖ ≤ (∫ (t : ℝ) in -T..T, ‖psiIntF x ((leftRe x : ℂ) + (t : ℂ) * Complex.I)‖) := by
    dsimp [leftInt]
    exact intervalIntegral.norm_integral_le_integral_norm hleT
  have hc : ‖((1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ) * Complex.I))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div]
    simp [Real.pi_pos.le]
  have hr : ‖((1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ)))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div]
    simp [Real.pi_pos.le]
  have hsub := perronZeta_sub_id h hx hT
  rw [hsub]
  -- ‖ c·(top−bot) + r·left ‖ ≤ ‖c‖‖top−bot‖ + ‖r‖‖left‖ ≤ ...
  have h1 : ‖((1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) * (topInt x T - botInt x T)‖ ≤
      (1 / (2 * Real.pi)) * (‖topInt x T‖ + ‖botInt x T‖) := by
    have hnorm := norm_mul_le ((1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) (topInt x T - botInt x T)
    have hsubn : ‖topInt x T - botInt x T‖ ≤ ‖topInt x T‖ + ‖botInt x T‖ := norm_sub_le _ _
    rw [hc] at hnorm
    have hcoef : 0 ≤ 1 / (2 * Real.pi) := by positivity
    calc
      ‖((1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) * (topInt x T - botInt x T)‖
          ≤ (1 / (2 * Real.pi)) * ‖topInt x T - botInt x T‖ := hnorm
      _ ≤ (1 / (2 * Real.pi)) * (‖topInt x T‖ + ‖botInt x T‖) :=
          mul_le_mul_of_nonneg_left hsubn hcoef
  have h2 : ‖((1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ))) * leftInt x T‖ ≤
      (1 / (2 * Real.pi)) * ‖leftInt x T‖ := by
    have hnorm := norm_mul_le ((1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ))) (leftInt x T)
    rw [hr] at hnorm
    simpa using hnorm
  have htot : ‖((1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) * (topInt x T - botInt x T) +
      ((1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ))) * leftInt x T‖ ≤
      (1 / (2 * Real.pi)) * (‖topInt x T‖ + ‖botInt x T‖ + ‖leftInt x T‖) := by
    have hadd := norm_add_le (((1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) * (topInt x T - botInt x T))
      (((1 : ℂ) / ((2 : ℂ) * (Real.pi : ℂ))) * leftInt x T)
    linarith
  have hcoef : 0 ≤ (1 / (2 * Real.pi)) := by positivity
  have hfin1 : (1 / (2 * Real.pi)) * (‖topInt x T‖ + ‖botInt x T‖ + ‖leftInt x T‖) ≤
      (1 / (2 * Real.pi)) *
        ((∫ (u : ℝ) in leftRe x..perronRe x, ‖psiIntF x ((u : ℂ) + (T : ℂ) * Complex.I)‖) +
         (∫ (u : ℝ) in leftRe x..perronRe x, ‖psiIntF x ((u : ℂ) - (T : ℂ) * Complex.I)‖) +
         (∫ (t : ℝ) in -T..T, ‖psiIntF x ((leftRe x : ℂ) + (t : ℂ) * Complex.I)‖)) := by
    have hsum : ‖topInt x T‖ + ‖botInt x T‖ + ‖leftInt x T‖ ≤
        (∫ (u : ℝ) in leftRe x..perronRe x, ‖psiIntF x ((u : ℂ) + (T : ℂ) * Complex.I)‖) +
        (∫ (u : ℝ) in leftRe x..perronRe x, ‖psiIntF x ((u : ℂ) - (T : ℂ) * Complex.I)‖) +
        (∫ (t : ℝ) in -T..T, ‖psiIntF x ((leftRe x : ℂ) + (t : ℂ) * Complex.I)‖) := by
      nlinarith
    exact mul_le_mul_of_nonneg_left hsum hcoef
  exact le_trans htot hfin1

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



/-- Unwrapped strip bound for the log-derivative of zeta under RH. -/
lemma zeta_logDeriv_strip_apply (h : RiemannHypothesis) {δ σ t : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hσlo : (1 / 2 + δ) ≤ σ) (hσhi : σ ≤ 2)
    (hdist : 1 / 4 ≤ ‖(((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) - 1‖) :
    ‖(deriv riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)) /
        riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)‖ ≤
      (Classical.choose zeta_logDeriv_strip_bound_rh) *
        (1 + 1 / δ) ^ 3 * (Real.log (|t| + 3) + 1) ^ 3 := by
  have h := (Classical.choose_spec zeta_logDeriv_strip_bound_rh).2 h δ σ t hδ0 hδ1 hσlo hσhi hdist
  simpa using h


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


lemma psiIntF_continuousAt (h : RiemannHypothesis) {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hsRe : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) : ContinuousAt (psiIntF x) s := by
  have hderAn : AnalyticOnNhd ℂ (deriv riemannZeta) ({1}ᶜ : Set ℂ) :=
    AnalyticOnNhd.deriv analyticOn_riemannZeta
  have hc1 : ContinuousAt (fun w : ℂ => -(deriv riemannZeta w) / riemannZeta w) s := by
    have hcd : ContinuousAt (fun w : ℂ => deriv riemannZeta w) s := by
      exact hderAn.continuousOn.continuousAt (isOpen_compl_singleton.mem_nhds hs1)
    have hcz : ContinuousAt riemannZeta s := by
      exact analyticOn_riemannZeta.continuousOn.continuousAt (isOpen_compl_singleton.mem_nhds hs1)
    have hz0 : riemannZeta s ≠ 0 := zeta_ne_zero_of_rh_gt_half h hsRe
    have hneg : ContinuousAt (fun w : ℂ => -(deriv riemannZeta w)) s := hcd.neg
    exact hneg.div hcz hz0
  have hcp : ContinuousAt (fun w : ℂ => (x : ℂ) ^ w) s := by
    have heq : (fun w : ℂ => (x : ℂ) ^ w) = fun w : ℂ => Complex.exp ((Real.log x : ℂ) * w) := by
      funext w
      exact cpow_eq_exp_log_mul hx w
    rw [heq]
    fun_prop
  have hc_id : ContinuousAt (fun w : ℂ => w) s := continuousAt_id
  have hs0 : s ≠ 0 := ne_zero_of_half_lt_re hsRe
  have hm : ContinuousAt (fun w : ℂ => (-(deriv riemannZeta w) / riemannZeta w) * (x : ℂ) ^ w) s :=
    hc1.mul hcp
  have htotal : ContinuousAt (fun w : ℂ => ((-(deriv riemannZeta w) / riemannZeta w) * (x : ℂ) ^ w) / w) s :=
    hm.div hc_id hs0
  change ContinuousAt (fun w : ℂ => (-(deriv riemannZeta w) / riemannZeta w) * (x : ℂ) ^ w / w) s
  exact htotal

/-- `u ↦ ‖psiIntF x (u + i·r)‖` is interval integrable on `uIcc a b` provided the points avoid 1
and lie in `Re > 1/2`. -/
lemma norm_horiz_integrable (h : RiemannHypothesis) {x : ℝ} (hx : 0 < x) {r : ℝ} {a b : ℝ}
    (hIm : r ≠ 0) (hRe : ∀ u : ℝ, u ∈ Set.uIcc a b → (1 / 2 : ℝ) < u) :
    IntervalIntegrable (fun u : ℝ => ‖psiIntF x ((u : ℂ) + Complex.I * (r : ℂ))‖) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.norm
  intro u0 hu0
  let φ : ℝ → ℂ := fun u : ℝ => (u : ℂ) + Complex.I * (r : ℂ)
  have hcφ : ContinuousAt φ u0 := by dsimp [φ]; fun_prop
  have hp : ContinuousAt (psiIntF x) (φ u0) := by
    dsimp [φ]
    exact psiIntF_continuousAt h hx (s := (u0 : ℂ) + Complex.I * (r : ℂ))
      (hsRe := by simpa using (hRe u0 hu0)) (hs1 := by
        apply ne_one_of_im_ne_zero
        simp [hIm])
  have hg : ContinuousAt (fun u : ℝ => psiIntF x ((u : ℂ) + Complex.I * (r : ℂ))) u0 := by
    exact ContinuousAt.comp (f := φ) (x := u0) (g := psiIntF x) hp hcφ
  exact hg.continuousWithinAt

/-- Bound of the top horizontal integral `∫_{β}^{σ₁} ‖f(u+iT)‖ du`. -/
lemma topIntegral_le (h : RiemannHypothesis) {C : ℝ} (hC0 : 0 < C)
    (hC : ∀ (δ σ t : ℝ), 0 < δ → δ ≤ 1 → (1 / 2 + δ) ≤ σ → σ ≤ 2 →
      (1 / 4 ≤ ‖(((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) - 1‖) →
      ‖(deriv riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)) /
          riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)‖ ≤
        C * (1 + 1 / δ) ^ 3 * (Real.log (|t| + 3) + 1) ^ 3)
    {x : ℝ} (hx : Real.exp 8 ≤ x) {T : ℝ} (hT : 2 ≤ T) {r : ℝ} (hr : |r| = T) :
    (∫ (u : ℝ) in leftRe x..perronRe x, ‖psiIntF x ((u : ℂ) + Complex.I * (r : ℂ))‖) ≤
      C * (1 + Real.log x) ^ 3 * (Real.log (T + 3) + 1) ^ 3 *
        (x : ℝ) ^ perronRe x * (perronRe x - leftRe x) / T := by
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 8) hx
  have hx1 : 1 < x := lt_of_lt_of_le exp8_gt_one hx
  have hTpos : 0 < T := by linarith
  have hab : leftRe x ≤ perronRe x := le_of_lt (leftRe_lt_perronRe x)
  have hlog1 : 1 ≤ Real.log x := by linarith [logx_ge_eight_of_exp_eight_le hx]
  have hlogT : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T + 3)
  let K : ℝ := C * (1 + Real.log x) ^ 3 * (Real.log (T + 3) + 1) ^ 3 * (x : ℝ) ^ perronRe x / T
  have hK0 : 0 ≤ K := by
    dsimp [K]
    have h1 : 0 ≤ (1 + Real.log x) ^ 3 := pow_nonneg (by linarith) 3
    have h2 : 0 ≤ (Real.log (T + 3) + 1) ^ 3 := pow_nonneg (by linarith) 3
    have h3 : 0 ≤ (x : ℝ) ^ perronRe x := Real.rpow_nonneg (le_of_lt hxpos) (perronRe x)
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hC0) h1) h2) h3) (le_of_lt hTpos)
  have hf : IntervalIntegrable (fun u : ℝ => ‖psiIntF x ((u : ℂ) + Complex.I * (r : ℂ))‖) volume (leftRe x) (perronRe x) := by
    have hr0 : r ≠ 0 := abs_ne_zero.mp (by rw [hr]; exact (ne_of_gt hTpos))
    exact norm_horiz_integrable h hxpos (r := r) hr0 (fun u hu => by
      have hu' : u ∈ Set.Icc (leftRe x) (perronRe x) := by
        rw [Set.uIcc_of_le hab] at hu
        exact hu
      have hge : leftRe x ≤ u := hu'.1
      have hgt : (1 / 2 : ℝ) < leftRe x := leftRe_gt_half hx
      linarith)
  have hpt : ∀ u ∈ Set.Icc (leftRe x) (perronRe x),
      ‖psiIntF x ((u : ℂ) + Complex.I * (r : ℂ))‖ ≤ K := by
    intro u hu
    have hb' := psiIntF_horiz_le h hC0 hC hx hT hu.1 hu.2 hr
    have hrpow : (x : ℝ) ^ u ≤ (x : ℝ) ^ perronRe x := (Real.rpow_le_rpow_left_iff hx1).2 hu.2
    have hc0 : 0 ≤ C * (1 + Real.log x) ^ 3 * (Real.log (T + 3) + 1) ^ 3 / T := by
      have h1 : 0 ≤ (1 + Real.log x) ^ 3 := pow_nonneg (by linarith) 3
      have h2 : 0 ≤ (Real.log (T + 3) + 1) ^ 3 := pow_nonneg (by linarith) 3
      exact div_nonneg (mul_nonneg (mul_nonneg (le_of_lt hC0) h1) h2) (le_of_lt hTpos)
    have hstep1 : C * (1 + Real.log x) ^ 3 * (Real.log (T + 3) + 1) ^ 3 * (x : ℝ) ^ u / T ≤
        C * (1 + Real.log x) ^ 3 * (Real.log (T + 3) + 1) ^ 3 * (x : ℝ) ^ perronRe x / T := by
      have hprod : C * (1 + Real.log x) ^ 3 * (Real.log (T + 3) + 1) ^ 3 / T * (x : ℝ) ^ u ≤
          C * (1 + Real.log x) ^ 3 * (Real.log (T + 3) + 1) ^ 3 / T * (x : ℝ) ^ perronRe x := by
        exact mul_le_mul_of_nonneg_left hrpow hc0
      have hlu : C * (1 + Real.log x) ^ 3 * (Real.log (T + 3) + 1) ^ 3 * (x : ℝ) ^ u / T =
          C * (1 + Real.log x) ^ 3 * (Real.log (T + 3) + 1) ^ 3 / T * (x : ℝ) ^ u := by ring
      have hlp : C * (1 + Real.log x) ^ 3 * (Real.log (T + 3) + 1) ^ 3 * (x : ℝ) ^ perronRe x / T =
          C * (1 + Real.log x) ^ 3 * (Real.log (T + 3) + 1) ^ 3 / T * (x : ℝ) ^ perronRe x := by ring
      rw [hlu, hlp]
      exact hprod
    dsimp [K]
    exact le_trans hb' hstep1
  have hg : IntervalIntegrable (fun _ : ℝ => K) volume (leftRe x) (perronRe x) := by
    simpa using (Continuous.intervalIntegrable (by fun_prop : Continuous fun _ : ℝ => K) (leftRe x) (perronRe x))
  have hmono := intervalIntegral.integral_mono_on hab hf hg hpt
  have hconst : (∫ (u : ℝ) in leftRe x..perronRe x, K) = K * (perronRe x - leftRe x) := by
    rw [intervalIntegral.integral_const]
    simp [mul_comm]
  have hKeq : K * (perronRe x - leftRe x) =
      C * (1 + Real.log x) ^ 3 * (Real.log (T + 3) + 1) ^ 3 * (x : ℝ) ^ perronRe x *
        (perronRe x - leftRe x) / T := by
    dsimp [K]
    ring
  calc
    (∫ (u : ℝ) in leftRe x..perronRe x, ‖psiIntF x ((u : ℂ) + Complex.I * (r : ℂ))‖) ≤ (∫ (u : ℝ) in leftRe x..perronRe x, K) := hmono
    _ = K * (perronRe x - leftRe x) := hconst
    _ = C * (1 + Real.log x) ^ 3 * (Real.log (T + 3) + 1) ^ 3 * (x : ℝ) ^ perronRe x *
        (perronRe x - leftRe x) / T := hKeq


/-- Bound of the bottom horizontal integral `∫_{β}^{σ₁} ‖f(u−iT)‖ du` (same estimate as the
top edge: the two lines only differ by the sign of `Im`, and `|r| = T` makes the bounds agree). -/
lemma bottomIntegral_le (h : RiemannHypothesis) {C : ℝ} (hC0 : 0 < C)
    (hC : ∀ (δ σ t : ℝ), 0 < δ → δ ≤ 1 → (1 / 2 + δ) ≤ σ → σ ≤ 2 →
      (1 / 4 ≤ ‖(((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) - 1‖) →
      ‖(deriv riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)) /
          riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)‖ ≤
        C * (1 + 1 / δ) ^ 3 * (Real.log (|t| + 3) + 1) ^ 3)
    {x : ℝ} (hx : Real.exp 8 ≤ x) {T : ℝ} (hT : 2 ≤ T) :
    (∫ (u : ℝ) in leftRe x..perronRe x, ‖psiIntF x ((u : ℂ) - (T : ℂ) * Complex.I)‖) ≤
      C * (1 + Real.log x) ^ 3 * (Real.log (T + 3) + 1) ^ 3 *
        (x : ℝ) ^ perronRe x * (perronRe x - leftRe x) / T := by
  have hTpos : 0 < T := by linarith
  have hsw : (∫ (u : ℝ) in leftRe x..perronRe x, ‖psiIntF x ((u : ℂ) - (T : ℂ) * Complex.I)‖) =
      (∫ (u : ℝ) in leftRe x..perronRe x, ‖psiIntF x ((u : ℂ) + Complex.I * ((-T : ℝ) : ℂ))‖) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hc : ((-T : ℝ) : ℂ) = -((T : ℝ) : ℂ) := by norm_num
    have hp : ((u : ℂ) - (T : ℂ) * Complex.I) = ((u : ℂ) + Complex.I * ((-T : ℝ) : ℂ)) := by
      rw [hc]
      ring
    change ‖psiIntF x ((u : ℂ) - (T : ℂ) * Complex.I)‖ =
        ‖psiIntF x ((u : ℂ) + Complex.I * ((-T : ℝ) : ℂ))‖
    rw [hp]
  have hb := topIntegral_le h hC0 hC hx hT (r := -T) (by rw [abs_neg, abs_of_nonneg (le_of_lt hTpos)])
  rw [hsw]
  exact hb


/-- `t ↦ ‖psiIntF x (a + i·t)‖` is interval integrable on `uIcc c d` provided `1/2 < a ≠ 1`. -/
lemma norm_vert_integrable (h : RiemannHypothesis) {x : ℝ} (hx : 0 < x) {a : ℝ} {c d : ℝ}
    (haRe : (1 / 2 : ℝ) < a) (ha1 : a ≠ 1) :
    IntervalIntegrable (fun t : ℝ => ‖psiIntF x ((a : ℂ) + Complex.I * (t : ℂ))‖) volume c d := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.norm
  intro t0 ht0
  let φ : ℝ → ℂ := fun t : ℝ => (a : ℂ) + Complex.I * (t : ℂ)
  have hcφ : ContinuousAt φ t0 := by dsimp [φ]; fun_prop
  have hp : ContinuousAt (psiIntF x) (φ t0) := by
    dsimp [φ]
    exact psiIntF_continuousAt h hx (s := (a : ℂ) + Complex.I * (t0 : ℂ))
      (hsRe := by simpa using haRe) (hs1 := by
        apply ne_one_of_re_ne_one
        simpa using ha1)
  have hg : ContinuousAt (fun t : ℝ => psiIntF x ((a : ℂ) + Complex.I * (t : ℂ))) t0 := by
    exact ContinuousAt.comp (f := φ) (x := t0) (g := psiIntF x) hp hcφ
  exact hg.continuousWithinAt

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


/-- Bound of the left (vertical) edge integral `∫_{−T}^{T} ‖f(β+it)‖ dt`. -/
lemma leftIntegral_le (h : RiemannHypothesis) {C : ℝ} (hC0 : 0 < C)
    (hC : ∀ (δ σ t : ℝ), 0 < δ → δ ≤ 1 → (1 / 2 + δ) ≤ σ → σ ≤ 2 →
      (1 / 4 ≤ ‖(((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) - 1‖) →
      ‖(deriv riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)) /
          riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)‖ ≤
        C * (1 + 1 / δ) ^ 3 * (Real.log (|t| + 3) + 1) ^ 3)
    {x : ℝ} (hx : Real.exp 8 ≤ x) {T : ℝ} (hT : 2 ≤ T) :
    (∫ (t : ℝ) in -T..T, ‖psiIntF x ((leftRe x : ℂ) + (t : ℂ) * Complex.I)‖) ≤
      8 * C * (1 + Real.log x) ^ 3 * (x : ℝ) ^ leftRe x *
        (Real.log (T + 3) + 1) ^ 3 * (Real.log (T / leftRe x) + 1) := by
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 8) hx
  have hTpos : 0 < T := by linarith
  let β : ℝ := leftRe x
  have hb0 : 0 < β := by
    dsimp [β, leftRe]
    linarith [leftRe_gt_half hx]
  have hbT : β ≤ T := by
    dsimp [β, leftRe]
    have h1 : 1 / 2 + 1 / Real.log x < 1 := leftRe_lt_one hx
    nlinarith
  have hleT : -T ≤ T := by linarith
  let c : ℝ := C * (1 + Real.log x) ^ 3 * (x : ℝ) ^ β
  have hc0 : 0 ≤ c := by
    dsimp [c]
    have h1 : 0 ≤ (1 + Real.log x) ^ 3 := pow_nonneg (by linarith [logx_ge_eight_of_exp_eight_le hx]) 3
    exact mul_nonneg (mul_nonneg (le_of_lt hC0) h1) (Real.rpow_nonneg (le_of_lt hxpos) β)
  -- swap the point order (t)*I  vs  I*t
  have hsw : (∫ (t : ℝ) in -T..T, ‖psiIntF x ((leftRe x : ℂ) + (t : ℂ) * Complex.I)‖) =
      (∫ (t : ℝ) in -T..T, ‖psiIntF x ((leftRe x : ℂ) + Complex.I * (t : ℂ))‖) := by
    apply intervalIntegral.integral_congr
    intro t ht
    change ‖psiIntF x ((leftRe x : ℂ) + (t : ℂ) * Complex.I)‖ =
        ‖psiIntF x ((leftRe x : ℂ) + Complex.I * (t : ℂ))‖
    have hp : ((leftRe x : ℂ) + (t : ℂ) * Complex.I) = ((leftRe x : ℂ) + Complex.I * (t : ℂ)) := by ring
    rw [hp]
  -- integrability of the left-hand-side integrand (I·t form)
  have hf : IntervalIntegrable (fun t : ℝ => ‖psiIntF x ((leftRe x : ℂ) + Complex.I * (t : ℂ))‖) volume (-T) T := by
    exact norm_vert_integrable h hxpos (a := leftRe x) (c := -T) (d := T) (leftRe_gt_half hx)
      (ne_of_lt (leftRe_lt_one hx))
  let g0 : ℝ → ℝ := fun t : ℝ => (Real.log (|t| + 3) + 1) ^ 3 / Real.sqrt (β ^ 2 + t ^ 2)
  have hg0i : IntervalIntegrable g0 volume (-T) T := by
    dsimp [g0]
    exact (Continuous.intervalIntegrable (logWeightBound_continuous hb0) (-T) T)
  have hcgi : IntervalIntegrable (fun t : ℝ => c * g0 t) volume (-T) T := by
    exact hg0i.const_mul c
  -- pointwise bound ‖psiIntF x (β + I t)‖ ≤ c · g0 t
  have hpt : ∀ t ∈ Set.Icc (-T) T, ‖psiIntF x ((leftRe x : ℂ) + Complex.I * (t : ℂ))‖ ≤ c * g0 t := by
    intro t ht
    let s : ℂ := (leftRe x : ℂ) + Complex.I * (t : ℂ)
    have hb' := psiIntF_left_le h hC0 hC hx (t := t)
    have hs_eq : ‖s‖ = Real.sqrt (β ^ 2 + t ^ 2) := by
      have hs' := Complex.norm_eq_sqrt_sq_add_sq s
      rw [hs']
      have hre : s.re = leftRe x := by dsimp [s]; simp
      have him : s.im = t := by dsimp [s]; simp
      dsimp [β]
      simp [hre, him]
    have hb'' : ‖psiIntF x s‖ ≤ c * g0 t := by
      dsimp [c, g0]
      calc
        ‖psiIntF x s‖ ≤ C * (1 + Real.log x) ^ 3 * (Real.log (|t| + 3) + 1) ^ 3 *
            (x : ℝ) ^ leftRe x / ‖s‖ := by
              simpa [s] using hb'
        _ = C * (1 + Real.log x) ^ 3 * (Real.log (|t| + 3) + 1) ^ 3 *
            (x : ℝ) ^ leftRe x / Real.sqrt (β ^ 2 + t ^ 2) := by rw [hs_eq]
        _ = C * (1 + Real.log x) ^ 3 * (x : ℝ) ^ β *
            ((Real.log (|t| + 3) + 1) ^ 3 / Real.sqrt (β ^ 2 + t ^ 2)) := by
              dsimp [β]
              ring
    simpa [s] using hb''
  -- assemble: the swapped integral is bounded by c·∫g0, and ∫g0 is bounded by the child lemma
  have hmono := intervalIntegral.integral_mono_on hleT hf hcgi hpt
  have hconstmul : (∫ (t : ℝ) in -T..T, c * g0 t) = c * (∫ (t : ℝ) in -T..T, g0 t) := by
    rw [intervalIntegral.integral_const_mul]
  have hvert := Commons.Analysis.Real.verticalLogWeight_integral_le hb0 hbT hT
  have hg0b : (∫ (t : ℝ) in -T..T, g0 t) ≤
      8 * (Real.log (T + 3) + 1) ^ 3 * (Real.log (T / β) + 1) := by
    simpa [g0] using hvert
  have hmul2 : c * (∫ (t : ℝ) in -T..T, g0 t) ≤
      c * (8 * (Real.log (T + 3) + 1) ^ 3 * (Real.log (T / β) + 1)) := by
    exact mul_le_mul_of_nonneg_left hg0b hc0
  calc
    (∫ (t : ℝ) in -T..T, ‖psiIntF x ((leftRe x : ℂ) + (t : ℂ) * Complex.I)‖)
        = (∫ (t : ℝ) in -T..T, ‖psiIntF x ((leftRe x : ℂ) + Complex.I * (t : ℂ))‖) := hsw
    _ ≤ (∫ (t : ℝ) in -T..T, c * g0 t) := hmono
    _ = c * (∫ (t : ℝ) in -T..T, g0 t) := hconstmul
    _ ≤ c * (8 * (Real.log (T + 3) + 1) ^ 3 * (Real.log (T / β) + 1)) := hmul2
    _ = 8 * C * (1 + Real.log x) ^ 3 * (x : ℝ) ^ leftRe x *
        (Real.log (T + 3) + 1) ^ 3 * (Real.log (T / leftRe x) + 1) := by
          dsimp [c, β]
          ring


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

/-- Assembled bound for the truncated Perron integral at `T = √x` under the strip bound. -/
lemma perronZeta_sqrt_bound (h : RiemannHypothesis) {C : ℝ} (hC0 : 0 < C)
    (hC : ∀ (δ σ t : ℝ), 0 < δ → δ ≤ 1 → (1 / 2 + δ) ≤ σ → σ ≤ 2 →
      (1 / 4 ≤ ‖(((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) - 1‖) →
      ‖(deriv riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)) /
          riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)‖ ≤
        C * (1 + 1 / δ) ^ 3 * (Real.log (|t| + 3) + 1) ^ 3)
    {x : ℝ} (hx : Real.exp 16 ≤ x) :
    ‖perronZeta x (Real.sqrt x) - (x : ℂ)‖ ≤
      (1 / (2 * Real.pi)) *
        (2 * (C * (1 + Real.log x) ^ 3 * (Real.log (Real.sqrt x + 3) + 1) ^ 3 *
            (x : ℝ) ^ perronRe x * (perronRe x - leftRe x) / Real.sqrt x) +
         8 * C * (1 + Real.log x) ^ 3 * (x : ℝ) ^ leftRe x *
           (Real.log (Real.sqrt x + 3) + 1) ^ 3 * (Real.log (Real.sqrt x / leftRe x) + 1)) := by
  have hx8 : Real.exp 8 ≤ x := by
    have hm : Real.exp 8 ≤ Real.exp 16 := (Real.exp_le_exp).2 (by norm_num)
    exact le_trans hm hx
  have hT2 : 2 ≤ Real.sqrt x := sqrt_ge_two_of_exp_sixteen_le hx
  have hTpos : 0 < Real.sqrt x := by linarith
  let T : ℝ := Real.sqrt x
  have hT2' : 2 ≤ T := by simpa [T] using hT2
  have hn := perronZeta_sub_id_norm_le h hx8 (T := T) hT2'
  -- bound the three edge integrals
  have htop0 := topIntegral_le h hC0 hC hx8 (T := T) hT2' (r := T)
    (by dsimp [T]; exact abs_of_nonneg (le_of_lt hTpos))
  have hswTop : (∫ (u : ℝ) in leftRe x..perronRe x, ‖psiIntF x ((u : ℂ) + (T : ℂ) * Complex.I)‖) =
      (∫ (u : ℝ) in leftRe x..perronRe x, ‖psiIntF x ((u : ℂ) + Complex.I * (T : ℂ))‖) := by
    dsimp [T]
    exact topIntegral_swap (x := x) (T := Real.sqrt x)
  have htop : (∫ (u : ℝ) in leftRe x..perronRe x, ‖psiIntF x ((u : ℂ) + (T : ℂ) * Complex.I)‖) ≤
      C * (1 + Real.log x) ^ 3 * (Real.log (T + 3) + 1) ^ 3 * (x : ℝ) ^ perronRe x *
        (perronRe x - leftRe x) / T := by
    rw [hswTop]
    exact htop0
  have hbot := bottomIntegral_le h hC0 hC hx8 (T := T) hT2'
  have hleft := leftIntegral_le h hC0 hC hx8 (T := T) hT2'
  -- hn : ‖perronZeta x T - x‖ ≤ (1/(2π))·(∫top' + ∫bot + ∫left)   (with T)
  -- rewrite the three integrals inside hn to match our bound statements:

  let E : ℝ := C * (1 + Real.log x) ^ 3 * (Real.log (T + 3) + 1) ^ 3 * (x : ℝ) ^ perronRe x *
      (perronRe x - leftRe x) / T
  let LE : ℝ := 8 * C * (1 + Real.log x) ^ 3 * (x : ℝ) ^ leftRe x * (Real.log (T + 3) + 1) ^ 3 *
      (Real.log (T / leftRe x) + 1)
  have htopE : (∫ (u : ℝ) in leftRe x..perronRe x, ‖psiIntF x ((u : ℂ) + (T : ℂ) * Complex.I)‖) ≤ E := by
    dsimp [E, T]
    exact htop
  have hbotE : (∫ (u : ℝ) in leftRe x..perronRe x, ‖psiIntF x ((u : ℂ) - (T : ℂ) * Complex.I)‖) ≤ E := by
    dsimp [E, T]
    exact hbot
  have hleftE : (∫ (t : ℝ) in -T..T, ‖psiIntF x ((leftRe x : ℂ) + (t : ℂ) * Complex.I)‖) ≤ LE := by
    dsimp [LE, T]
    exact hleft
  have hsum : (∫ (u : ℝ) in leftRe x..perronRe x, ‖psiIntF x ((u : ℂ) + (T : ℂ) * Complex.I)‖) +
        (∫ (u : ℝ) in leftRe x..perronRe x, ‖psiIntF x ((u : ℂ) - (T : ℂ) * Complex.I)‖) +
        (∫ (t : ℝ) in -T..T, ‖psiIntF x ((leftRe x : ℂ) + (t : ℂ) * Complex.I)‖) ≤ E + E + LE := by
    nlinarith
  have hcoef : 0 ≤ 1 / (2 * Real.pi) := by positivity
  have hstep := le_trans hn (mul_le_mul_of_nonneg_left hsum hcoef)
  have hconv : (1 / (2 * Real.pi)) * (E + E + LE) =
      (1 / (2 * Real.pi)) * (2 * E + LE) := by ring
  rw [hconv] at hstep
  -- unfold E, LE, T to match the statement
  dsimp [E, LE, T] at hstep
  simpa [mul_add, mul_assoc] using hstep

/-- The truncated-Perron error constant from `chebyshevPsi_truncatedPerron`. -/
noncomputable def perronErrC : ℝ := Classical.choose chebyshevPsi_truncatedPerron

lemma perronErrC_pos : 0 < perronErrC := (Classical.choose_spec chebyshevPsi_truncatedPerron).1

/-- `‖ψ(x) − perronZeta x T‖` is bounded by the truncated-Perron error (in `ζ'/ζ` form). -/
lemma psi_sub_perronZeta_le {x T : ℝ} (hx : 3 ≤ x) (hT : 2 ≤ T) :
    ‖(Chebyshev.psi x : ℂ) - perronZeta x T‖ ≤
      perronErrC * (x * (Real.log x) ^ 2 / T + Real.log x) := by
  have hCp := (Classical.choose_spec chebyshevPsi_truncatedPerron).2 x hx T hT
  -- hCp: bound with the LSeries integrand at σ := 1 + 1/log x
  let σ : ℝ := 1 + 1 / Real.log x
  have hxpos : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hσ1 : 1 < σ := by dsimp [σ]; linarith [one_div_pos.mpr hlog]
  have hint : (∫ (t : ℝ) in -T..T,
      (LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
          ((σ : ℂ) + Complex.I * (t : ℂ))) *
        (x : ℂ) ^ ((σ : ℂ) + Complex.I * (t : ℂ)) /
        ((σ : ℂ) + Complex.I * (t : ℂ))) =
      (∫ (t : ℝ) in -T..T, psiIntF x ((σ : ℂ) + Complex.I * (t : ℂ))) := by
    have hl := lSeries_mangoldt_integral_eq_zeta_logDeriv x σ T hσ1
    simpa [psiIntF, σ] using hl
  -- perronZeta x T = (1/(2π))·∫(ζ'/ζ-form): compare with cheb integral
  have hmain : (∫ (t : ℝ) in -T..T,
      (LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
          ((σ : ℂ) + Complex.I * (t : ℂ))) *
        (x : ℂ) ^ ((σ : ℂ) + Complex.I * (t : ℂ)) /
        ((σ : ℂ) + Complex.I * (t : ℂ))) =
      perronRight x T := by
    rw [hint]
    -- perronRight uses point (perronRe x : ℂ) + (t:ℂ)*I vs (σ : ℂ)+I*(t:ℂ): σ = perronRe x
    have hσeq : σ = perronRe x := by dsimp [σ, perronRe]
    have hper : perronRight x T = (∫ (t : ℝ) in -T..T, psiIntF x ((σ : ℂ) + Complex.I * (t : ℂ))) := by
      dsimp [perronRight]
      apply intervalIntegral.integral_congr
      intro t ht
      change psiIntF x ((perronRe x : ℂ) + (t : ℂ) * Complex.I) =
          psiIntF x ((σ : ℂ) + Complex.I * (t : ℂ))
      have hp : ((perronRe x : ℂ) + (t : ℂ) * Complex.I) = ((σ : ℂ) + Complex.I * (t : ℂ)) := by
        rw [← hσeq]
        ring
      rw [hp]
    exact hper.symm
  have hperZ : perronZeta x T = (1 / (2 * Real.pi)) * (∫ (t : ℝ) in -T..T,
      (LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
          ((σ : ℂ) + Complex.I * (t : ℂ))) *
        (x : ℂ) ^ ((σ : ℂ) + Complex.I * (t : ℂ)) /
        ((σ : ℂ) + Complex.I * (t : ℂ))) := by
    dsimp [perronZeta]
    rw [hmain]
  rw [hperZ]
  dsimp [perronErrC]
  exact hCp


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

/-- `|ψ(x) − x|` combined bound from the truncated-Perron error and the contour estimate. -/
lemma psi_sub_id_bound (h : RiemannHypothesis) {C : ℝ} (hC0 : 0 < C)
    (hC : ∀ (δ σ t : ℝ), 0 < δ → δ ≤ 1 → (1 / 2 + δ) ≤ σ → σ ≤ 2 →
      (1 / 4 ≤ ‖(((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) - 1‖) →
      ‖(deriv riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)) /
          riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)‖ ≤
        C * (1 + 1 / δ) ^ 3 * (Real.log (|t| + 3) + 1) ^ 3)
    {x : ℝ} (hx : Real.exp 16 ≤ x) :
    |Chebyshev.psi x - x| ≤
      perronErrC * (x * (Real.log x) ^ 2 / Real.sqrt x + Real.log x) +
        (1 / (2 * Real.pi)) *
          (2 * (C * (1 + Real.log x) ^ 3 * (Real.log (Real.sqrt x + 3) + 1) ^ 3 *
              (x : ℝ) ^ perronRe x * (perronRe x - leftRe x) / Real.sqrt x) +
           8 * C * (1 + Real.log x) ^ 3 * (x : ℝ) ^ leftRe x *
             (Real.log (Real.sqrt x + 3) + 1) ^ 3 * (Real.log (Real.sqrt x / leftRe x) + 1)) := by
  have hx3 : 3 ≤ x := by
    exact le_trans (le_of_lt exp16_gt_three) hx
  have hT2 : 2 ≤ Real.sqrt x := sqrt_ge_two_of_exp_sixteen_le hx
  have herr := psi_sub_perronZeta_le (x := x) (T := Real.sqrt x) hx3 hT2
  have hcont := perronZeta_sqrt_bound h hC0 hC hx
  have hreal : |Chebyshev.psi x - x| = ‖(Chebyshev.psi x : ℂ) - (x : ℂ)‖ := by
    rw [← Complex.ofReal_sub]
    rw [Complex.norm_real, Real.norm_eq_abs]
  have htri : ‖(Chebyshev.psi x : ℂ) - (x : ℂ)‖ ≤
      ‖(Chebyshev.psi x : ℂ) - perronZeta x (Real.sqrt x)‖ +
        ‖perronZeta x (Real.sqrt x) - (x : ℂ)‖ := by
    have h := norm_add_le ((Chebyshev.psi x : ℂ) - perronZeta x (Real.sqrt x))
      (perronZeta x (Real.sqrt x) - (x : ℂ))
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
  rw [hreal]
  linarith

/-- **Lagarias-type consequence of RH:** `|ψ(x) − x| ≤ C√x (log x)^10` for large `x`. -/
theorem chebyshevPsi_sub_id_rh_bound (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      |Chebyshev.psi x - x| ≤ C * Real.sqrt x * (Real.log x) ^ 10 := by
  let Cst : ℝ := Classical.choose zeta_logDeriv_strip_bound_rh
  have hCst0 : 0 < Cst := (Classical.choose_spec zeta_logDeriv_strip_bound_rh).1
  have hCst : ∀ (δ σ t : ℝ), 0 < δ → δ ≤ 1 → (1 / 2 + δ) ≤ σ → σ ≤ 2 →
      (1 / 4 ≤ ‖(((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) - 1‖) →
      ‖(deriv riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)) /
          riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)‖ ≤
        Cst * (1 + 1 / δ) ^ 3 * (Real.log (|t| + 3) + 1) ^ 3 := by
    intro δ σ t hδ0 hδ1 hσlo hσhi hdist
    exact (Classical.choose_spec zeta_logDeriv_strip_bound_rh).2 h δ σ t hδ0 hδ1 hσlo hσhi hdist
  let Cfin : ℝ := (perronErrC + Cst + 1) * 1000000
  have hCfin : 0 < Cfin := by
    dsimp [Cfin]
    have hper : 0 < perronErrC := perronErrC_pos
    nlinarith
  refine ⟨Cfin, hCfin, Real.exp 16, ?_⟩
  intro x hx
  have hb := psi_sub_id_bound h hCst0 hCst hx
  have hdom := Commons.Analysis.Real.combinedBound_domination_full (C := Cst) (P := perronErrC) hCst0 (le_of_lt perronErrC_pos) hx
  have heq : perronErrC * (x * (Real.log x) ^ 2 / Real.sqrt x + Real.log x) +
        (1 / (2 * Real.pi)) *
          (2 * (Cst * (1 + Real.log x) ^ 3 * (Real.log (Real.sqrt x + 3) + 1) ^ 3 *
              (x : ℝ) ^ perronRe x * (perronRe x - leftRe x) / Real.sqrt x) +
           8 * Cst * (1 + Real.log x) ^ 3 * (x : ℝ) ^ leftRe x *
             (Real.log (Real.sqrt x + 3) + 1) ^ 3 * (Real.log (Real.sqrt x / leftRe x) + 1)) =
      perronErrC * (x * (Real.log x) ^ 2 / Real.sqrt x + Real.log x) +
        (1 / (2 * Real.pi)) *
          (2 * (Cst * (1 + Real.log x) ^ 3 * (Real.log (Real.sqrt x + 3) + 1) ^ 3 *
              (x : ℝ) ^ (1 + 1 / Real.log x) * (1 / 2) / Real.sqrt x) +
           8 * Cst * (1 + Real.log x) ^ 3 * (x : ℝ) ^ (1 / 2 + 1 / Real.log x) *
             (Real.log (Real.sqrt x + 3) + 1) ^ 3 *
             (Real.log (Real.sqrt x / (1 / 2 + 1 / Real.log x)) + 1)) := by
    have hpd : perronRe x - leftRe x = 1 / 2 := by dsimp [perronRe, leftRe]; ring
    rw [hpd]
    rw [perronRe, leftRe]
  calc
    |Chebyshev.psi x - x| ≤
        perronErrC * (x * (Real.log x) ^ 2 / Real.sqrt x + Real.log x) +
          (1 / (2 * Real.pi)) *
            (2 * (Cst * (1 + Real.log x) ^ 3 * (Real.log (Real.sqrt x + 3) + 1) ^ 3 *
                (x : ℝ) ^ perronRe x * (perronRe x - leftRe x) / Real.sqrt x) +
             8 * Cst * (1 + Real.log x) ^ 3 * (x : ℝ) ^ leftRe x *
               (Real.log (Real.sqrt x + 3) + 1) ^ 3 * (Real.log (Real.sqrt x / leftRe x) + 1)) := hb
    _ = perronErrC * (x * (Real.log x) ^ 2 / Real.sqrt x + Real.log x) +
        (1 / (2 * Real.pi)) *
          (2 * (Cst * (1 + Real.log x) ^ 3 * (Real.log (Real.sqrt x + 3) + 1) ^ 3 *
              (x : ℝ) ^ (1 + 1 / Real.log x) * (1 / 2) / Real.sqrt x) +
           8 * Cst * (1 + Real.log x) ^ 3 * (x : ℝ) ^ (1 / 2 + 1 / Real.log x) *
             (Real.log (Real.sqrt x + 3) + 1) ^ 3 *
             (Real.log (Real.sqrt x / (1 / 2 + 1 / Real.log x)) + 1)) := heq
    _ ≤ (perronErrC + Cst + 1) * 1000000 * Real.sqrt x * (Real.log x) ^ 10 := hdom
    _ = Cfin * Real.sqrt x * (Real.log x) ^ 10 := by rfl

end
end Commons.NumberTheory.Zeta
