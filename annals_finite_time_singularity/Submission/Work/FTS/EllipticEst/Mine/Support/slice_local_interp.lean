import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Mine.Support

open MeasureTheory intervalIntegral Set

/-- **Cauchy–Schwarz for interval integrals.**  For `f` continuous on `[u,v]` with `u ≤ v`,
`(∫_u^v |f|)^2 ≤ (v - u) ∫_u^v f^2`.  Proof: the quadratic polynomial
`λ ↦ ∫_u^v (λ - |f|)^2` is nonnegative, and at `λ = (∫_u^v |f|)/(v-u)` its value is
`(∫_u^v f^2) - (∫_u^v |f|)^2/(v-u)`. -/
theorem sq_integral_abs_le_aux {f : ℝ → ℝ} {u v : ℝ} (huv : u ≤ v)
    (hf : ContinuousOn f (Set.Icc u v)) :
    (∫ t in u..v, |f t|) ^ 2 ≤ (v - u) * ∫ t in u..v, (f t) ^ 2 := by
  rcases eq_or_lt_of_le huv with h | h
  · subst h; simp
  have hb : 0 < v - u := sub_pos.mpr h
  have hInt1 : IntervalIntegrable (fun t : ℝ => (f t) ^ 2) volume u v :=
    (hf.pow 2).intervalIntegrable_of_Icc huv
  have hInt2 : IntervalIntegrable (fun t : ℝ => |f t|) volume u v :=
    (hf.abs).intervalIntegrable_of_Icc huv
  set A := ∫ t in u..v, |f t|
  set B := ∫ t in u..v, (f t) ^ 2
  have hexp : ∀ lam : ℝ, ∫ t in u..v, (lam - |f t|) ^ 2 = lam ^ 2 * (v - u) - 2 * lam * A + B := by
    intro lam
    have h1 : (fun t => (lam - |f t|) ^ 2) = fun t => lam ^ 2 - 2 * lam * |f t| + (f t) ^ 2 := by
      funext t
      rw [show (lam - |f t|) ^ 2 = lam ^ 2 - 2 * lam * |f t| + |f t| ^ 2 by ring, sq_abs]
    have hint1 : IntervalIntegrable (fun t : ℝ => lam ^ 2 - 2 * lam * |f t|) volume u v :=
      intervalIntegrable_const.sub (hInt2.const_mul (2 * lam))
    rw [h1, intervalIntegral.integral_add hint1 hInt1,
      intervalIntegral.integral_sub intervalIntegrable_const (hInt2.const_mul (2 * lam)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  have hmain : 0 ≤ ∫ t in u..v, (A / (v - u) - |f t|) ^ 2 :=
    integral_nonneg huv (fun t _ => sq_nonneg _)
  rw [hexp (A / (v - u))] at hmain
  have e1 : (A / (v - u)) ^ 2 * (v - u) = A ^ 2 / (v - u) := by field_simp
  have e2 : 2 * (A / (v - u)) * A = 2 * (A ^ 2 / (v - u)) := by field_simp
  rw [e1, e2] at hmain
  have h4 : A ^ 2 / (v - u) ≤ B := by linarith
  rw [div_le_iff₀ hb] at h4
  nlinarith [h4]

/-- The two-fold FTC identity for the left endpoint. -/
theorem ftc_fwd_aux {g : ℝ → ℝ} {p r u v : ℝ} (huv : u ≤ v)
    (hsub : Icc u v ⊆ Ioo p r) (hg : ContDiffOn ℝ 2 g (Ioo p r)) :
    (v - u) * deriv g u = (g v - g u) - ∫ t in u..v, (v - t) * deriv (deriv g) t := by
  have hsub' : Ioo u v ⊆ Ioo p r := fun y hy => hsub ⟨hy.1.le, hy.2.le⟩
  have hCd : ContinuousOn (deriv g) (Ioo p r) :=
    hg.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have h1 : ContDiffOn ℝ 1 (deriv g) (Ioo p r) := hg.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hDd : DifferentiableOn ℝ (deriv g) (Ioo p r) := h1.differentiableOn (by norm_num)
  have hCdd : ContinuousOn (deriv (deriv g)) (Ioo p r) := by
    have h2 := (contDiffOn_succ_iff_deriv_of_isOpen (n := 0) (f := deriv g) isOpen_Ioo).mp h1
    exact contDiffOn_zero.mp h2.2.2
  have hderiv : ∀ y ∈ Ioo u v,
      HasDerivAt (fun t => (v - t) * deriv g t + g t) ((v - y) * deriv (deriv g) y) y := by
    intro y hy
    have hyr : y ∈ Ioo p r := hsub' hy
    have hdg : HasDerivAt g (deriv g y) y :=
      ((hg.differentiableOn (by norm_num)).differentiableAt
        (Ioo_mem_nhds hyr.1 hyr.2)).hasDerivAt
    have hddg : HasDerivAt (deriv g) (deriv (deriv g) y) y :=
      (hDd.differentiableAt (Ioo_mem_nhds hyr.1 hyr.2)).hasDerivAt
    have hconst : HasDerivAt (fun t : ℝ => v - t) (-1) y := (hasDerivAt_id y).const_sub v
    have hmain := (hconst.mul hddg).add hdg
    have hval : -1 * deriv g y + (v - y) * deriv (deriv g) y + deriv g y
        = (v - y) * deriv (deriv g) y := by ring
    rw [hval] at hmain
    convert hmain using 1
  have hFc : ContinuousOn (fun t => (v - t) * deriv g t + g t) (Icc u v) :=
    (((continuousOn_const (c := v)).sub continuousOn_id).mul (hCd.mono hsub)).add
      ((hg.continuousOn).mono hsub)
  have hint : IntervalIntegrable (fun t => (v - t) * deriv (deriv g) t) volume u v :=
    (((continuousOn_const (c := v)).sub continuousOn_id).mul (hCdd.mono hsub)).intervalIntegrable_of_Icc
      huv
  have hFTC := integral_eq_sub_of_hasDerivAt_of_le huv hFc hderiv hint
  have hsimpl : (v - v) * deriv g v + g v = g v := by ring
  rw [hsimpl] at hFTC
  linarith

/-- The two-fold FTC identity for the right endpoint. -/
theorem ftc_bwd_aux {g : ℝ → ℝ} {p r u v : ℝ} (huv : u ≤ v)
    (hsub : Icc u v ⊆ Ioo p r) (hg : ContDiffOn ℝ 2 g (Ioo p r)) :
    (v - u) * deriv g v = (g v - g u) + ∫ t in u..v, (t - u) * deriv (deriv g) t := by
  have hsub' : Ioo u v ⊆ Ioo p r := fun y hy => hsub ⟨hy.1.le, hy.2.le⟩
  have hCd : ContinuousOn (deriv g) (Ioo p r) :=
    hg.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have h1 : ContDiffOn ℝ 1 (deriv g) (Ioo p r) := hg.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hDd : DifferentiableOn ℝ (deriv g) (Ioo p r) := h1.differentiableOn (by norm_num)
  have hCdd : ContinuousOn (deriv (deriv g)) (Ioo p r) := by
    have h2 := (contDiffOn_succ_iff_deriv_of_isOpen (n := 0) (f := deriv g) isOpen_Ioo).mp h1
    exact contDiffOn_zero.mp h2.2.2
  have hderiv : ∀ y ∈ Ioo u v,
      HasDerivAt (fun t => (t - u) * deriv g t - g t) ((y - u) * deriv (deriv g) y) y := by
    intro y hy
    have hyr : y ∈ Ioo p r := hsub' hy
    have hdg : HasDerivAt g (deriv g y) y :=
      ((hg.differentiableOn (by norm_num)).differentiableAt
        (Ioo_mem_nhds hyr.1 hyr.2)).hasDerivAt
    have hddg : HasDerivAt (deriv g) (deriv (deriv g) y) y :=
      (hDd.differentiableAt (Ioo_mem_nhds hyr.1 hyr.2)).hasDerivAt
    have hconst : HasDerivAt (fun t : ℝ => t - u) 1 y := (hasDerivAt_id y).sub_const u
    have hmain := (hconst.mul hddg).sub hdg
    have hval : 1 * deriv g y + (y - u) * deriv (deriv g) y - deriv g y
        = (y - u) * deriv (deriv g) y := by ring
    rw [hval] at hmain
    convert hmain using 1
  have hFc : ContinuousOn (fun t => (t - u) * deriv g t - g t) (Icc u v) :=
    (((continuousOn_id.sub (continuousOn_const (c := u))).mul (hCd.mono hsub))).sub
      ((hg.continuousOn).mono hsub)
  have hint : IntervalIntegrable (fun t => (t - u) * deriv (deriv g) t) volume u v :=
    (((continuousOn_id.sub (continuousOn_const (c := u))).mul (hCdd.mono hsub))).intervalIntegrable_of_Icc
      huv
  have hFTC := integral_eq_sub_of_hasDerivAt_of_le huv hFc hderiv hint
  have hsimpl : (u - u) * deriv g u - g u = -g u := by ring
  rw [hsimpl] at hFTC
  linarith

/-- Pointwise bound, left half:
`(g'x)^2 ≤ (4/h^2)(g(x+h)^2 + g(x)^2) + 2h ∫_x^{x+h}(g'')^2`. -/
theorem pointwise_fwd_aux {g : ℝ → ℝ} {p r x h : ℝ} (hh : 0 < h)
    (hsub : Icc x (x + h) ⊆ Ioo p r) (hg : ContDiffOn ℝ 2 g (Ioo p r)) :
    (deriv g x) ^ 2
      ≤ (4 / h ^ 2) * ((g (x + h)) ^ 2 + (g x) ^ 2)
        + 2 * h * (∫ t in x..(x + h), (deriv (deriv g) t) ^ 2) := by
  have hxle : x ≤ x + h := by linarith
  have hCdd : ContinuousOn (deriv (deriv g)) (Ioo p r) := by
    have h1 : ContDiffOn ℝ 1 (deriv g) (Ioo p r) := hg.deriv_of_isOpen isOpen_Ioo (by norm_num)
    have h2 := (contDiffOn_succ_iff_deriv_of_isOpen (n := 0) (f := deriv g) isOpen_Ioo).mp h1
    exact contDiffOn_zero.mp h2.2.2
  have hCddx : ContinuousOn (deriv (deriv g)) (Icc x (x + h)) := hCdd.mono hsub
  have hid := ftc_fwd_aux hxle hsub hg
  set K : ℝ := ∫ t in x..(x + h), (x + h - t) * deriv (deriv g) t with hKdef
  set B : ℝ := ∫ t in x..(x + h), |deriv (deriv g) t| with hBdef
  set F : ℝ := ∫ t in x..(x + h), (deriv (deriv g) t) ^ 2 with hFdef
  have hid' : h * deriv g x = (g (x + h) - g x) - K := by
    have h2 : x + h - x = h := by ring
    have h4 := hid
    rw [h2] at h4
    exact h4
  have hBnonneg : 0 ≤ B := by
    rw [hBdef]
    exact integral_nonneg hxle (fun t _ => abs_nonneg _)
  have hCSraw : B ^ 2 ≤ h * F := by
    have hcs := sq_integral_abs_le_aux hxle hCddx
    rw [← hBdef, ← hFdef, show x + h - x = h by ring] at hcs
    exact hcs
  have hKabs : |K| ≤ h * B := by
    have h1 : |∫ t in x..(x + h), (x + h - t) * deriv (deriv g) t|
        ≤ ∫ t in x..(x + h), |(x + h - t) * deriv (deriv g) t| :=
      abs_integral_le_integral_abs hxle
    rw [← hKdef] at h1
    have h2 : ∫ t in x..(x + h), |(x + h - t) * deriv (deriv g) t|
        ≤ ∫ t in x..(x + h), h * |deriv (deriv g) t| := by
      refine integral_mono_on hxle ?_ ?_ (fun t ht => ?_)
      · exact ((((continuousOn_const (c := x + h)).sub continuousOn_id).mul hCddx)).abs
          |>.intervalIntegrable_of_Icc hxle
      · exact (((continuousOn_const (c := h)).mul hCddx.abs)).intervalIntegrable_of_Icc hxle
      · rw [abs_mul]
        have h3 : |x + h - t| ≤ h := by
          rw [abs_of_nonneg (by linarith [ht.2])]
          linarith [ht.1]
        exact mul_le_mul_of_nonneg_right h3 (abs_nonneg _)
    have h3 : ∫ t in x..(x + h), h * |deriv (deriv g) t| = h * B := by
      rw [intervalIntegral.integral_const_mul, ← hBdef]
    linarith
  have hKsq : K ^ 2 ≤ h ^ 3 * F := by
    have h1 : K ^ 2 ≤ (h * B) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg (mul_nonneg hh.le hBnonneg)]
      exact hKabs
    have h2 : (h * B) ^ 2 ≤ h ^ 2 * (h * F) := by
      have he : (h * B) ^ 2 = h ^ 2 * B ^ 2 := by ring
      rw [he]
      exact mul_le_mul_of_nonneg_left hCSraw (sq_nonneg h)
    nlinarith [h1, h2]
  have hsq : h ^ 2 * (deriv g x) ^ 2 ≤ 2 * (g (x + h) - g x) ^ 2 + 2 * h ^ 3 * F := by
    have he : h ^ 2 * (deriv g x) ^ 2 = (h * deriv g x) ^ 2 := by ring
    rw [he, hid']
    nlinarith [hKsq, sq_nonneg ((g (x + h) - g x) + K)]
  have hfinal : h ^ 2 * (deriv g x) ^ 2
      ≤ 4 * ((g (x + h)) ^ 2 + (g x) ^ 2) + 2 * h ^ 3 * F := by
    nlinarith [hsq, sq_nonneg (g (x + h) + g x)]
  have hgoal1 : (deriv g x) ^ 2
      ≤ (4 * ((g (x + h)) ^ 2 + (g x) ^ 2) + 2 * h ^ 3 * F) / h ^ 2 := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < h ^ 2)]
    nlinarith [hfinal]
  have hgoal2 : (4 * ((g (x + h)) ^ 2 + (g x) ^ 2) + 2 * h ^ 3 * F) / h ^ 2
      = (4 / h ^ 2) * ((g (x + h)) ^ 2 + (g x) ^ 2) + 2 * h * F := by
    field_simp
    try ring
  rw [hgoal2] at hgoal1
  exact hgoal1

/-- Pointwise bound, right half:
`(g'x)^2 ≤ (4/h^2)(g(x)^2 + g(x-h)^2) + 2h ∫_{x-h}^{x}(g'')^2`. -/
theorem pointwise_bwd_aux {g : ℝ → ℝ} {p r x h : ℝ} (hh : 0 < h)
    (hsub : Icc (x - h) x ⊆ Ioo p r) (hg : ContDiffOn ℝ 2 g (Ioo p r)) :
    (deriv g x) ^ 2
      ≤ (4 / h ^ 2) * ((g x) ^ 2 + (g (x - h)) ^ 2)
        + 2 * h * (∫ t in (x - h)..x, (deriv (deriv g) t) ^ 2) := by
  have hxle : x - h ≤ x := by linarith
  have hCdd : ContinuousOn (deriv (deriv g)) (Ioo p r) := by
    have h1 : ContDiffOn ℝ 1 (deriv g) (Ioo p r) := hg.deriv_of_isOpen isOpen_Ioo (by norm_num)
    have h2 := (contDiffOn_succ_iff_deriv_of_isOpen (n := 0) (f := deriv g) isOpen_Ioo).mp h1
    exact contDiffOn_zero.mp h2.2.2
  have hCddx : ContinuousOn (deriv (deriv g)) (Icc (x - h) x) := hCdd.mono hsub
  have hid := ftc_bwd_aux hxle hsub hg
  set K : ℝ := ∫ t in (x - h)..x, (t - (x - h)) * deriv (deriv g) t with hKdef
  set B : ℝ := ∫ t in (x - h)..x, |deriv (deriv g) t| with hBdef
  set F : ℝ := ∫ t in (x - h)..x, (deriv (deriv g) t) ^ 2 with hFdef
  have hid' : h * deriv g x = (g x - g (x - h)) + K := by
    have h2 : x - (x - h) = h := by ring
    have h4 := hid
    rw [h2] at h4
    exact h4
  have hBnonneg : 0 ≤ B := by
    rw [hBdef]
    exact integral_nonneg hxle (fun t _ => abs_nonneg _)
  have hCSraw : B ^ 2 ≤ h * F := by
    have hcs := sq_integral_abs_le_aux hxle hCddx
    rw [← hBdef, ← hFdef, show x - (x - h) = h by ring] at hcs
    exact hcs
  have hKabs : |K| ≤ h * B := by
    have h1 : |∫ t in (x - h)..x, (t - (x - h)) * deriv (deriv g) t|
        ≤ ∫ t in (x - h)..x, |(t - (x - h)) * deriv (deriv g) t| :=
      abs_integral_le_integral_abs hxle
    rw [← hKdef] at h1
    have h2 : ∫ t in (x - h)..x, |(t - (x - h)) * deriv (deriv g) t|
        ≤ ∫ t in (x - h)..x, h * |deriv (deriv g) t| := by
      refine integral_mono_on hxle ?_ ?_ (fun t ht => ?_)
      · exact ((((continuousOn_id).sub (continuousOn_const (c := x - h))).mul hCddx)).abs
          |>.intervalIntegrable_of_Icc hxle
      · exact (((continuousOn_const (c := h)).mul hCddx.abs)).intervalIntegrable_of_Icc hxle
      · rw [abs_mul]
        have h3 : |t - (x - h)| ≤ h := by
          rw [abs_of_nonneg (by linarith [ht.1])]
          linarith [ht.2]
        exact mul_le_mul_of_nonneg_right h3 (abs_nonneg _)
    have h3 : ∫ t in (x - h)..x, h * |deriv (deriv g) t| = h * B := by
      rw [intervalIntegral.integral_const_mul, ← hBdef]
    linarith
  have hKsq : K ^ 2 ≤ h ^ 3 * F := by
    have h1 : K ^ 2 ≤ (h * B) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg (mul_nonneg hh.le hBnonneg)]
      exact hKabs
    have h2 : (h * B) ^ 2 ≤ h ^ 2 * (h * F) := by
      have he : (h * B) ^ 2 = h ^ 2 * B ^ 2 := by ring
      rw [he]
      exact mul_le_mul_of_nonneg_left hCSraw (sq_nonneg h)
    nlinarith [h1, h2]
  have hsq : h ^ 2 * (deriv g x) ^ 2 ≤ 2 * (g x - g (x - h)) ^ 2 + 2 * h ^ 3 * F := by
    have he : h ^ 2 * (deriv g x) ^ 2 = (h * deriv g x) ^ 2 := by ring
    rw [he, hid']
    nlinarith [hKsq, sq_nonneg ((g x - g (x - h)) - K)]
  have hfinal : h ^ 2 * (deriv g x) ^ 2
      ≤ 4 * ((g x) ^ 2 + (g (x - h)) ^ 2) + 2 * h ^ 3 * F := by
    nlinarith [hsq, sq_nonneg (g x + g (x - h))]
  have hgoal1 : (deriv g x) ^ 2
      ≤ (4 * ((g x) ^ 2 + (g (x - h)) ^ 2) + 2 * h ^ 3 * F) / h ^ 2 := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < h ^ 2)]
    nlinarith [hfinal]
  have hgoal2 : (4 * ((g x) ^ 2 + (g (x - h)) ^ 2) + 2 * h ^ 3 * F) / h ^ 2
      = (4 / h ^ 2) * ((g x) ^ 2 + (g (x - h)) ^ 2) + 2 * h * F := by
    field_simp
    try ring
  rw [hgoal2] at hgoal1
  exact hgoal1

/-- The primitive of a nonnegative interval-integrable function is monotone. -/
theorem monotoneOn_primitive_aux {φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hint : IntervalIntegrable φ volume a b) (hnn : ∀ x, 0 ≤ φ x) :
    MonotoneOn (fun x => ∫ t in a..x, φ t) (Set.Icc a b) := by
  intro x hx y hy hxy
  have hax : a ≤ x := hx.1
  have hyb : y ≤ b := hy.2
  have h1 : IntervalIntegrable φ volume a x :=
    hint.mono_set (by
      rw [uIcc_of_le hax, uIcc_of_le hab]
      exact Icc_subset_Icc le_rfl (le_trans hxy hyb))
  have h2 : IntervalIntegrable φ volume x y :=
    hint.mono_set (by
      rw [uIcc_of_le hxy, uIcc_of_le hab]
      exact Icc_subset_Icc hax hyb)
  have hadd := intervalIntegral.integral_add_adjacent_intervals h1 h2
  have h3 : 0 ≤ ∫ t in x..y, φ t := integral_nonneg hxy (fun t _ => hnn t)
  linarith

/-- **Moving-window bound.**  For a nonnegative interval-integrable `φ`, both the right-shifted
window integral `x ↦ ∫_x^{x+h} φ` on `[a, a+h]` and the left-shifted window integral
`x ↦ ∫_{x-h}^{x} φ` on `[a+h, a+2h]` are interval integrable, with integral at most
`h · ∫_a^{a+2h} φ`. -/
theorem shifted_primitive_bound_aux {φ : ℝ → ℝ} {a h : ℝ} (hh : 0 ≤ h)
    (hint : IntervalIntegrable φ volume a (a + 2 * h)) (hnn : ∀ x, 0 ≤ φ x) :
    (IntervalIntegrable (fun x => ∫ t in x..(x + h), φ t) volume a (a + h) ∧
      ∫ x in a..(a + h), (∫ t in x..(x + h), φ t) ≤ h * ∫ t in a..(a + 2 * h), φ t) ∧
    (IntervalIntegrable (fun x => ∫ t in (x - h)..x, φ t) volume (a + h) (a + 2 * h) ∧
      ∫ x in (a + h)..(a + 2 * h), (∫ t in (x - h)..x, φ t)
        ≤ h * ∫ t in a..(a + 2 * h), φ t) := by
  have hab : a ≤ a + 2 * h := by linarith
  have hah : a ≤ a + h := by linarith
  have hh2h : a + h ≤ a + 2 * h := by linarith
  have hmono : MonotoneOn (fun x => ∫ t in a..x, φ t) (Set.Icc a (a + 2 * h)) :=
    monotoneOn_primitive_aux hab hint hnn
  have hPrim : IntervalIntegrable (fun x => ∫ t in a..x, φ t) volume a (a + 2 * h) := by
    apply MonotoneOn.intervalIntegrable
    rwa [uIcc_of_le hab]
  have hsub_big : Set.uIcc a (a + h) ⊆ Set.uIcc a (a + 2 * h) := by
    rw [uIcc_of_le hah, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl hh2h
  have hPrim_mid : IntervalIntegrable (fun x => ∫ t in a..x, φ t) volume a (a + h) :=
    hPrim.mono_set hsub_big
  have hPrim_mid' : IntervalIntegrable (fun x => ∫ t in a..x, φ t) volume (a + h) (a + 2 * h) := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le hh2h]
    exact hmono.mono (Icc_subset_Icc (by linarith) le_rfl)
  have hmonoShift : MonotoneOn (fun x => ∫ t in a..(x + h), φ t) (Set.Icc a (a + h)) :=
    fun x hx y hy hxy =>
      hmono ⟨by linarith [hx.1], by linarith [hx.2]⟩
        ⟨by linarith [hy.1], by linarith [hy.2]⟩ (by linarith)
  have hmonoShift' : MonotoneOn (fun x => ∫ t in a..(x - h), φ t) (Set.Icc (a + h) (a + 2 * h)) :=
    fun x hx y hy hxy =>
      hmono ⟨by linarith [hx.1], by linarith [hx.2]⟩
        ⟨by linarith [hy.1], by linarith [hy.2]⟩ (by linarith)
  have hShiftInt : IntervalIntegrable (fun x => ∫ t in a..(x + h), φ t) volume a (a + h) := by
    apply MonotoneOn.intervalIntegrable
    rwa [uIcc_of_le hah]
  have hShiftInt' : IntervalIntegrable (fun x => ∫ t in a..(x - h), φ t)
      volume (a + h) (a + 2 * h) := by
    apply MonotoneOn.intervalIntegrable
    rwa [uIcc_of_le hh2h]
  -- telescoping identity for the right window
  have hpoint : ∀ x ∈ Set.Icc a (a + h),
      ∫ t in x..(x + h), φ t = (∫ t in a..(x + h), φ t) - ∫ t in a..x, φ t := by
    intro x hx
    have hxa : a ≤ x := hx.1
    have h1 : IntervalIntegrable φ volume a x :=
      hint.mono_set (by
        rw [uIcc_of_le hxa, uIcc_of_le hab]
        exact Icc_subset_Icc le_rfl (by linarith [hx.2]))
    have hxy : x ≤ x + h := by linarith
    have h2 : IntervalIntegrable φ volume x (x + h) :=
      hint.mono_set (by
        rw [uIcc_of_le hxy, uIcc_of_le hab]
        exact Icc_subset_Icc hxa (by linarith [hx.2]))
    have hadd := intervalIntegral.integral_add_adjacent_intervals h1 h2
    linarith
  have hFint : IntervalIntegrable (fun x => ∫ t in x..(x + h), φ t) volume a (a + h) := by
    refine IntervalIntegrable.congr (f := fun x => (∫ t in a..(x + h), φ t) - ∫ t in a..x, φ t) ?_
      (hShiftInt.sub hPrim_mid)
    intro x hx
    have hx' : x ∈ Set.Icc a (a + h) := by
      rw [← uIcc_of_le hah]
      exact uIoc_subset_uIcc hx
    exact (hpoint x hx').symm
  -- bound on the tail of the primitive
  have htail : ∫ x in (a + h)..(a + 2 * h), (∫ t in a..x, φ t)
      ≤ h * ∫ t in a..(a + 2 * h), φ t := by
    have h3 : ∫ x in (a + h)..(a + 2 * h), (∫ t in a..x, φ t)
        ≤ ∫ x in (a + h)..(a + 2 * h), (∫ t in a..(a + 2 * h), φ t) := by
      refine integral_mono_on hh2h hPrim_mid' intervalIntegrable_const (fun x hx => ?_)
      exact hmono ⟨by linarith [hx.1], by linarith [hx.2]⟩
        ⟨by linarith, le_refl _⟩ (by linarith [hx.2])
    have h4 : ∫ x in (a + h)..(a + 2 * h), (∫ t in a..(a + 2 * h), φ t)
        = h * ∫ t in a..(a + 2 * h), φ t := by
      rw [intervalIntegral.integral_const, smul_eq_mul, show (a + 2 * h) - (a + h) = h by ring]
    exact h3.trans h4.le
  -- the right-window bound
  have hright : ∫ x in a..(a + h), (∫ t in x..(x + h), φ t) ≤ h * ∫ t in a..(a + 2 * h), φ t := by
    have h1 : ∫ x in a..(a + h), (∫ t in x..(x + h), φ t)
        ≤ ∫ x in a..(a + h), (∫ t in a..(x + h), φ t) := by
      refine integral_mono_on hah hFint hShiftInt (fun x hx => ?_)
      rw [hpoint x hx]
      have hpos : 0 ≤ ∫ t in a..x, φ t := integral_nonneg hx.1 (fun t _ => hnn t)
      linarith
    have h2 : ∫ x in a..(a + h), (∫ t in a..(x + h), φ t)
        = ∫ x in (a + h)..(a + 2 * h), (∫ t in a..x, φ t) := by
      have hthis := intervalIntegral.integral_comp_add_right (a := a) (b := a + h)
        (fun u => ∫ t in a..u, φ t) h
      rwa [show a + h + h = a + 2 * h by ring] at hthis
    exact h1.trans (h2.trans_le htail)
  -- the left-window bound
  have hpointL : ∀ x ∈ Set.Icc (a + h) (a + 2 * h),
      ∫ t in (x - h)..x, φ t = (∫ t in a..x, φ t) - ∫ t in a..(x - h), φ t := by
    intro x hx
    have hxa : a ≤ x - h := by linarith [hx.1]
    have h1 : IntervalIntegrable φ volume a (x - h) :=
      hint.mono_set (by
        rw [uIcc_of_le hxa, uIcc_of_le hab]
        exact Icc_subset_Icc le_rfl (by linarith [hx.2]))
    have hxy : x - h ≤ x := by linarith
    have h2 : IntervalIntegrable φ volume (x - h) x :=
      hint.mono_set (by
        rw [uIcc_of_le hxy, uIcc_of_le hab]
        exact Icc_subset_Icc hxa (by linarith [hx.2]))
    have hadd := intervalIntegral.integral_add_adjacent_intervals h1 h2
    linarith
  have hFintL : IntervalIntegrable (fun x => ∫ t in (x - h)..x, φ t)
      volume (a + h) (a + 2 * h) := by
    refine IntervalIntegrable.congr
      (f := fun x => (∫ t in a..x, φ t) - ∫ t in a..(x - h), φ t) ?_
      (hPrim_mid'.sub hShiftInt')
    intro x hx
    have hx' : x ∈ Set.Icc (a + h) (a + 2 * h) := by
      rw [← uIcc_of_le hh2h]
      exact uIoc_subset_uIcc hx
    exact (hpointL x hx').symm
  have hleft : ∫ x in (a + h)..(a + 2 * h), (∫ t in (x - h)..x, φ t)
      ≤ h * ∫ t in a..(a + 2 * h), φ t := by
    have h1 : ∫ x in (a + h)..(a + 2 * h), (∫ t in (x - h)..x, φ t)
        ≤ ∫ x in (a + h)..(a + 2 * h), (∫ t in a..x, φ t) := by
      refine integral_mono_on hh2h hFintL hPrim_mid' (fun x hx => ?_)
      rw [hpointL x hx]
      have hpos : 0 ≤ ∫ t in a..(x - h), φ t :=
        integral_nonneg (by linarith [hx.1]) (fun t _ => hnn t)
      linarith
    exact h1.trans htail
  exact ⟨⟨hFint, hright⟩, hFintL, hleft⟩

/-- **Second-order interpolation inequality on an interval.**  For `g` of class `C²` on an open
interval containing the compact interval `[a,b]` of length `L = b - a > 0`,
`∫_a^b (g')² ≤ (64/L²) ∫_a^b g² + L² ∫_a^b (g'')²`.  Route: split `[a,b]` at the midpoint
`m = (a+b)/2`, `h = L/2`.  On `[a,m]`, the two-fold FTC identity
`h·g'(x) = (g(x+h) - g(x)) - ∫_x^{x+h} ∫_x^t g''(s) ds dt` gives
`|g'(x)| ≤ (|g(x+h)|+|g(x)|)/h + ∫_x^{x+h}|g''|` and
`(∫_x^{x+h}|g''|)² ≤ h ∫_x^{x+h}(g'')² ≤ h ∫_a^b (g'')²`; squaring and integrating over `x ∈ [a,m]`
(using `∫_a^m |g(x+h)|² dx = ∫_m^b |g|²`) gives constants `8/h²` and `2h²`; the same argument
backwards on `[m,b]`, added, gives the claim.  All functions are continuous on the compact `[a,b]`
by `hg`, so all integrals are genuine. -/
theorem slice_local_interp {g : ℝ → ℝ} {p a b r : ℝ}
    (hpa : p < a) (hab : a < b) (hbr : b < r)
    (hg : ContDiffOn ℝ 2 g (Set.Ioo p r))
    (hF : IntervalIntegrable (fun y : ℝ => (deriv (deriv g) y) ^ 2) MeasureTheory.volume a b) :
    (∫ y in a..b, (deriv g y) ^ 2)
      ≤ (64 / (b - a) ^ 2) * (∫ y in a..b, (g y) ^ 2)
        + (b - a) ^ 2 * (∫ y in a..b, (deriv (deriv g) y) ^ 2) := by
  -- ### setup
  set h : ℝ := (b - a) / 2 with hhdef
  set m : ℝ := a + h with hmdef
  have hh : 0 < h := by rw [hhdef]; linarith
  have hmh : m + h = b := by rw [hmdef, hhdef]; ring
  have hbm : b = a + 2 * h := by rw [← hmh, hmdef]; ring
  have hiff : a + 2 * h = b := hbm.symm
  have hab' : a ≤ b := le_of_lt hab
  have ham : a ≤ m := by rw [hmdef]; linarith
  have hmb : m ≤ b := by rw [← hmh]; linarith
  have hnn : ∀ x : ℝ, 0 ≤ (deriv (deriv g) x) ^ 2 := fun x => sq_nonneg _
  have hint_phi : IntervalIntegrable (fun y : ℝ => (deriv (deriv g) y) ^ 2) volume a (a + 2 * h) := by
    rw [hiff]; exact hF
  have hCd : ContinuousOn (deriv g) (Ioo p r) :=
    hg.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hsub_am : Icc a m ⊆ Ioo p r := fun y hy =>
    ⟨lt_of_lt_of_le hpa hy.1, lt_of_le_of_lt (le_trans hy.2 hmb) hbr⟩
  have hsub_mb : Icc m b ⊆ Ioo p r := fun y hy =>
    ⟨lt_of_lt_of_le hpa (le_trans ham hy.1), lt_of_le_of_lt hy.2 hbr⟩
  -- ### the moving-window bound
  have hsp := shifted_primitive_bound_aux (le_of_lt hh) hint_phi hnn
  obtain ⟨⟨hFint0, hFbd0⟩, hF'int0, hF'bd0⟩ := hsp
  have hFint : IntervalIntegrable (fun x : ℝ => ∫ t in x..(x + h), (deriv (deriv g) t) ^ 2)
      volume a m := by
    rw [hmdef]; exact hFint0
  have hF'int : IntervalIntegrable (fun x : ℝ => ∫ t in (x - h)..x, (deriv (deriv g) t) ^ 2)
      volume m b := by
    rw [hmdef, hbm]; exact hF'int0
  have hFbd : ∫ x in a..m, (∫ t in x..(x + h), (deriv (deriv g) t) ^ 2)
      ≤ h * ∫ y in a..b, (deriv (deriv g) y) ^ 2 := by
    rw [hmdef.symm, hiff] at hFbd0
    exact hFbd0
  have hF'bd : ∫ x in m..b, (∫ t in (x - h)..x, (deriv (deriv g) t) ^ 2)
      ≤ h * ∫ y in a..b, (deriv (deriv g) y) ^ 2 := by
    rw [hmdef.symm, hiff] at hF'bd0
    exact hF'bd0
  -- ### the left half `[a,m]`
  have hpt_fwd : ∀ x ∈ Set.Icc a m, (deriv g x) ^ 2
      ≤ (4 / h ^ 2) * ((g (x + h)) ^ 2 + (g x) ^ 2)
        + 2 * h * (∫ t in x..(x + h), (deriv (deriv g) t) ^ 2) := by
    intro x hx
    have hxmh : x + h ≤ b := by
      rw [← hmh]
      linarith [hx.2]
    exact pointwise_fwd_aux hh
      (fun y hy => ⟨lt_of_lt_of_le hpa (le_trans hx.1 hy.1),
        lt_of_le_of_lt (le_trans hy.2 hxmh) hbr⟩) hg
  have hcd_am : ContinuousOn (deriv g) (Icc a m) := hCd.mono hsub_am
  have hcont_shift : ContinuousOn (fun x : ℝ => (g (x + h)) ^ 2) (Icc a m) := by
    have hmap : MapsTo (fun x : ℝ => x + h) (Icc a m) (Ioo p r) := by
      intro x hx
      refine ⟨?_, ?_⟩
      · have : p < x := lt_of_lt_of_le hpa hx.1
        linarith
      · have hxmh : x + h ≤ b := by
          rw [← hmh]
          linarith [hx.2]
        exact lt_of_le_of_lt hxmh hbr
    exact ((hg.continuousOn).comp (continuousOn_id.add (continuousOn_const (c := h))) hmap).pow 2
  have hcont_plain : ContinuousOn (fun x : ℝ => (g x) ^ 2) (Icc a m) :=
    ((hg.continuousOn).mono hsub_am).pow 2
  have hintG : IntervalIntegrable (fun x : ℝ => (deriv g x) ^ 2) volume a m :=
    (hcd_am.pow 2).intervalIntegrable_of_Icc ham
  have hintA : IntervalIntegrable
      (fun x : ℝ => (4 / h ^ 2) * ((g (x + h)) ^ 2 + (g x) ^ 2)) volume a m :=
    ((hcont_shift.add hcont_plain).const_mul (4 / h ^ 2)).intervalIntegrable_of_Icc ham
  have hintB : IntervalIntegrable
      (fun x : ℝ => 2 * h * (∫ t in x..(x + h), (deriv (deriv g) t) ^ 2)) volume a m :=
    hFint.const_mul (2 * h)
  have hstep : ∫ x in a..m, (deriv g x) ^ 2
      ≤ ∫ x in a..m, ((4 / h ^ 2) * ((g (x + h)) ^ 2 + (g x) ^ 2)
          + 2 * h * (∫ t in x..(x + h), (deriv (deriv g) t) ^ 2)) :=
    integral_mono_on ham hintG (hintA.add hintB) hpt_fwd
  have hlin : ∫ x in a..m, ((4 / h ^ 2) * ((g (x + h)) ^ 2 + (g x) ^ 2)
        + 2 * h * (∫ t in x..(x + h), (deriv (deriv g) t) ^ 2))
      = (4 / h ^ 2) * ((∫ x in a..m, (g (x + h)) ^ 2) + (∫ x in a..m, (g x) ^ 2))
        + 2 * h * (∫ x in a..m, (∫ t in x..(x + h), (deriv (deriv g) t) ^ 2)) := by
    rw [intervalIntegral.integral_add hintA hintB, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hcont_shift.intervalIntegrable_of_Icc ham)
        (hcont_plain.intervalIntegrable_of_Icc ham),
      intervalIntegral.integral_const_mul]
  have hsh1 : ∫ x in a..m, (g (x + h)) ^ 2 = ∫ x in m..b, (g x) ^ 2 := by
    have hthis := intervalIntegral.integral_comp_add_right (a := a) (b := m)
      (fun y : ℝ => (g y) ^ 2) h
    rw [show a + h = m from hmdef.symm, show m + h = b from hmh] at hthis
    simpa using hthis
  have hleft : ∫ x in a..m, (deriv g x) ^ 2
      ≤ (4 / h ^ 2) * ((∫ x in m..b, (g x) ^ 2) + (∫ x in a..m, (g x) ^ 2))
        + 2 * h * (h * ∫ y in a..b, (deriv (deriv g) y) ^ 2) := by
    refine hstep.trans ?_
    rw [hlin]
    refine add_le_add ?_ ?_
    · rw [hsh1]
    · exact mul_le_mul_of_nonneg_left hFbd (by linarith)
  -- ### the right half `[m,b]`
  have hpt_bwd : ∀ x ∈ Set.Icc m b, (deriv g x) ^ 2
      ≤ (4 / h ^ 2) * ((g x) ^ 2 + (g (x - h)) ^ 2)
        + 2 * h * (∫ t in (x - h)..x, (deriv (deriv g) t) ^ 2) := by
    intro x hx
    have hxmh : a ≤ x - h := by
      have h1 : a + h ≤ x := by rw [← hmdef]; exact hx.1
      linarith
    exact pointwise_bwd_aux hh
      (fun y hy => ⟨lt_of_lt_of_le hpa (le_trans hxmh hy.1),
        lt_of_le_of_lt (le_trans hy.2 hx.2) hbr⟩) hg
  have hcd_mb : ContinuousOn (deriv g) (Icc m b) := hCd.mono hsub_mb
  have hcont_shift' : ContinuousOn (fun x : ℝ => (g (x - h)) ^ 2) (Icc m b) := by
    have hmap : MapsTo (fun x : ℝ => x - h) (Icc m b) (Ioo p r) := by
      intro x hx
      have h1 : a + h ≤ x := by rw [← hmdef]; exact hx.1
      exact ⟨by linarith, lt_of_le_of_lt (by linarith [hx.2]) hbr⟩
    exact ((hg.continuousOn).comp (continuousOn_id.sub (continuousOn_const (c := h))) hmap).pow 2
  have hcont_plain' : ContinuousOn (fun x : ℝ => (g x) ^ 2) (Icc m b) :=
    ((hg.continuousOn).mono hsub_mb).pow 2
  have hintG' : IntervalIntegrable (fun x : ℝ => (deriv g x) ^ 2) volume m b :=
    (hcd_mb.pow 2).intervalIntegrable_of_Icc hmb
  have hintA' : IntervalIntegrable
      (fun x : ℝ => (4 / h ^ 2) * ((g x) ^ 2 + (g (x - h)) ^ 2)) volume m b :=
    ((hcont_plain'.add hcont_shift').const_mul (4 / h ^ 2)).intervalIntegrable_of_Icc hmb
  have hintB' : IntervalIntegrable
      (fun x : ℝ => 2 * h * (∫ t in (x - h)..x, (deriv (deriv g) t) ^ 2)) volume m b :=
    hF'int.const_mul (2 * h)
  have hstep' : ∫ x in m..b, (deriv g x) ^ 2
      ≤ ∫ x in m..b, ((4 / h ^ 2) * ((g x) ^ 2 + (g (x - h)) ^ 2)
          + 2 * h * (∫ t in (x - h)..x, (deriv (deriv g) t) ^ 2)) :=
    integral_mono_on hmb hintG' (hintA'.add hintB') hpt_bwd
  have hlin' : ∫ x in m..b, ((4 / h ^ 2) * ((g x) ^ 2 + (g (x - h)) ^ 2)
        + 2 * h * (∫ t in (x - h)..x, (deriv (deriv g) t) ^ 2))
      = (4 / h ^ 2) * ((∫ x in m..b, (g x) ^ 2) + (∫ x in m..b, (g (x - h)) ^ 2))
        + 2 * h * (∫ x in m..b, (∫ t in (x - h)..x, (deriv (deriv g) t) ^ 2)) := by
    rw [intervalIntegral.integral_add hintA' hintB', intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hcont_plain'.intervalIntegrable_of_Icc hmb)
        (hcont_shift'.intervalIntegrable_of_Icc hmb),
      intervalIntegral.integral_const_mul]
  have hsh2 : ∫ x in m..b, (g (x - h)) ^ 2 = ∫ x in a..m, (g x) ^ 2 := by
    have hthis := intervalIntegral.integral_comp_add_right (a := m) (b := b)
      (fun y : ℝ => (g y) ^ 2) (-h)
    rw [show m + -h = a from by rw [hmdef]; ring,
      show b + -h = m from by rw [← hmh]; ring] at hthis
    simpa [sub_eq_add_neg] using hthis
  have hright : ∫ x in m..b, (deriv g x) ^ 2
      ≤ (4 / h ^ 2) * ((∫ x in m..b, (g x) ^ 2) + (∫ x in a..m, (g x) ^ 2))
        + 2 * h * (h * ∫ y in a..b, (deriv (deriv g) y) ^ 2) := by
    refine hstep'.trans ?_
    rw [hlin']
    refine add_le_add ?_ ?_
    · rw [hsh2]
    · exact mul_le_mul_of_nonneg_left hF'bd (by linarith)
  -- ### assembly
  set D : ℝ := ∫ y in a..b, (deriv (deriv g) y) ^ 2 with hDdef
  have hsm : ∫ x in a..b, (deriv g x) ^ 2
      = (∫ x in a..m, (deriv g x) ^ 2) + ∫ x in m..b, (deriv g x) ^ 2 :=
    (intervalIntegral.integral_add_adjacent_intervals
      ((hcd_am.pow 2).intervalIntegrable_of_Icc ham)
      ((hcd_mb.pow 2).intervalIntegrable_of_Icc hmb)).symm
  have hgb'' : ∫ x in a..b, (g x) ^ 2
      = (∫ x in m..b, (g x) ^ 2) + (∫ x in a..m, (g x) ^ 2) := by
    have hsplit : ∫ x in a..b, (g x) ^ 2
        = (∫ x in a..m, (g x) ^ 2) + ∫ x in m..b, (g x) ^ 2 :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hcont_plain.intervalIntegrable_of_Icc ham)
        (hcont_plain'.intervalIntegrable_of_Icc hmb)).symm
    rw [hsplit]; ring
  have htotal : ∫ x in a..b, (deriv g x) ^ 2
      ≤ (8 / h ^ 2) * (∫ x in a..b, (g x) ^ 2) + 4 * h ^ 2 * D := by
    rw [hsm, hgb'']
    have hsum : (∫ x in a..m, (deriv g x) ^ 2) + (∫ x in m..b, (deriv g x) ^ 2)
        ≤ ((4 / h ^ 2) * ((∫ x in m..b, (g x) ^ 2) + (∫ x in a..m, (g x) ^ 2))
            + 2 * h * (h * D))
          + ((4 / h ^ 2) * ((∫ x in m..b, (g x) ^ 2) + (∫ x in a..m, (g x) ^ 2))
            + 2 * h * (h * D)) := by
      linarith [hleft, hright]
    have key : ((4 / h ^ 2) * ((∫ x in m..b, (g x) ^ 2) + (∫ x in a..m, (g x) ^ 2))
            + 2 * h * (h * D))
          + ((4 / h ^ 2) * ((∫ x in m..b, (g x) ^ 2) + (∫ x in a..m, (g x) ^ 2))
            + 2 * h * (h * D))
        = (8 / h ^ 2) * ((∫ x in m..b, (g x) ^ 2) + (∫ x in a..m, (g x) ^ 2))
          + 4 * h ^ 2 * D := by
      ring
    linarith [hsum, key]
  -- ### final arithmetic
  have h32 : 8 / h ^ 2 = 32 / (b - a) ^ 2 := by
    have hb2 : h ^ 2 = (b - a) ^ 2 / 4 := by rw [hhdef]; ring
    rw [hb2]
    have hne : (b - a) ^ 2 ≠ 0 := by
      have : b - a ≠ 0 := by linarith
      positivity
    field_simp
    ring
  have h4h : 4 * h ^ 2 = (b - a) ^ 2 := by
    rw [hhdef]
    ring
  have hS : 0 ≤ ∫ y in a..b, (g y) ^ 2 := integral_nonneg hab' (fun y _ => sq_nonneg _)
  have hle : 32 / (b - a) ^ 2 ≤ 64 / (b - a) ^ 2 :=
    div_le_div_of_nonneg_right (by norm_num) (by positivity)
  calc ∫ y in a..b, (deriv g y) ^ 2
      ≤ (8 / h ^ 2) * (∫ y in a..b, (g y) ^ 2) + 4 * h ^ 2 * D := htotal
    _ = (32 / (b - a) ^ 2) * (∫ y in a..b, (g y) ^ 2) + 4 * h ^ 2 * D := by rw [h32]
    _ ≤ (64 / (b - a) ^ 2) * (∫ y in a..b, (g y) ^ 2) + (b - a) ^ 2 * D := by
        rw [h4h]
        exact add_le_add (mul_le_mul_of_nonneg_right hle hS) le_rfl

end Work.FTS.EllipticEst.Mine.Support
