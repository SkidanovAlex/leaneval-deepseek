import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Commons.Analysis.ExpLog.atanh_series_log_lower

namespace Commons.Analysis.Integral

open scoped Real

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Numerical bounds for logarithms -/

/-- `log (1+z) ≥ 2z/(2+z)` for `z > 0`, from the artanh power series. -/
theorem log_one_add_ge (z : ℝ) (hz : 0 < z) : 2*z/(2+z) ≤ Real.log (1+z) := by
  have hden : (0:ℝ) < 2 + z := by linarith
  have hr0 : 0 < z/(2+z) := div_pos hz hden
  have hr1 : z/(2+z) < 1 := by rw [div_lt_one hden]; linarith
  have h := Commons.Analysis.ExpLog.atanh_series_log_lower hr0 hr1 0
  have hsum : (Finset.sum (Finset.range (0 + 1))
      (fun k => (z/(2+z)) ^ (2 * k + 1) / (2 * k + 1 : ℝ))) = z/(2+z) := by
    simp
  rw [hsum] at h
  have harg : (1 + z/(2+z))/(1 - z/(2+z)) = 1 + z := by field_simp; ring
  rw [harg] at h
  calc 2*z/(2+z) = 2*(z/(2+z)) := by ring
    _ ≤ Real.log (1+z) := h

theorem log_257_16_lower : (2.77648 : ℝ) ≤ Real.log (257/16) := by
  have hlog2 : (4:ℝ) * 0.6931471803 ≤ 4 * Real.log 2 :=
    mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (by norm_num)
  have h16 : Real.log (16:ℝ) = 4 * Real.log 2 := by
    rw [show (16:ℝ) = 2^4 by norm_num, Real.log_pow]; norm_num
  have hsplit : Real.log (257/16) = Real.log 16 + Real.log (257/256) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have hb := log_one_add_ge (1/256) (by norm_num)
  rw [show (2*(1/256)/(2+1/256) : ℝ) = 2/513 by norm_num] at hb
  rw [show (1 + 1/256 : ℝ) = 257/256 by norm_num] at hb
  rw [hsplit, h16]
  linarith

theorem log_1435_294_lower : (1.5853 : ℝ) ≤ Real.log (1435/294) := by
  have hr0 : (0:ℝ) < 259/2611 := by norm_num
  have hr1 : (259/2611 : ℝ) < 1 := by norm_num
  have h := Commons.Analysis.ExpLog.atanh_series_log_lower hr0 hr1 1
  have hsum : (Finset.sum (Finset.range (1+1))
      (fun k => (259/2611:ℝ) ^ (2*k+1)/(2*k+1))) = (259/2611 + (259/2611)^3/3) := by
    norm_num [Finset.sum_range_succ]
  rw [hsum] at h
  have harg : (1 + (259/2611:ℝ))/(1 - 259/2611) = 1435/1176 := by norm_num
  rw [harg] at h
  have hsplit : Real.log (1435/294) = Real.log 4 + Real.log (1435/1176) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h4 : Real.log (4:ℝ) = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  have hlog2 : 2 * (0.6931471803:ℝ) ≤ 2 * Real.log 2 :=
    mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (by norm_num)
  rw [hsplit, h4]
  linarith

/-! ## The auxiliary function `gfun` -/

private def gfun (w : ℝ) : ℝ := w * (2 * Real.log ((1 + w^2)/w) - (3 - w^2)/(1 + w^2))
private def Rfun (w : ℝ) : ℝ := 2 * Real.log ((1 + w^2)/w) + (3*w^4 + 6*w^2 - 5)/(1 + w^2)^2
private def Rsfun (w : ℝ) : ℝ := 4*w/(1 + w^2) - 2/w + 32*w/(1 + w^2)^3

private lemma hd_one_add_sq (w : ℝ) : HasDerivAt (fun t : ℝ => 1 + t^2) (2*w) w := by
  have h := ((hasDerivAt_id w).pow 2).const_add 1
  refine h.congr_deriv ?_
  simp only [Nat.reduceSub, pow_one, id_eq, mul_one]
  ring

private lemma hd_three_sub_sq (w : ℝ) : HasDerivAt (fun t : ℝ => 3 - t^2) (-(2*w)) w := by
  have h := ((hasDerivAt_id w).pow 2).const_sub 3
  refine h.congr_deriv ?_
  simp only [Nat.reduceSub, pow_one, id_eq, mul_one]
  ring

private lemma hasDerivAt_log_ratio (w : ℝ) (hw : 0 < w) :
    HasDerivAt (fun t : ℝ => Real.log ((1 + t^2)/t)) ((w^2-1)/(w*(1+w^2))) w := by
  have h1 : HasDerivAt (fun t : ℝ => (1 + t^2)/t) (((2*w)*w - (1+w^2)*1)/w^2) w :=
    (hd_one_add_sq w).div (hasDerivAt_id w) (by positivity)
  have h2 := h1.log (by positivity : (1 + w^2)/w ≠ 0)
  refine h2.congr_deriv ?_
  field_simp
  ring

private lemma hasDerivAt_two_log_ratio (w : ℝ) (hw : 0 < w) :
    HasDerivAt (fun t : ℝ => 2 * Real.log ((1 + t^2)/t)) (2 * ((w^2-1)/(w*(1+w^2)))) w :=
  (hasDerivAt_log_ratio w hw).const_mul 2

private lemma hasDerivAt_Q (w : ℝ) (hw : 0 < w) :
    HasDerivAt (fun t : ℝ => (3 - t^2)/(1+t^2)) (-8*w/(1+w^2)^2) w := by
  have h := (hd_three_sub_sq w).div (hd_one_add_sq w) (by positivity)
  refine h.congr_deriv ?_
  field_simp
  ring

private lemma hasDerivAt_gfun (w : ℝ) (hw : 0 < w) : HasDerivAt gfun (Rfun w) w := by
  have h := (hasDerivAt_id w).mul ((hasDerivAt_two_log_ratio w hw).sub (hasDerivAt_Q w hw))
  refine h.congr_deriv ?_
  rw [Rfun]
  simp only [Pi.sub_apply, id_eq, one_mul]
  field_simp
  ring

private lemma hd_cubic_frac (w : ℝ) (hw : 0 < w) :
    HasDerivAt (fun t : ℝ => (3*t^4+6*t^2-5)/(1+t^2)^2) (32*w/(1+w^2)^3) w := by
  have hn : HasDerivAt (fun t : ℝ => 3*t^4+6*t^2-5) (12*w^3+12*w) w := by
    have h := ((((hasDerivAt_id w).pow 4).const_mul 3).add
      (((hasDerivAt_id w).pow 2).const_mul 6)).sub_const 5
    refine h.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one, id_eq, mul_one]
    ring
  have hd : HasDerivAt (fun t : ℝ => (1+t^2)^2) (2*(1+w^2)*(2*w)) w := by
    have h := (hd_one_add_sq w).pow 2
    refine h.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one, id_eq, mul_one]
    ring
  have h := hn.div hd (by positivity)
  refine h.congr_deriv ?_
  field_simp
  ring

private lemma hasDerivAt_Rfun (w : ℝ) (hw : 0 < w) : HasDerivAt Rfun (Rsfun w) w := by
  have h := ((hasDerivAt_two_log_ratio w hw)).add (hd_cubic_frac w hw)
  refine h.congr_deriv ?_
  rw [Rsfun]
  field_simp
  ring

private lemma Rsfun_neg (w : ℝ) (hw1 : 1/16 ≤ w) (hw2 : w ≤ 3/14) : Rsfun w ≤ 0 := by
  have hwpos : 0 < w := by linarith
  have hkey : Rsfun w = (2*w^6+2*w^4+30*w^2-2)/(w*(1+w^2)^3) := by
    rw [Rsfun]; field_simp; ring
  rw [hkey]
  have hden : 0 < w*(1+w^2)^3 := by positivity
  have h2 : w^2 ≤ 9/196 := by nlinarith
  have h4 : w^4 ≤ (9/196)^2 := by nlinarith [h2, sq_nonneg w]
  have h6 : w^6 ≤ (9/196)^3 := by nlinarith [h2, h4, sq_nonneg (w^3)]
  have hnum : 2*w^6+2*w^4+30*w^2-2 ≤ 0 := by nlinarith [h2, h4, h6]
  exact div_nonpos_of_nonpos_of_nonneg hnum (le_of_lt hden)

private lemma gfun_concave : ConcaveOn ℝ (Set.Icc (1/16) (3/14)) gfun := by
  have hD : Convex ℝ (Set.Icc (1/16:ℝ) (3/14)) := convex_Icc _ _
  refine concaveOn_of_hasDerivWithinAt2_nonpos hD (f := gfun) (f' := Rfun) (f'' := Rsfun) ?_ ?_ ?_ ?_
  · have hdiff : DifferentiableOn ℝ gfun (Set.Icc (1/16:ℝ) (3/14)) := by
      intro x hx
      exact ((hasDerivAt_gfun x (by linarith [hx.1])).differentiableAt).differentiableWithinAt
    exact hdiff.continuousOn
  · intro x hx
    exact (hasDerivAt_gfun x (by have := interior_subset hx; linarith [this.1])).hasDerivWithinAt
  · intro x hx
    exact (hasDerivAt_Rfun x (by have := interior_subset hx; linarith [this.1])).hasDerivWithinAt
  · intro x hx
    have hx' := interior_subset hx
    exact Rsfun_neg x hx'.1 hx'.2

private lemma gfun_lower (w : ℝ) (hw1 : 1/16 ≤ w) (hw2 : w ≤ 3/14) : (0.0736:ℝ) ≤ gfun w := by
  have hmin := gfun_concave.min_le_of_mem_Icc (x := (1/16:ℝ)) (y := (3/14:ℝ)) (z := w)
    (by norm_num) (by norm_num) ⟨hw1, hw2⟩
  have h1 : (0.0736:ℝ) ≤ gfun (1/16) := by
    have hlog : (2.77648:ℝ) ≤ Real.log (257/16) := log_257_16_lower
    have hval : gfun (1/16) = (1/16)*(2*Real.log (257/16) - 767/257) := by
      rw [gfun]
      have e1 : (1 + (1/16:ℝ)^2)/(1/16) = 257/16 := by norm_num
      have e2 : (3 - (1/16:ℝ)^2)/(1+(1/16)^2) = 767/257 := by norm_num
      rw [e1, e2]
    rw [hval]; nlinarith [hlog]
  have h2 : (0.0736:ℝ) ≤ gfun (3/14) := by
    have hlog : (1.5853:ℝ) ≤ Real.log (1435/294) := log_1435_294_lower
    have hval : gfun (3/14) = (3/14)*(2*Real.log (1435/294) - 579/205) := by
      rw [gfun]
      have e1 : (1 + (3/14:ℝ)^2)/(3/14) = 1435/294 := by norm_num
      have e2 : (3 - (3/14:ℝ)^2)/(1+(3/14)^2) = 579/205 := by norm_num
      rw [e1, e2]
    rw [hval]; nlinarith [hlog]
  exact le_trans (le_min h1 h2) hmin

/-- Explicit lower bound for `w * (2 log((1+w²)/w) - (3-w²)/(1+w²))` on `[1/16, 3/14]`. -/
theorem w_mul_beta_lower (w : ℝ) (hw1 : 1/16 ≤ w) (hw2 : w ≤ 3/14) :
    (0.0736:ℝ) ≤ w * (2 * Real.log ((1 + w^2)/w) - (3 - w^2)/(1 + w^2)) := by
  have h := gfun_lower w hw1 hw2
  rwa [gfun] at h

/-! ## The lower bound for the integrand -/

/-- Pointwise lower bound `0.0184` for the derivative integrand. -/
theorem phi_lower (x A : ℝ) (hx1 : 1/4 ≤ x) (hx2 : x ≤ 3/4) (hA1 : 7/2 ≤ A) (hA2 : A ≤ 4) :
    (0.0184:ℝ) ≤ (x/A^2)*(2*Real.log ((A^2+x^2)/(A*x)) - (3*A^2-x^2)/(A^2+x^2)) := by
  have hApos : 0 < A := by linarith
  have hxpos : 0 < x := by linarith
  set w : ℝ := x/A with hw
  have hw1 : 1/16 ≤ w := by
    rw [hw]; rw [le_div_iff₀ hApos]; nlinarith
  have hw2 : w ≤ 3/14 := by
    rw [hw]; rw [div_le_iff₀ hApos]; nlinarith
  have hgl := w_mul_beta_lower w hw1 hw2
  have hxw : x = w * A := by rw [hw]; field_simp
  have hkey : (x/A^2)*(2*Real.log ((A^2+x^2)/(A*x)) - (3*A^2-x^2)/(A^2+x^2))
      = w*(2*Real.log ((1+w^2)/w) - (3-w^2)/(1+w^2))/A := by
    rw [hxw]
    have ha1 : (A^2 + (w*A)^2)/(A*(w*A)) = (1+w^2)/w := by field_simp <;> ring
    have ha2 : (3*A^2 - (w*A)^2)/(A^2 + (w*A)^2) = (3-w^2)/(1+w^2) := by field_simp <;> ring
    rw [ha1, ha2]
    field_simp <;> ring
  rw [hkey]
  calc (0.0184:ℝ) ≤ 0.0736/A := by rw [le_div_iff₀ hApos]; nlinarith
    _ ≤ w*(2*Real.log ((1+w^2)/w) - (3-w^2)/(1+w^2))/A :=
        div_le_div_of_nonneg_right hgl (le_of_lt hApos)

/-! ## The auxiliary function `psi` and its derivative -/

private def psi (A x : ℝ) : ℝ := (1 - x^2/A^2)*Real.log ((A^2+x^2)/(A*x)) + Real.log x

private def phif (A x : ℝ) : ℝ := (x/A^2)*(2*Real.log ((A^2+x^2)/(A*x)) - (3*A^2-x^2)/(A^2+x^2))

private lemma hd_add_sq_const (A x : ℝ) : HasDerivAt (fun y : ℝ => A^2 + y^2) (2*x) x := by
  have h := ((hasDerivAt_id x).pow 2).const_add (A^2)
  refine h.congr_deriv ?_
  simp only [Nat.reduceSub, pow_one, id_eq, mul_one]
  ring

private lemma hd_mul_const (A x : ℝ) : HasDerivAt (fun y : ℝ => A*y) A x := by
  have h := (hasDerivAt_id x).const_mul A
  refine h.congr_deriv ?_
  ring

private lemma hasDerivAt_G (A : ℝ) (hA : 0 < A) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => Real.log ((A^2+y^2)/(A*y))) ((2*x)/(A^2+x^2) - 1/x) x := by
  have h := (hd_add_sq_const A x).div (hd_mul_const A x) (by positivity)
  have h2 := h.log (by positivity : (A^2+x^2)/(A*x) ≠ 0)
  refine h2.congr_deriv ?_
  simp only [Pi.div_apply]
  field_simp <;> ring

private lemma hasDerivAt_c (A : ℝ) (hA : 0 < A) (x : ℝ) :
    HasDerivAt (fun y : ℝ => 1 - y^2/A^2) (-2*x/A^2) x := by
  have h1 : HasDerivAt (fun y : ℝ => y^2/A^2) (2*x/A^2) x := by
    have h := ((hasDerivAt_id x).pow 2).div_const (A^2)
    refine h.congr_deriv ?_
    simp only [Nat.reduceSub, pow_one, id_eq, mul_one]
    ring
  have h := (hasDerivAt_const (x:=x) (c:=(1:ℝ))).sub h1
  refine h.congr_deriv ?_
  ring

private lemma hasDerivAt_psi (A : ℝ) (hA : 0 < A) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => psi A y) (-(phif A x)) x := by
  have h := ((hasDerivAt_c A hA x).mul (hasDerivAt_G A hA x hx)).add
    (Real.hasDerivAt_log (ne_of_gt hx))
  refine h.congr_deriv ?_
  rw [phif]
  field_simp
  ring

/-! ## Bound for the explicit polynomial RHS -/

private lemma rhs_bound (s : ℝ) (hs1 : 1/4 ≤ s) (hs2 : s ≤ 1/2) :
    (1/8)*((0.97297359015:ℝ)*((1-s)^2-s^2) - ((2:ℝ)/3)*((1-s)^3-s^3)) - (1-2*s)/((49:ℝ)/2)
    ≤ (0.0184:ℝ)*(1-2*s) := by
  have hd : 0 ≤ 1 - 2*s := by linarith
  have hq : (3:ℝ)/4 ≤ 1 - s + s^2 := by nlinarith [sq_nonneg (s - 1/2)]
  have hgoal : (1/8)*((0.97297359015:ℝ)*((1-s)^2-s^2) - ((2:ℝ)/3)*((1-s)^3-s^3))
      - (1-2*s)/((49:ℝ)/2)
      = (1-2*s)*(((0.97297359015:ℝ) - (2/3)*(1-s+s^2))/8 - 2/49) := by
    ring
  rw [hgoal]
  have hb : ((0.97297359015:ℝ) - (2/3)*(1-s+s^2))/8 - 2/49 ≤ (0.0184:ℝ) := by
    nlinarith [hq]
  calc (1-2*s)*(((0.97297359015:ℝ) - (2/3)*(1-s+s^2))/8 - 2/49)
      ≤ (1-2*s)*(0.0184:ℝ) := mul_le_mul_of_nonneg_left hb hd
    _ = (0.0184:ℝ)*(1-2*s) := by ring

/-! ## The main estimate, parametrised by `A` -/

private theorem main_general (s A : ℝ) (hs1 : 1/4 ≤ s) (hs2 : s ≤ 1/2)
    (hA1 : 7/2 ≤ A) (hA2 : A ≤ 4) :
    Real.log ((A^2+s^2)/(A*s))*(1-s^2/A^2)
      - Real.log ((A^2+(1-s)^2)/(A*(1-s)))*(1-(1-s)^2/A^2) + Real.log (s/(1-s))
    ≥ (1/8)*((0.97297359015:ℝ)*((1-s)^2-s^2) - ((2:ℝ)/3)*((1-s)^3-s^3))
      - (1-2*s)/((49:ℝ)/2) := by
  have hApos : 0 < A := by linarith
  have hs_pos : 0 < s := by linarith
  have hv_pos : 0 < 1 - s := by linarith
  rcases lt_or_eq_of_le hs2 with hlt | heq
  · have hsv : s < 1 - s := by linarith
    have hcont : ContinuousOn (fun y : ℝ => psi A y) (Set.Icc s (1-s)) := by
      have hdiff : DifferentiableOn ℝ (fun y : ℝ => psi A y) (Set.Icc s (1-s)) := by
        intro y hy
        exact ((hasDerivAt_psi A hApos y (by linarith [hy.1])).differentiableAt).differentiableWithinAt
      exact hdiff.continuousOn
    have hdiff : DifferentiableOn ℝ (fun y : ℝ => psi A y) (Set.Ioo s (1-s)) := by
      intro y hy
      exact ((hasDerivAt_psi A hApos y (by linarith [hy.1])).differentiableAt).differentiableWithinAt
    obtain ⟨ξ, hξmem, hξeq⟩ := exists_deriv_eq_slope (fun y : ℝ => psi A y) hsv hcont hdiff
    have hξpos : 0 < ξ := by linarith [hξmem.1]
    have hderivξ : deriv (fun y : ℝ => psi A y) ξ = -(phif A ξ) :=
      (hasDerivAt_psi A hApos ξ hξpos).deriv
    have hξ1 : 1/4 ≤ ξ := by linarith [hξmem.1]
    have hξ2 : ξ ≤ 3/4 := by linarith [hξmem.2]
    have hphilb : (0.0184:ℝ) ≤ phif A ξ := by
      have h := phi_lower ξ A hξ1 hξ2 hA1 hA2
      simpa only [phif] using h
    have hne : (1-s) - s ≠ 0 := by linarith
    have hval : psi A s - psi A (1-s) = (1-2*s)*(phif A ξ) := by
      have h1 : deriv (fun y : ℝ => psi A y) ξ * ((1-s) - s) = (psi A (1-s) - psi A s) := by
        rw [hξeq, div_mul_cancel₀ _ hne]
      rw [hderivξ] at h1
      have h2 : (1:ℝ) - s - s = 1 - 2*s := by ring
      rw [h2] at h1
      linarith
    have hT : Real.log ((A^2+s^2)/(A*s))*(1-s^2/A^2)
          - Real.log ((A^2+(1-s)^2)/(A*(1-s)))*(1-(1-s)^2/A^2) + Real.log (s/(1-s))
        = psi A s - psi A (1-s) := by
      simp only [psi]
      rw [Real.log_div (ne_of_gt hs_pos) (ne_of_gt hv_pos)]
      ring
    rw [hT, hval]
    have hd : 0 ≤ 1 - 2*s := by linarith
    have hfirst : (1-2*s)*(0.0184:ℝ) ≤ (1-2*s)*(phif A ξ) :=
      mul_le_mul_of_nonneg_left hphilb hd
    have hrhs := rhs_bound s hs1 hs2
    linarith
  · subst heq
    have e1 : (1:ℝ) - 1/2 = 1/2 := by norm_num
    rw [e1]
    have hlog : Real.log ((1:ℝ)/2/(1/2)) = 0 := by
      rw [show ((1:ℝ)/2/(1/2)) = 1 by norm_num, Real.log_one]
    rw [hlog]
    norm_num

/-! ## The target theorem -/

/-- The `L1`-correction `T` dominates the explicit polynomial lower bound `Tlb` on
`1/4 ≤ s ≤ 1/2`, `0 < β ≤ 1/4`. -/
theorem T_lower_Tlb :
  ∀ s β : ℝ, 1/4 ≤ s → s ≤ 1/2 → 0 < β → β ≤ 1/4 →
    Real.log ((4*(2-β)^2+s^2)/(2*(2-β)*s))*(1-s^2/(4*(2-β)^2))
    - Real.log ((4*(2-β)^2+(1-s)^2)/(2*(2-β)*(1-s)))*(1-(1-s)^2/(4*(2-β)^2))
    + Real.log (s/(1-s))
    ≥ (1/8)*((0.97297359015:ℝ)*((1-s)^2-s^2) - ((2:ℝ)/3)*((1-s)^3-s^3)) - (1-2*s)/((49:ℝ)/2) := by
  intro s β hs1 hs2 hβ1 hβ2
  have hA1 : (7:ℝ)/2 ≤ 2*(2-β) := by nlinarith
  have hA2 : 2*(2-β) ≤ 4 := by nlinarith
  have hgen := main_general s (2*(2-β)) hs1 hs2 hA1 hA2
  rw [show (4:ℝ)*(2-β)^2 = (2*(2-β))^2 by ring,
      show (2:ℝ)*(2-β)*s = (2*(2-β))*s by ring,
      show (2:ℝ)*(2-β)*(1-s) = (2*(2-β))*(1-s) by ring]
  exact hgen

end

end Commons.Analysis.Integral