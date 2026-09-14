import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace Commons.Analysis.Integral

open MeasureTheory Real Set Filter
open scoped Topology

/-- The integrand of the target inequality. -/
private noncomputable def u (x : ℝ) : ℝ :=
  ((Real.sqrt (x^2 - 1))⁻¹ - x⁻¹) * Real.sqrt x

/-- The substitution parameter: `cosh T = √2`. -/
private noncomputable def T : ℝ := Real.arcosh (Real.sqrt 2)

/-- The integrand after the change of variables `x = cosh t`. -/
private noncomputable def g (x : ℝ) : ℝ := Real.exp (-x) / Real.sqrt (Real.cosh x)

/-- The dominating function on the tail. -/
private noncomputable def bnd (x : ℝ) : ℝ :=
  Real.sqrt 2 * Real.exp (-(3/2)*x) - (Real.sqrt 2/3) * Real.exp (-(7/2)*x)

/-- `s = e^{-T/2}`, so that `s^2 = √2 - 1`. -/
private noncomputable def s : ℝ := Real.exp (-(T/2))

private lemma sqrt_two_gt_one : (1:ℝ) < Real.sqrt 2 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)

private lemma T_nonneg : 0 ≤ T := by
  simp only [T]; exact Real.arcosh_nonneg (le_of_lt sqrt_two_gt_one)

private lemma T_pos : 0 < T := by
  simp only [T]; exact Real.arcosh_pos sqrt_two_gt_one

private lemma cosh_T : Real.cosh T = Real.sqrt 2 := by
  simp only [T]; exact Real.cosh_arcosh (le_of_lt sqrt_two_gt_one)

private lemma tendsto_cosh_atTop : Tendsto Real.cosh atTop atTop := by
  have h1 : Tendsto (fun x : ℝ => Real.exp x) atTop atTop := Real.tendsto_exp_atTop
  have h2 : Tendsto (fun x : ℝ => Real.exp (-x)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have h3 : Tendsto (fun x : ℝ => Real.exp x + Real.exp (-x)) atTop atTop :=
    h1.atTop_add h2
  have h4 : Tendsto (fun x : ℝ => (1/2:ℝ) * (Real.exp x + Real.exp (-x))) atTop atTop :=
    h3.const_mul_atTop (by norm_num)
  have h5 : (fun x : ℝ => (1/2:ℝ) * (Real.exp x + Real.exp (-x))) = Real.cosh := by
    funext x; rw [Real.cosh_eq]; ring
  rwa [h5] at h4

/-- `√a * b / a = b / √a` for `a > 0`. -/
private lemma sqrt_mul_div {a b : ℝ} (_ha : 0 < a) :
    Real.sqrt a * b / a = b / Real.sqrt a := by
  rw [mul_comm (Real.sqrt a) b, mul_div_assoc, Real.sqrt_div_self, div_eq_mul_inv]

/-- Pointwise identity of the change of variables `x = cosh t`. -/
private lemma key_pointwise {x : ℝ} (hx : 0 < x) :
    Real.sinh x * u (Real.cosh x) = g x := by
  show Real.sinh x * u (Real.cosh x) = Real.exp (-x) / Real.sqrt (Real.cosh x)
  have hsinh_pos : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have hcosh_pos : 0 < Real.cosh x := Real.cosh_pos x
  have hsq : Real.cosh x ^ 2 - 1 = Real.sinh x ^ 2 := by
    have := Real.cosh_sq_sub_sinh_sq x; linarith
  have hsqrt : Real.sqrt (Real.cosh x ^ 2 - 1) = Real.sinh x := by
    rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg hsinh_pos.le]
  have hF : u (Real.cosh x)
      = ((Real.sinh x)⁻¹ - (Real.cosh x)⁻¹) * Real.sqrt (Real.cosh x) := by
    unfold u
    rw [hsqrt]
  calc Real.sinh x * u (Real.cosh x)
      = Real.sinh x * (((Real.sinh x)⁻¹ - (Real.cosh x)⁻¹) * Real.sqrt (Real.cosh x)) := by
        rw [hF]
    _ = (Real.sinh x * (Real.sinh x)⁻¹ - Real.sinh x * (Real.cosh x)⁻¹)
          * Real.sqrt (Real.cosh x) := by ring
    _ = (1 - Real.sinh x / Real.cosh x) * Real.sqrt (Real.cosh x) := by
        rw [mul_inv_cancel₀ (ne_of_gt hsinh_pos), div_eq_mul_inv]
    _ = ((Real.cosh x - Real.sinh x) / Real.cosh x) * Real.sqrt (Real.cosh x) := by
        congr 1
        rw [sub_div, div_self (ne_of_gt hcosh_pos)]
    _ = (Real.exp (-x) / Real.cosh x) * Real.sqrt (Real.cosh x) := by
        rw [Real.cosh_sub_sinh]
    _ = Real.exp (-x) / Real.sqrt (Real.cosh x) := by
        rw [div_mul_eq_mul_div, mul_comm (Real.exp (-x)) (Real.sqrt (Real.cosh x)),
          sqrt_mul_div hcosh_pos]

/-- Change of variables `x = cosh t`. -/
private lemma integral_subst :
    ∫ x in Set.Ioi (Real.sqrt 2), u x = ∫ x in Set.Ioi T, g x := by
  have hstrIci : StrictMonoOn Real.cosh (Set.Ici T) :=
    Real.cosh_strictMonoOn.mono (fun x hx => le_trans T_nonneg hx)
  have hmonoIoi : MonotoneOn Real.cosh (Set.Ioi T) :=
    (Real.cosh_strictMonoOn.mono (fun x hx => le_trans T_nonneg (le_of_lt hx))).monotoneOn
  have himg : Real.cosh '' Set.Ioi T = Set.Ioi (Real.sqrt 2) := by
    have h := ContinuousOn.image_Ioi_of_strictMonoOn (f := Real.cosh) (a := T)
      Real.continuous_cosh.continuousOn hstrIci tendsto_cosh_atTop
    rwa [cosh_T] at h
  have hsub := integral_image_eq_integral_deriv_smul_of_monotoneOn
      (f := Real.cosh) (f' := Real.sinh) (g := u) (s := Set.Ioi T)
      measurableSet_Ioi
      (fun x _ => (Real.hasDerivAt_cosh x).hasDerivWithinAt)
      hmonoIoi
  rw [himg] at hsub
  rw [hsub]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  show Real.sinh x • u (Real.cosh x) = g x
  exact key_pointwise (lt_trans T_pos hx)

/-! ## Numerical facts about `T` -/

private lemma exp_T : Real.exp T = Real.sqrt 2 + 1 := by
  have hsinh : Real.sinh T = 1 := by
    have h := Real.cosh_sq_sub_sinh_sq T
    rw [cosh_T] at h
    have h2 : Real.sinh T ^ 2 = 1 := by
      nlinarith [h, Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
    have hnn : 0 ≤ Real.sinh T := le_of_lt (Real.sinh_pos_iff.mpr T_pos)
    have h2' : Real.sinh T ^ 2 = (1:ℝ)^2 := by rw [h2]; norm_num
    exact (sq_eq_sq₀ hnn (by norm_num)).mp h2'
  have h := Real.cosh_add_sinh T
  rw [cosh_T, hsinh] at h
  linarith

private lemma hmul_sqrt : (Real.sqrt 2 + 1) * (Real.sqrt 2 - 1) = 1 := by
  have h := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  nlinarith [h]

private lemma exp_neg_T : Real.exp (-T) = Real.sqrt 2 - 1 := by
  rw [Real.exp_neg, exp_T]
  exact inv_eq_of_mul_eq_one_right hmul_sqrt

private lemma s_sq : s^2 = Real.sqrt 2 - 1 := by
  have h1 : s^2 = Real.exp (-T) := by
    show Real.exp (-(T/2))^2 = Real.exp (-T)
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [h1, exp_neg_T]

private lemma exp_neg_two_T : Real.exp (-2*T) = 3 - 2*Real.sqrt 2 := by
  have h1 : Real.exp (-2*T) = (Real.exp (-T))^2 := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  rw [h1, exp_neg_T]
  have h := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  nlinarith [h]

/-! ## The pointwise bound `g t ≤ bnd t` -/

private lemma g_nonneg (t : ℝ) : 0 ≤ g t := by
  show 0 ≤ Real.exp (-t) / Real.sqrt (Real.cosh t)
  exact div_nonneg (Real.exp_pos _).le (Real.sqrt_pos.mpr (Real.cosh_pos t)).le

/-- Cross-multiplied form of `g t = √2 e^{-3t/2}/√(1+e^{-2t})`. -/
private lemma g_cross (t : ℝ) :
    Real.exp (-t) * Real.sqrt (1 + Real.exp (-2*t))
      = Real.sqrt 2 * Real.exp (-(3/2)*t) * Real.sqrt (Real.cosh t) := by
  have hL : 0 ≤ Real.exp (-t) * Real.sqrt (1 + Real.exp (-2*t)) := by positivity
  have hR : 0 ≤ Real.sqrt 2 * Real.exp (-(3/2)*t) * Real.sqrt (Real.cosh t) := by positivity
  refine (sq_eq_sq₀ hL hR).mp ?_
  have e1 : Real.exp (-t)^2 = Real.exp (-2*t) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (-(3/2)*t)^2 = Real.exp (-3*t) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hL2 : (Real.exp (-t) * Real.sqrt (1 + Real.exp (-2*t)))^2
      = Real.exp (-2*t) * (1 + Real.exp (-2*t)) := by
    rw [mul_pow, e1, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 1 + Real.exp (-2*t))]
  have hR2 : (Real.sqrt 2 * Real.exp (-(3/2)*t) * Real.sqrt (Real.cosh t))^2
      = 2 * Real.exp (-3*t) * Real.cosh t := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), e2,
        Real.sq_sqrt (Real.cosh_pos t).le]
  rw [hL2, hR2, Real.cosh_eq]
  have f1 : Real.exp (-3*t) * Real.exp t = Real.exp (-2*t) := by
    rw [← Real.exp_add]; congr 1; ring
  have f2 : Real.exp (-3*t) * Real.exp (-t) = Real.exp (-4*t) := by
    rw [← Real.exp_add]; congr 1; ring
  have f3 : Real.exp (-2*t) * Real.exp (-2*t) = Real.exp (-4*t) := by
    rw [← Real.exp_add]; congr 1; ring
  have hRHS : (2:ℝ) * Real.exp (-3*t) * ((Real.exp t + Real.exp (-t))/2)
      = Real.exp (-2*t) + Real.exp (-4*t) := by
    rw [show (2:ℝ) * Real.exp (-3*t) * ((Real.exp t + Real.exp (-t))/2)
        = Real.exp (-3*t) * (Real.exp t + Real.exp (-t)) by ring]
    rw [mul_add, f1, f2]
  have hLHS : Real.exp (-2*t) * (1 + Real.exp (-2*t))
      = Real.exp (-2*t) + Real.exp (-4*t) := by
    rw [mul_add, mul_one, f3]
  rw [hLHS, hRHS]

private lemma g_eq (t : ℝ) :
    g t = Real.sqrt 2 * Real.exp (-(3/2)*t) * (1 / Real.sqrt (1 + Real.exp (-2*t))) := by
  show Real.exp (-t) / Real.sqrt (Real.cosh t) = _
  rw [mul_one_div]
  have h1 : 0 < Real.sqrt (1 + Real.exp (-2*t)) := Real.sqrt_pos.mpr (by positivity)
  have h2 : 0 < Real.sqrt (Real.cosh t) := Real.sqrt_pos.mpr (Real.cosh_pos t)
  rw [div_eq_div_iff h2.ne' h1.ne']
  exact g_cross t

private lemma bnd_eq (t : ℝ) :
    bnd t = Real.sqrt 2 * Real.exp (-(3/2)*t) * (1 - Real.exp (-2*t)/3) := by
  show Real.sqrt 2 * Real.exp (-(3/2)*t) - (Real.sqrt 2/3) * Real.exp (-(7/2)*t) = _
  have h : Real.exp (-(7/2)*t) = Real.exp (-(3/2)*t) * Real.exp (-2*t) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h]; ring

/-- For `0 ≤ v ≤ 1/5`, `(1+v)^{-1/2} ≤ 1 - v/3`. -/
private lemma inv_sqrt_one_add_le (v : ℝ) (hv0 : 0 ≤ v) (hv15 : v ≤ 1/5) :
    1 / Real.sqrt (1 + v) ≤ 1 - v/3 := by
  have h1v : 0 < 1 + v := by linarith
  have h3 : 0 < 1 - v/3 := by linarith
  have hsqrt : 0 < Real.sqrt (1 + v) := Real.sqrt_pos.mpr h1v
  have hfac : (1 - v/3)^2 * (1 + v) = 1 + v*(3 - 5*v + v^2)/9 := by ring
  have hpoly : 0 ≤ v*(3 - 5*v + v^2) := by nlinarith [hv0, hv15, sq_nonneg v]
  have hs : 1 ≤ (1 - v/3)^2 * (1 + v) := by rw [hfac]; nlinarith [hpoly]
  have hsq : ((1:ℝ))^2 ≤ ((1 - v/3) * Real.sqrt (1 + v))^2 := by
    rw [one_pow, mul_pow, Real.sq_sqrt h1v.le]
    exact hs
  have hprod : 0 ≤ (1 - v/3) * Real.sqrt (1 + v) := mul_nonneg h3.le hsqrt.le
  have hone : (1:ℝ) ≤ (1 - v/3) * Real.sqrt (1 + v) := by
    have := sq_le_sq.mp hsq
    rwa [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1), abs_of_nonneg hprod] at this
  rw [div_le_iff₀ hsqrt]
  exact hone

private lemma g_le_bnd {t : ℝ} (ht : T ≤ t) : g t ≤ bnd t := by
  have h2T : Real.exp (-2*t) ≤ 3 - 2*Real.sqrt 2 := by
    have h1 : Real.exp (-2*t) ≤ Real.exp (-2*T) := Real.exp_le_exp.mpr (by linarith)
    rwa [exp_neg_two_T] at h1
  have hv0 : 0 ≤ Real.exp (-2*t) := (Real.exp_pos _).le
  have hv15 : Real.exp (-2*t) ≤ 1/5 := by
    refine le_trans h2T ?_
    have h : (7/5:ℝ) ≤ Real.sqrt 2 :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    linarith
  have hinv := inv_sqrt_one_add_le (Real.exp (-2*t)) hv0 hv15
  rw [g_eq, bnd_eq]
  exact mul_le_mul_of_nonneg_left hinv (by positivity)

/-! ## Integrating the bound -/

private lemma integral_bnd :
    ∫ t in Set.Ioi T, bnd t
      = Real.sqrt 2 * (2/3) * Real.exp (-(3/2)*T)
          - (Real.sqrt 2/3) * (2/7) * Real.exp (-(7/2)*T) := by
  have h3 : IntegrableOn (fun t : ℝ => Real.sqrt 2 * Real.exp (-(3/2)*t)) (Set.Ioi T) :=
    (integrableOn_exp_mul_Ioi (a := -(3/2)) (by norm_num) T).const_mul _
  have h7 : IntegrableOn (fun t : ℝ => (Real.sqrt 2/3) * Real.exp (-(7/2)*t)) (Set.Ioi T) :=
    (integrableOn_exp_mul_Ioi (a := -(7/2)) (by norm_num) T).const_mul _
  show (∫ t in Set.Ioi T, (Real.sqrt 2 * Real.exp (-(3/2)*t)
        - (Real.sqrt 2/3) * Real.exp (-(7/2)*t))) = _
  rw [integral_sub h3 h7, integral_const_mul, integral_const_mul,
      integral_exp_mul_Ioi (a := -(3/2)) (by norm_num) T,
      integral_exp_mul_Ioi (a := -(7/2)) (by norm_num) T]
  ring

private lemma bnd_value :
    Real.sqrt 2 * (2/3) * Real.exp (-(3/2)*T)
        - (Real.sqrt 2/3) * (2/7) * Real.exp (-(7/2)*T) = 8*s/21 := by
  have hs3 : Real.exp (-(3/2)*T) = s^3 := by
    have h : -(3/2)*T = ((3:ℕ):ℝ) * (-(T/2)) := by push_cast; ring
    rw [h, Real.exp_nat_mul]
    rfl
  have hs7 : Real.exp (-(7/2)*T) = s^7 := by
    have h : -(7/2)*T = ((7:ℕ):ℝ) * (-(T/2)) := by push_cast; ring
    rw [h, Real.exp_nat_mul]
    rfl
  rw [hs3, hs7]
  have hσ : Real.sqrt 2 ^ 2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
  have hs2 := s_sq
  have e1 : s^3 = s * s^2 := by ring
  have e2 : s^7 = s * (s^2)^3 := by ring
  rw [e1, e2, hs2]
  have e3 : (Real.sqrt 2 - 1)^3 = 5*Real.sqrt 2 - 7 := by nlinarith [hσ]
  rw [e3]
  ring_nf
  rw [hσ]
  ring

private lemma s_le : s ≤ 21/32 := by
  have hσle : Real.sqrt 2 ≤ 1465/1024 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by norm_num⟩
  have hs2le : s^2 ≤ (21/32)^2 := by
    rw [s_sq]
    have h : (21/32:ℝ)^2 = 441/1024 := by norm_num
    rw [h]
    linarith [hσle]
  have hsn : 0 ≤ s := (Real.exp_pos _).le
  have h := sq_le_sq.mp hs2le
  rwa [abs_of_nonneg hsn, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 21/32)] at h

private lemma integral_bnd_le : ∫ t in Set.Ioi T, bnd t ≤ 1/4 := by
  rw [integral_bnd, bnd_value]
  have : 8*s/21 ≤ 1/4 := by linarith [s_le]
  exact this

theorem integral_sqrt_sq_sub_one_le_quarter :
    ∫ x in Set.Ioi (Real.sqrt 2), ((Real.sqrt (x^2-1))⁻¹ - x⁻¹) * Real.sqrt x ≤ 1/4 := by
  change (∫ x in Set.Ioi (Real.sqrt 2), u x) ≤ 1/4
  rw [integral_subst]
  have hbint : IntegrableOn bnd (Set.Ioi T) := by
    have h3 : IntegrableOn (fun t : ℝ => Real.sqrt 2 * Real.exp (-(3/2)*t)) (Set.Ioi T) :=
      (integrableOn_exp_mul_Ioi (a := -(3/2)) (by norm_num) T).const_mul _
    have h7 : IntegrableOn (fun t : ℝ => (Real.sqrt 2/3) * Real.exp (-(7/2)*t)) (Set.Ioi T) :=
      (integrableOn_exp_mul_Ioi (a := -(7/2)) (by norm_num) T).const_mul _
    exact h3.sub h7
  have hgint : IntegrableOn g (Set.Ioi T) := by
    have h3 : IntegrableOn (fun t : ℝ => Real.sqrt 2 * Real.exp (-(3/2)*t)) (Set.Ioi T) :=
      (integrableOn_exp_mul_Ioi (a := -(3/2)) (by norm_num) T).const_mul _
    have hcont : Continuous g := by
      show Continuous (fun t : ℝ => Real.exp (-t) / Real.sqrt (Real.cosh t))
      exact (Real.continuous_exp.comp continuous_neg).div
        (Real.continuous_sqrt.comp Real.continuous_cosh)
        (fun t => ne_of_gt (Real.sqrt_pos.mpr (Real.cosh_pos t)))
    refine h3.mono' (hcont.aestronglyMeasurable.restrict) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (g_nonneg t)]
    calc g t ≤ bnd t := g_le_bnd (le_of_lt ht)
      _ ≤ Real.sqrt 2 * Real.exp (-(3/2)*t) := by
          show Real.sqrt 2 * Real.exp (-(3/2)*t) - (Real.sqrt 2/3) * Real.exp (-(7/2)*t)
            ≤ Real.sqrt 2 * Real.exp (-(3/2)*t)
          have : 0 ≤ (Real.sqrt 2/3) * Real.exp (-(7/2)*t) := by positivity
          linarith
  have hmono := setIntegral_mono_on hgint hbint measurableSet_Ioi
      (fun t ht => g_le_bnd (le_of_lt ht))
  exact hmono.trans integral_bnd_le

end Commons.Analysis.Integral