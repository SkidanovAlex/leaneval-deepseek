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

private lemma sqrt_two_gt_one : (1:ℝ) < Real.sqrt 2 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)

private lemma T_nonneg : 0 ≤ T := by
  simp only [T]; exact Real.arcosh_nonneg (le_of_lt sqrt_two_gt_one)

private lemma T_pos : 0 < T := by
  simp only [T]; exact Real.arcosh_pos sqrt_two_gt_one

private lemma cosh_T : Real.cosh T = Real.sqrt 2 := by
  simp only [T]; exact Real.cosh_arcosh (le_of_lt sqrt_two_gt_one)

private lemma log_two_le_T : Real.log 2 ≤ T := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hcosh : Real.cosh (Real.log 2) = 5/4 := by
    rw [Real.cosh_log (by norm_num : (0:ℝ) < 2)]; norm_num
  have heq : Real.log 2 = Real.arcosh (5/4) := by
    rw [← hcosh, Real.arcosh_cosh hlog]
  rw [heq]
  simp only [T]
  rw [Real.arcosh_le_arcosh (by norm_num) (Real.sqrt_pos.mpr (by norm_num))]
  rw [Real.le_sqrt (by norm_num) (by norm_num)]
  norm_num

/-- `√a / a = 1 / √a` for `a > 0`. -/
private lemma sqrt_div_self {a : ℝ} (ha : 0 < a) : Real.sqrt a / a = (Real.sqrt a)⁻¹ := by
  have hs0 : Real.sqrt a ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ha)
  have hinv : a⁻¹ = (Real.sqrt a)⁻¹ * (Real.sqrt a)⁻¹ := by
    rw [← mul_inv, ← sq, Real.sq_sqrt ha.le]
  rw [div_eq_mul_inv, hinv, ← mul_assoc, mul_inv_cancel₀ hs0, one_mul]

/-- `√a * b / a = b / √a` for `a > 0`. -/
private lemma sqrt_mul_div {a b : ℝ} (ha : 0 < a) :
    Real.sqrt a * b / a = b / Real.sqrt a := by
  rw [mul_comm (Real.sqrt a) b, mul_div_assoc, sqrt_div_self ha, div_eq_mul_inv]

/-- Pointwise identity of the change of variables `x = cosh t`. -/
private lemma key_pointwise {x : ℝ} (hx : 0 < x) :
    Real.sinh x * u (Real.cosh x) = Real.exp (-x) / Real.sqrt (Real.cosh x) := by
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

/-- Pointwise domination by `√2 · exp(-3x/2)`. -/
private lemma pointwise_bound (x : ℝ) :
    Real.exp (-x) / Real.sqrt (Real.cosh x) ≤ Real.sqrt 2 * Real.exp ((-(3:ℝ)/2) * x) := by
  have hsp : 0 < Real.sqrt (Real.cosh x) := Real.sqrt_pos.mpr (Real.cosh_pos x)
  have hcosh_le : Real.exp x ≤ 2 * Real.cosh x := by
    rw [Real.cosh_eq]; linarith [Real.exp_pos (-x)]
  have h1 : Real.exp (x/2) ≤ Real.sqrt 2 * Real.sqrt (Real.cosh x) := by
    rw [Real.exp_half, ← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) (Real.cosh x)]
    exact Real.sqrt_le_sqrt hcosh_le
  have hK : 1 ≤ Real.sqrt 2 * Real.sqrt (Real.cosh x) * Real.exp (-(x/2)) := by
    have h3 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-(x/2))).le
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h3
    simpa using h3
  rw [div_le_iff₀ hsp]
  have hmul : Real.sqrt 2 * Real.exp ((-(3:ℝ)/2) * x) * Real.sqrt (Real.cosh x)
      = Real.exp (-x) * (Real.sqrt 2 * Real.sqrt (Real.cosh x) * Real.exp (-(x/2))) := by
    have h3exp : Real.exp ((-(3:ℝ)/2) * x) = Real.exp (-x) * Real.exp (-(x/2)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h3exp]; ring
  rw [hmul]
  exact le_mul_of_one_le_right (Real.exp_pos (-x)).le hK

private lemma integral_subst :
    ∫ x in Set.Ioi (Real.sqrt 2), u x
      = ∫ x in Set.Ioi T, Real.exp (-x) / Real.sqrt (Real.cosh x) := by
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
  show Real.sinh x * u (Real.cosh x) = Real.exp (-x) / Real.sqrt (Real.cosh x)
  exact key_pointwise (lt_trans T_pos hx)

private lemma integral_bound :
    ∫ x in Set.Ioi T, Real.exp (-x) / Real.sqrt (Real.cosh x) ≤ 1/3 := by
  have hdom : IntegrableOn (fun x : ℝ => Real.sqrt 2 * Real.exp ((-(3:ℝ)/2) * x)) (Set.Ioi T) :=
    (integrableOn_exp_mul_Ioi (by norm_num : (-(3:ℝ)/2) < 0) T).const_mul _
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi T)]
      (fun x : ℝ => Real.exp (-x) / Real.sqrt (Real.cosh x)) :=
    Eventually.of_forall (fun x => by positivity)
  have hle : (fun x : ℝ => Real.exp (-x) / Real.sqrt (Real.cosh x))
      ≤ᵐ[volume.restrict (Set.Ioi T)] (fun x : ℝ => Real.sqrt 2 * Real.exp ((-(3:ℝ)/2) * x)) :=
    Eventually.of_forall (fun x => pointwise_bound x)
  have h1 := integral_mono_of_nonneg hnn hdom hle
  have hexp : Real.exp ((3/2) * Real.log 2) = 2 * Real.sqrt 2 := by
    have hsplit : (3/2:ℝ) * Real.log 2 = Real.log 2 + Real.log 2 / 2 := by ring
    rw [hsplit, Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 2),
      Real.exp_half, Real.exp_log (by norm_num : (0:ℝ) < 2)]
  have h2 : 2 * Real.sqrt 2 ≤ Real.exp ((3/2) * T) := by
    rw [← hexp]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left log_two_le_T (by norm_num))
  have hfin : 2 * Real.sqrt 2 * Real.exp ((-(3:ℝ)/2) * T) ≤ 1 := by
    have hpos : 0 < Real.exp ((-(3:ℝ)/2) * T) := Real.exp_pos _
    have h3 := mul_le_mul_of_nonneg_right h2 hpos.le
    rw [← Real.exp_add, show (3/2:ℝ) * T + (-(3:ℝ)/2) * T = 0 by ring, Real.exp_zero] at h3
    simpa using h3
  refine h1.trans ?_
  rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-(3:ℝ)/2) < 0) T]
  have key : Real.sqrt 2 * (-Real.exp ((-(3:ℝ)/2) * T) / (-(3:ℝ)/2))
      = Real.sqrt 2 * (2/3) * Real.exp ((-(3:ℝ)/2) * T) := by ring
  rw [key]
  nlinarith [hfin]

theorem integral_sqrt_sq_sub_one_le :
    ∫ x in Set.Ioi (Real.sqrt 2), ((Real.sqrt (x^2-1))⁻¹ - x⁻¹) * Real.sqrt x ≤ 1/3 := by
  calc ∫ x in Set.Ioi (Real.sqrt 2), ((Real.sqrt (x^2-1))⁻¹ - x⁻¹) * Real.sqrt x
      = ∫ x in Set.Ioi (Real.sqrt 2), u x := rfl
    _ = ∫ x in Set.Ioi T, Real.exp (-x) / Real.sqrt (Real.cosh x) := integral_subst
    _ ≤ 1/3 := integral_bound

end Commons.Analysis.Integral