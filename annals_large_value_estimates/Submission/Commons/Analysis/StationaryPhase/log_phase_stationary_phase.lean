import Mathlib.Analysis.Complex.ExponentialBounds
import Submission.Commons.Analysis.Fresnel.fresnel_interval
import Submission.Commons.Analysis.Calculus.logQuot_facts
import Submission.Commons.Analysis.Oscillatory.first_derivative_test_ibp
import Submission.Commons.Analysis.StationaryPhase.logphase_outer_bound

namespace Commons.Analysis.StationaryPhase

open Complex MeasureTheory Real Set
open scoped Real Topology NNReal

set_option autoImplicit false
set_option maxHeartbeats 0

noncomputable section


/-! ### 1. The phase `h y = log y - y` -/

lemma hasDerivAt_logphase (y : ℝ) (hy : y ≠ 0) :
    HasDerivAt (fun y : ℝ => Real.log y - y) (1 / y - 1) y := by
  have h1 : HasDerivAt (fun y : ℝ => Real.log y) y⁻¹ y := Real.hasDerivAt_log hy
  have h2 : HasDerivAt (fun y : ℝ => y) 1 y := hasDerivAt_id y
  have h3 : HasDerivAt (fun y : ℝ => Real.log y - y) (y⁻¹ - 1) y := h1.sub h2
  refine h3.congr_deriv ?_
  rw [one_div]

/-! ### 2. The smooth change of variables `u = W s = s √(G s)` -/

/-- `G s = ∫_0^1 t/(1+st) dt`, the smooth extension of `s ↦ (s - log (1+s))/s²`. -/
def Gfun (s : ℝ) : ℝ := ∫ t in (0:ℝ)..1, t / (1 + s * t)

/-- First derivative of `Gfun`. -/
def Gfun' (s : ℝ) : ℝ := -(∫ t in (0:ℝ)..1, t ^ 2 / (1 + s * t) ^ 2)

/-- Second derivative of `Gfun`. -/
def Gfun'' (s : ℝ) : ℝ := ∫ t in (0:ℝ)..1, 2 * t ^ 3 / (1 + s * t) ^ 3

lemma Gfun_hasDerivAt (s : ℝ) (hs : |s| < 1/2) : HasDerivAt Gfun (Gfun' s) s := by
  have h : HasDerivAt (fun s : ℝ => ∫ t in (0:ℝ)..1, t / (1 + s * t))
      (-(∫ t in (0:ℝ)..1, t ^ 2 / (1 + s * t) ^ 2)) s :=
    Commons.Analysis.Calculus.logQuot_facts.2.1 s hs
  change HasDerivAt (fun s : ℝ => ∫ t in (0:ℝ)..1, t / (1 + s * t))
    (-(∫ t in (0:ℝ)..1, t ^ 2 / (1 + s * t) ^ 2)) s
  exact h

lemma Gfun'_hasDerivAt (s : ℝ) (hs : |s| < 1/2) : HasDerivAt Gfun' (Gfun'' s) s := by
  have h : HasDerivAt (fun u : ℝ => -(∫ t in (0:ℝ)..1, t ^ 2 / (1 + u * t) ^ 2))
      (∫ t in (0:ℝ)..1, 2 * t ^ 3 / (1 + s * t) ^ 3) s :=
    Commons.Analysis.Calculus.logQuot_facts.2.2.1 s hs
  change HasDerivAt (fun u : ℝ => -(∫ t in (0:ℝ)..1, t ^ 2 / (1 + u * t) ^ 2))
    (∫ t in (0:ℝ)..1, 2 * t ^ 3 / (1 + s * t) ^ 3) s
  exact h

lemma Gfun_mul_sq (s : ℝ) (hs : |s| < 1/2) : s ^ 2 * Gfun s = s - Real.log (1 + s) := by
  have h : s ^ 2 * (∫ t in (0:ℝ)..1, t / (1 + s * t)) = s - Real.log (1 + s) :=
    Commons.Analysis.Calculus.logQuot_facts.2.2.2 s hs
  simpa [Gfun] using h

lemma one_add_mul_bounds {s t : ℝ} (hs : |s| ≤ 1/4) (ht : t ∈ Icc (0:ℝ) 1) :
    3/4 ≤ 1 + s * t ∧ 1 + s * t ≤ 5/4 := by
  have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have hst : |s * t| ≤ 1/4 := by
    rw [abs_mul]
    calc |s| * |t| ≤ (1/4) * 1 := mul_le_mul hs ht1 (abs_nonneg _) (by norm_num)
      _ = 1/4 := by ring
  obtain ⟨h1, h2⟩ := abs_le.mp hst
  constructor <;> linarith

lemma Gfun_bounds {s : ℝ} (hs : |s| ≤ 1/4) : 1/4 ≤ Gfun s ∧ Gfun s ≤ 1 := by
  have hden : ∀ t ∈ Icc (0:ℝ) 1, (1 + s * t) ≠ 0 := by
    intro t ht
    have := (one_add_mul_bounds hs ht).1
    linarith
  have hcont : ContinuousOn (fun t : ℝ => t / (1 + s * t)) (Icc 0 1) := by
    apply ContinuousOn.div
    · exact continuous_id.continuousOn
    · exact (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
    · intro t ht; exact hden t ht
  have hcont' : ContinuousOn (fun t : ℝ => t / (1 + s * t)) (uIcc (0:ℝ) 1) := by
    rwa [uIcc_of_le zero_le_one]
  have hint : IntervalIntegrable (fun t : ℝ => t / (1 + s * t)) volume 0 1 := hcont'.intervalIntegrable
  have hpt : ∀ t ∈ Icc (0:ℝ) 1, (4/5) * t ≤ t / (1 + s * t) ∧ t / (1 + s * t) ≤ (4/3) * t := by
    intro t ht
    have hb := one_add_mul_bounds hs ht
    have ht0 : (0:ℝ) ≤ t := ht.1
    have hpos : (0:ℝ) < 1 + s * t := by linarith [hb.1]
    constructor
    · rw [le_div_iff₀ hpos]
      have hle : (4/5) * (1 + s * t) ≤ 1 := by linarith [hb.2]
      calc (4/5) * t * (1 + s * t) = t * ((4/5) * (1 + s * t)) := by ring
        _ ≤ t * 1 := mul_le_mul_of_nonneg_left hle ht0
        _ = t := by ring
    · rw [div_le_iff₀ hpos]
      have hle : 1 ≤ (4/3) * (1 + s * t) := by linarith [hb.1]
      calc t = t * 1 := by ring
        _ ≤ t * ((4/3) * (1 + s * t)) := mul_le_mul_of_nonneg_left hle ht0
        _ = (4/3) * t * (1 + s * t) := by ring
  have hint1 : IntervalIntegrable (fun t : ℝ => (4/5) * t) volume 0 1 :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 1
  have hint2 : IntervalIntegrable (fun t : ℝ => (4/3) * t) volume 0 1 :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 1
  have hv1 : (∫ t in (0:ℝ)..1, (4/5) * t) = 2/5 := by
    rw [intervalIntegral.integral_const_mul, integral_id]; norm_num
  have hv2 : (∫ t in (0:ℝ)..1, (4/3) * t) = 2/3 := by
    rw [intervalIntegral.integral_const_mul, integral_id]; norm_num
  have h1 := intervalIntegral.integral_mono_on (f := fun t : ℝ => (4/5) * t)
    (g := fun t : ℝ => t / (1 + s * t)) zero_le_one hint1 hint (fun t ht => (hpt t ht).1)
  have h2 := intervalIntegral.integral_mono_on (f := fun t : ℝ => t / (1 + s * t))
    (g := fun t : ℝ => (4/3) * t) zero_le_one hint hint2 (fun t ht => (hpt t ht).2)
  rw [hv1] at h1; rw [hv2] at h2
  have hG : (∫ t in (0:ℝ)..1, t / (1 + s * t)) = Gfun s := rfl
  rw [hG] at h1 h2
  constructor <;> linarith

lemma Gfun'_abs_le {s : ℝ} (hs : |s| ≤ 1/4) : |Gfun' s| ≤ 1 := by
  have hb : ∀ t ∈ Icc (0:ℝ) 1, (3/4 : ℝ) ≤ 1 + s * t := fun t ht => (one_add_mul_bounds hs ht).1
  have hden : ∀ t ∈ Icc (0:ℝ) 1, (1 + s * t) ≠ 0 := fun t ht => by linarith [hb t ht]
  have hcont : ContinuousOn (fun t : ℝ => t ^ 2 / (1 + s * t) ^ 2) (Icc 0 1) := by
    apply ContinuousOn.div
    · exact (continuous_id.pow 2).continuousOn
    · exact ((continuous_const.add (continuous_const.mul continuous_id)).pow 2).continuousOn
    · intro t ht; exact pow_ne_zero 2 (hden t ht)
  have hcont' : ContinuousOn (fun t : ℝ => t ^ 2 / (1 + s * t) ^ 2) (uIcc (0:ℝ) 1) := by
    rwa [uIcc_of_le zero_le_one]
  have hint : IntervalIntegrable (fun t : ℝ => t ^ 2 / (1 + s * t) ^ 2) volume 0 1 := hcont'.intervalIntegrable
  have hint2 : IntervalIntegrable (fun t : ℝ => (16/9) * t ^ 2) volume 0 1 :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable 0 1
  have hpt : ∀ t ∈ Icc (0:ℝ) 1, |t ^ 2 / (1 + s * t) ^ 2| ≤ (16/9) * t ^ 2 := by
    intro t ht
    have h1 := hb t ht
    have ht0 : (0:ℝ) ≤ t := ht.1
    have hpos : (0:ℝ) < 1 + s * t := by linarith
    rw [abs_of_nonneg (div_nonneg (sq_nonneg t) (le_of_lt (pow_pos hpos 2)))]
    rw [div_le_iff₀ (pow_pos hpos 2)]
    have h2 : (3/4 : ℝ) ^ 2 ≤ (1 + s * t) ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2
    have hle : 1 ≤ (16/9) * (1 + s * t) ^ 2 := by nlinarith [h2]
    calc t ^ 2 = t ^ 2 * 1 := by ring
      _ ≤ t ^ 2 * ((16/9) * (1 + s * t) ^ 2) := mul_le_mul_of_nonneg_left hle (sq_nonneg t)
      _ = (16/9) * t ^ 2 * (1 + s * t) ^ 2 := by ring
  have step1 : |∫ t in (0:ℝ)..1, t ^ 2 / (1 + s * t) ^ 2|
      ≤ ∫ t in (0:ℝ)..1, |t ^ 2 / (1 + s * t) ^ 2| :=
    intervalIntegral.abs_integral_le_integral_abs zero_le_one
  have step2 : (∫ t in (0:ℝ)..1, |t ^ 2 / (1 + s * t) ^ 2|)
      ≤ ∫ t in (0:ℝ)..1, (16/9) * t ^ 2 :=
    intervalIntegral.integral_mono_on zero_le_one hint.norm hint2 (fun t ht => hpt t ht)
  have hv : (∫ t in (0:ℝ)..1, (16/9) * t ^ 2) = 16/27 := by
    rw [intervalIntegral.integral_const_mul, integral_pow]; norm_num
  simp only [Gfun', abs_neg]
  linarith [hv ▸ step2]

lemma Gfun''_abs_le {s : ℝ} (hs : |s| ≤ 1/4) : |Gfun'' s| ≤ 2 := by
  have hb : ∀ t ∈ Icc (0:ℝ) 1, (3/4 : ℝ) ≤ 1 + s * t := fun t ht => (one_add_mul_bounds hs ht).1
  have hden : ∀ t ∈ Icc (0:ℝ) 1, (1 + s * t) ≠ 0 := fun t ht => by linarith [hb t ht]
  have hcont : ContinuousOn (fun t : ℝ => 2 * t ^ 3 / (1 + s * t) ^ 3) (Icc 0 1) := by
    apply ContinuousOn.div
    · exact (continuous_const.mul (continuous_id.pow 3)).continuousOn
    · exact ((continuous_const.add (continuous_const.mul continuous_id)).pow 3).continuousOn
    · intro t ht; exact pow_ne_zero 3 (hden t ht)
  have hcont' : ContinuousOn (fun t : ℝ => 2 * t ^ 3 / (1 + s * t) ^ 3) (uIcc (0:ℝ) 1) := by
    rwa [uIcc_of_le zero_le_one]
  have hint : IntervalIntegrable (fun t : ℝ => 2 * t ^ 3 / (1 + s * t) ^ 3) volume 0 1 := hcont'.intervalIntegrable
  have hint2 : IntervalIntegrable (fun t : ℝ => (128/27) * t ^ 3) volume 0 1 :=
    (continuous_const.mul (continuous_id.pow 3)).intervalIntegrable 0 1
  have hpt : ∀ t ∈ Icc (0:ℝ) 1, |2 * t ^ 3 / (1 + s * t) ^ 3| ≤ (128/27) * t ^ 3 := by
    intro t ht
    have h1 := hb t ht
    have ht0 : (0:ℝ) ≤ t := ht.1
    have hpos : (0:ℝ) < 1 + s * t := by linarith
    rw [abs_of_nonneg (div_nonneg (by positivity) (le_of_lt (pow_pos hpos 3)))]
    rw [div_le_iff₀ (pow_pos hpos 3)]
    have h2 : (3/4 : ℝ) ^ 3 ≤ (1 + s * t) ^ 3 := pow_le_pow_left₀ (by norm_num) h1 3
    have hle : 1 ≤ (64/27) * (1 + s * t) ^ 3 := by nlinarith [h2]
    calc 2 * t ^ 3 = 2 * t ^ 3 * 1 := by ring
      _ ≤ 2 * t ^ 3 * ((64/27) * (1 + s * t) ^ 3) := mul_le_mul_of_nonneg_left hle (by positivity)
      _ = (128/27) * t ^ 3 * (1 + s * t) ^ 3 := by ring
  have step1 : |∫ t in (0:ℝ)..1, 2 * t ^ 3 / (1 + s * t) ^ 3|
      ≤ ∫ t in (0:ℝ)..1, |2 * t ^ 3 / (1 + s * t) ^ 3| :=
    intervalIntegral.abs_integral_le_integral_abs zero_le_one
  have step2 : (∫ t in (0:ℝ)..1, |2 * t ^ 3 / (1 + s * t) ^ 3|)
      ≤ ∫ t in (0:ℝ)..1, (128/27) * t ^ 3 :=
    intervalIntegral.integral_mono_on zero_le_one hint.norm hint2 (fun t ht => hpt t ht)
  have hv : (∫ t in (0:ℝ)..1, (128/27) * t ^ 3) = 32/27 := by
    rw [intervalIntegral.integral_const_mul, integral_pow]; norm_num
  simp only [Gfun'']
  linarith [hv ▸ step2]



/-! ### 3. The change of variables `u = W s` and its derivatives -/

/-- The change of variables `u = W s = s √(G s)`, making the log phase exactly `-1 - u²`. -/
def Wfun (s : ℝ) : ℝ := s * Real.sqrt (Gfun s)

/-- First derivative of `Wfun`. -/
def Wfun' (s : ℝ) : ℝ := Real.sqrt (Gfun s) + s * (Gfun' s * (2 * Real.sqrt (Gfun s))⁻¹)

/-- Second derivative of `Wfun`. -/
def Wfun'' (s : ℝ) : ℝ :=
  Gfun' s / Real.sqrt (Gfun s) + s * (Gfun'' s / (2 * Real.sqrt (Gfun s)))
    - s * (Gfun' s) ^ 2 / (4 * (Real.sqrt (Gfun s)) ^ 3)

lemma Gfun_pos {s : ℝ} (hs : |s| ≤ 1/4) : 0 < Gfun s :=
  lt_of_lt_of_le (by norm_num) (Gfun_bounds hs).1

lemma sqrt_Gfun_bounds {s : ℝ} (hs : |s| ≤ 1/4) :
    (1/2 : ℝ) ≤ Real.sqrt (Gfun s) ∧ Real.sqrt (Gfun s) ≤ 1 := by
  have h1 : (1/2 : ℝ) ^ 2 ≤ Gfun s := by
    have := (Gfun_bounds hs).1; linarith
  have h2 : Gfun s ≤ 1 := (Gfun_bounds hs).2
  constructor
  · have h := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/2)] at h
  · have h := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_one] at h

lemma Wfun_sq {s : ℝ} (hs : |s| ≤ 1/4) : Wfun s ^ 2 = s - Real.log (1 + s) := by
  have hG : (0:ℝ) < Gfun s := Gfun_pos hs
  have hs' : |s| < 1/2 := lt_of_le_of_lt hs (by norm_num)
  calc Wfun s ^ 2 = s ^ 2 * (Real.sqrt (Gfun s)) ^ 2 := by rw [Wfun]; ring
    _ = s ^ 2 * Gfun s := by rw [Real.sq_sqrt (le_of_lt hG)]
    _ = s - Real.log (1 + s) := Gfun_mul_sq s hs'

lemma Wfun_abs_le {s : ℝ} (hs : |s| ≤ 1/4) : |Wfun s| ≤ 1/4 := by
  have h2 : Real.sqrt (Gfun s) ≤ 1 := (sqrt_Gfun_bounds hs).2
  have h1 : (0:ℝ) ≤ Real.sqrt (Gfun s) := Real.sqrt_nonneg _
  rw [Wfun, abs_mul, abs_of_nonneg h1]
  calc |s| * Real.sqrt (Gfun s) ≤ (1/4) * 1 := mul_le_mul hs h2 h1 (by norm_num)
    _ = 1/4 := by ring

lemma Wfun_quarter : (1/8 : ℝ) ≤ Wfun (1/4) := by
  have hs : |(1:ℝ)/4| ≤ 1/4 := by norm_num
  have h1 : (1/2 : ℝ) ≤ Real.sqrt (Gfun (1/4)) := (sqrt_Gfun_bounds hs).1
  rw [Wfun]
  nlinarith

lemma Wfun_neg_quarter : Wfun (-1/4) ≤ -(1/8) := by
  have hs : |(-1/4 : ℝ)| ≤ 1/4 := by norm_num
  have h1 : (1/2 : ℝ) ≤ Real.sqrt (Gfun (-1/4)) := (sqrt_Gfun_bounds hs).1
  rw [Wfun]
  nlinarith

lemma Gfun_zero : Gfun 0 = 1/2 := by
  rw [Gfun]
  have h : (fun t : ℝ => t / (1 + (0:ℝ) * t)) = fun t : ℝ => t := by funext t; ring_nf
  rw [h, integral_id]
  norm_num

lemma Wfun_hasDerivAt {s : ℝ} (hs : |s| ≤ 1/4) : HasDerivAt Wfun (Wfun' s) s := by
  have hs' : |s| < 1/2 := lt_of_le_of_lt hs (by norm_num)
  have hG : HasDerivAt Gfun (Gfun' s) s := Gfun_hasDerivAt s hs'
  have hpos : Gfun s ≠ 0 := ne_of_gt (Gfun_pos hs)
  have hsqrt : HasDerivAt (fun u : ℝ => Real.sqrt (Gfun u))
      (Gfun' s / (2 * Real.sqrt (Gfun s))) s := hG.sqrt hpos
  have h2 : HasDerivAt (fun u : ℝ => u * Real.sqrt (Gfun u))
      (1 * Real.sqrt (Gfun s) + s * (Gfun' s / (2 * Real.sqrt (Gfun s)))) s :=
    (hasDerivAt_id s).mul hsqrt
  have key : HasDerivAt Wfun (1 * Real.sqrt (Gfun s) + s * (Gfun' s / (2 * Real.sqrt (Gfun s)))) s := by
    convert h2 using 1
    funext u; rfl
  refine key.congr_deriv ?_
  rw [Wfun', one_mul, div_eq_mul_inv]

lemma Wfun'_hasDerivAt {s : ℝ} (hs : |s| ≤ 1/4) : HasDerivAt Wfun' (Wfun'' s) s := by
  have hs' : |s| < 1/2 := lt_of_le_of_lt hs (by norm_num)
  have hG : HasDerivAt Gfun (Gfun' s) s := Gfun_hasDerivAt s hs'
  have hG' : HasDerivAt Gfun' (Gfun'' s) s := Gfun'_hasDerivAt s hs'
  have hpos : Gfun s ≠ 0 := ne_of_gt (Gfun_pos hs)
  have hsppos : (0:ℝ) < Real.sqrt (Gfun s) := Real.sqrt_pos_of_pos (Gfun_pos hs)
  have h2pos : (2 * Real.sqrt (Gfun s)) ≠ 0 := by positivity
  have hsqrt : HasDerivAt (fun u : ℝ => Real.sqrt (Gfun u))
      (Gfun' s / (2 * Real.sqrt (Gfun s))) s := hG.sqrt hpos
  have h2sqrt : HasDerivAt (fun u : ℝ => 2 * Real.sqrt (Gfun u))
      (2 * (Gfun' s / (2 * Real.sqrt (Gfun s)))) s := hsqrt.const_mul 2
  have hinv : HasDerivAt (fun u : ℝ => (2 * Real.sqrt (Gfun u))⁻¹)
      (-(2 * (Gfun' s / (2 * Real.sqrt (Gfun s)))) / (2 * Real.sqrt (Gfun s)) ^ 2) s :=
    h2sqrt.inv h2pos
  have hprod : HasDerivAt (fun u : ℝ => Gfun' u * (2 * Real.sqrt (Gfun u))⁻¹)
      (Gfun'' s * (2 * Real.sqrt (Gfun s))⁻¹
        + Gfun' s * (-(2 * (Gfun' s / (2 * Real.sqrt (Gfun s)))) / (2 * Real.sqrt (Gfun s)) ^ 2)) s :=
    hG'.mul hinv
  have h3 : HasDerivAt (fun u : ℝ => u * (Gfun' u * (2 * Real.sqrt (Gfun u))⁻¹))
      (1 * (Gfun' s * (2 * Real.sqrt (Gfun s))⁻¹)
        + s * (Gfun'' s * (2 * Real.sqrt (Gfun s))⁻¹
        + Gfun' s * (-(2 * (Gfun' s / (2 * Real.sqrt (Gfun s))))
            / (2 * Real.sqrt (Gfun s)) ^ 2))) s :=
    (hasDerivAt_id s).mul hprod
  have hsum := hsqrt.add h3
  have hEq : ((fun u : ℝ => Real.sqrt (Gfun u))
      + fun u => u * (Gfun' u * (2 * Real.sqrt (Gfun u))⁻¹)) = Wfun' := by
    funext u; rfl
  rw [hEq] at hsum
  refine hsum.congr_deriv ?_
  rw [Wfun'']
  field_simp
  ring

lemma Wfun'_pos {s : ℝ} (hs : |s| ≤ 1/4) : 0 < Wfun' s := by
  have h1 : (1/2 : ℝ) ≤ Real.sqrt (Gfun s) := (sqrt_Gfun_bounds hs).1
  have h3 : |Gfun' s| ≤ 1 := Gfun'_abs_le hs
  have h4 : (0:ℝ) < Real.sqrt (Gfun s) := by linarith
  have h6 : |Gfun' s * (2 * Real.sqrt (Gfun s))⁻¹| ≤ 1 := by
    rw [abs_mul, abs_inv, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.sqrt (Gfun s))]
    have hinv : (2 * Real.sqrt (Gfun s))⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by positivity)]
      linarith
    calc |Gfun' s| * (2 * Real.sqrt (Gfun s))⁻¹ ≤ 1 * 1 :=
          mul_le_mul h3 hinv (by positivity) (by norm_num)
      _ = 1 := by ring
  have h5 : |s * (Gfun' s * (2 * Real.sqrt (Gfun s))⁻¹)| ≤ 1/4 := by
    rw [abs_mul]
    calc |s| * |Gfun' s * (2 * Real.sqrt (Gfun s))⁻¹| ≤ (1/4) * 1 :=
          mul_le_mul hs h6 (abs_nonneg _) (by norm_num)
      _ = 1/4 := by ring
  have h7 : -(1/4) ≤ s * (Gfun' s * (2 * Real.sqrt (Gfun s))⁻¹) := (abs_le.mp h5).1
  rw [Wfun']
  linarith

lemma Wfun'_zero : Wfun' 0 = 1 / Real.sqrt 2 := by
  rw [Wfun', Gfun_zero]
  have hz : (0:ℝ) * (Gfun' 0 * (2 * Real.sqrt (1/2))⁻¹) = 0 := by ring
  rw [hz, add_zero]
  rw [show (1:ℝ)/2 = (2:ℝ)⁻¹ by norm_num, Real.sqrt_inv, one_div]

lemma Wfun''_abs_le {s : ℝ} (hs : |s| ≤ 1/4) : |Wfun'' s| ≤ 4 := by
  have h1 : (1/2 : ℝ) ≤ Real.sqrt (Gfun s) := (sqrt_Gfun_bounds hs).1
  have h3 : |Gfun' s| ≤ 1 := Gfun'_abs_le hs
  have h4 : |Gfun'' s| ≤ 2 := Gfun''_abs_le hs
  have h5 : (0:ℝ) < Real.sqrt (Gfun s) := by linarith
  have h6 : (0:ℝ) < (Real.sqrt (Gfun s)) ^ 3 := by positivity
  have h7 : (1/8 : ℝ) ≤ (Real.sqrt (Gfun s)) ^ 3 := by
    have h8 : (1/2 : ℝ) ^ 3 ≤ (Real.sqrt (Gfun s)) ^ 3 := pow_le_pow_left₀ (by norm_num) h1 3
    linarith
  have e1 : |Gfun' s / Real.sqrt (Gfun s)| ≤ 2 := by
    rw [abs_div, abs_of_pos h5, div_le_iff₀ h5]
    nlinarith [h3, h1]
  have e2 : |s * (Gfun'' s / (2 * Real.sqrt (Gfun s)))| ≤ 1/2 := by
    rw [abs_mul, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.sqrt (Gfun s))]
    have hden : (0:ℝ) < 2 * Real.sqrt (Gfun s) := by linarith
    rw [← mul_div_assoc, div_le_iff₀ hden]
    have hnum : |s| * |Gfun'' s| ≤ 1/2 := by
      calc |s| * |Gfun'' s| ≤ (1/4) * 2 := mul_le_mul hs h4 (abs_nonneg _) (by norm_num)
        _ = 1/2 := by ring
    nlinarith [hnum, h1]
  have e3 : |s * (Gfun' s) ^ 2 / (4 * (Real.sqrt (Gfun s)) ^ 3)| ≤ 1/2 := by
    have hnum : |s * (Gfun' s) ^ 2| ≤ 1/4 := by
      rw [abs_mul, abs_pow]
      have hsq : |Gfun' s| ^ 2 ≤ 1 := by nlinarith [h3, abs_nonneg (Gfun' s)]
      calc |s| * |Gfun' s| ^ 2 ≤ (1/4) * 1 := mul_le_mul hs hsq (by positivity) (by norm_num)
        _ = 1/4 := by ring
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 4 * (Real.sqrt (Gfun s)) ^ 3)]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 * (Real.sqrt (Gfun s)) ^ 3)]
    have h4' : (1/2 : ℝ) ≤ 4 * (Real.sqrt (Gfun s)) ^ 3 := by linarith
    calc |s * (Gfun' s) ^ 2| ≤ 1/4 := hnum
      _ = (1/2) * (1/2) := by norm_num
      _ ≤ (1/2) * (4 * (Real.sqrt (Gfun s)) ^ 3) := mul_le_mul_of_nonneg_left h4' (by norm_num)
  set A : ℝ := Gfun' s / Real.sqrt (Gfun s) + s * (Gfun'' s / (2 * Real.sqrt (Gfun s))) with hA
  set C : ℝ := s * (Gfun' s) ^ 2 / (4 * (Real.sqrt (Gfun s)) ^ 3) with hC
  have hmain : |A - C| ≤ |A| + |C| := by
    have := abs_sub_le A 0 C
    simpa using this
  have hA' : |A| ≤ 2 + 1/2 := by
    have := abs_add_le (Gfun' s / Real.sqrt (Gfun s)) (s * (Gfun'' s / (2 * Real.sqrt (Gfun s))))
    rw [hA]; linarith
  rw [Wfun'', hA.symm, hC.symm]
  linarith

/-! ### 4. Integration by parts with a bounded primitive -/

lemma integral_mul_le_of_primitive_bound_right {f : ℝ → ℂ} {K : ℝ → ℝ} {g g' : ℝ → ℂ}
    {r q M B : ℝ} (hrq : r < q)
    (hfcont : ContinuousOn f (Set.Icc r q))
    (hKint : IntervalIntegrable K volume r q)
    (hKbound : ∀ z ∈ Set.Ioo r q, ‖∫ y in z..q, f y‖ ≤ K z)
    (hKnn : ∀ z ∈ Set.Ioo r q, 0 ≤ K z)
    (hgcont : ContinuousOn g (Set.Icc r q))
    (hgderiv : ∀ z ∈ Set.Ioo r q, HasDerivAt g (g' z) z)
    (hg'int : IntervalIntegrable g' volume r q)
    (hg'bound : ∀ z ∈ Set.Ioo r q, ‖g' z‖ ≤ M)
    (hgr : g r = 0)
    (hB : (∫ z in r..q, K z) ≤ B) :
    ‖∫ y in r..q, g y * f y‖ ≤ M * B := by
  have hle : r ≤ q := le_of_lt hrq
  set F : ℝ → ℂ := fun z => ∫ y in z..q, f y with hF
  -- continuity of `f` gives differentiability of the primitive on the open interval
  have hFderiv : ∀ z ∈ Set.Ioo r q, HasDerivAt F (-(f z)) z := by
    intro z hz
    have hzq : z ≤ q := le_of_lt hz.2
    have hint : IntervalIntegrable f volume z q :=
      (hfcont.mono (fun x hx => ⟨le_trans hz.1.le hx.1, hx.2⟩)).intervalIntegrable_of_Icc hzq
    have hcat : ContinuousAt f z :=
      hfcont.continuousAt (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hz) Ioo_subset_Icc_self)
    have hmeas : StronglyMeasurableAtFilter f (𝓝 z) volume :=
      ⟨Set.Ioo r q, isOpen_Ioo.mem_nhds hz,
        ContinuousOn.aestronglyMeasurable
          (hfcont.mono (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)) measurableSet_Ioo⟩
    exact intervalIntegral.integral_hasDerivAt_left hint hmeas hcat
  -- continuity of the primitive on the closed interval via a Lipschitz bound
  obtain ⟨Cf, hCf⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc r q) hfcont
  have hCfnn : (0:ℝ) ≤ Cf := le_trans (norm_nonneg _) (hCf r ⟨le_rfl, hle⟩)
  have hFcont : ContinuousOn F (Set.uIcc r q) := by
    rw [Set.uIcc_of_le hle]
    refine LipschitzOnWith.continuousOn (K := Real.toNNReal Cf) ?_
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    rw [Complex.dist_eq, Real.dist_eq, Real.coe_toNNReal Cf hCfnn]
    have hxq : IntervalIntegrable f volume x q :=
      (hfcont.mono (fun u hu => ⟨le_trans hx.1 hu.1, hu.2⟩)).intervalIntegrable_of_Icc hx.2
    have hyq : IntervalIntegrable f volume y q :=
      (hfcont.mono (fun u hu => ⟨le_trans hy.1 hu.1, hu.2⟩)).intervalIntegrable_of_Icc hy.2
    rcases le_total x y with hxy | hyx
    · have hsplit : F x - F y = ∫ z in x..y, f z := by
        change (∫ z in x..q, f z) - (∫ z in y..q, f z) = ∫ z in x..y, f z
        have hadd : (∫ z in x..y, f z) + (∫ z in y..q, f z) = ∫ z in x..q, f z :=
          intervalIntegral.integral_add_adjacent_intervals
            ((hfcont.mono (fun u hu => ⟨le_trans hx.1 hu.1, le_trans hu.2 hy.2⟩)).intervalIntegrable_of_Icc hxy) hyq
        rw [← hadd]; ring
      rw [hsplit]
      calc ‖∫ z in x..y, f z‖ ≤ Cf * |y - x| := by
            refine intervalIntegral.norm_integral_le_of_norm_le_const (f := f) (fun z hz => ?_)
            rw [Set.uIoc_of_le hxy] at hz
            exact hCf z ⟨le_trans hx.1 hz.1.le, le_trans hz.2 hy.2⟩
        _ = Cf * |x - y| := by rw [abs_sub_comm]
    · have hsplit : F x - F y = -∫ z in y..x, f z := by
        change (∫ z in x..q, f z) - (∫ z in y..q, f z) = -∫ z in y..x, f z
        have hadd : (∫ z in y..x, f z) + (∫ z in x..q, f z) = ∫ z in y..q, f z :=
          intervalIntegral.integral_add_adjacent_intervals
            ((hfcont.mono (fun u hu => ⟨le_trans hy.1 hu.1, le_trans hu.2 hx.2⟩)).intervalIntegrable_of_Icc hyx) hxq
        rw [← hadd]; ring
      rw [hsplit, norm_neg]
      calc ‖∫ z in y..x, f z‖ ≤ Cf * |x - y| := by
            refine intervalIntegral.norm_integral_le_of_norm_le_const (f := f) (fun z hz => ?_)
            rw [Set.uIoc_of_le hyx] at hz
            exact hCf z ⟨le_trans hy.1 hz.1.le, le_trans hz.2 hx.2⟩
        _ = Cf * |x - y| := rfl
  -- integration by parts
  have hu : ContinuousOn g (Set.uIcc r q) := by rwa [Set.uIcc_of_le hle]
  have huu' : ∀ x ∈ Set.Ioo (min r q) (max r q), HasDerivAt g (g' x) x := by
    rw [min_eq_left hle, max_eq_right hle]; exact hgderiv
  have hvv' : ∀ x ∈ Set.Ioo (min r q) (max r q), HasDerivAt F (-(f x)) x := by
    rw [min_eq_left hle, max_eq_right hle]; exact hFderiv
  have hv' : IntervalIntegrable (fun z => -(f z)) volume r q :=
    (hfcont.neg.intervalIntegrable_of_Icc hle)
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := g) (v := F) (u' := g') (v' := fun z => -(f z)) hu hFcont huu' hvv' hg'int hv'
  have hFq : F q = 0 := by simp [hF]
  have h1 : (∫ z in r..q, g z * (-(f z))) = -∫ z in r..q, g z * f z := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr (fun z _ => by ring)
  rw [h1, hFq, hgr] at hibp
  simp only [mul_zero, zero_mul, zero_sub, sub_zero] at hibp
  have hEq : (∫ z in r..q, g z * f z) = ∫ z in r..q, g' z * F z := neg_injective hibp
  rw [hEq]
  refine le_trans (intervalIntegral.norm_integral_le_integral_norm hle) ?_
  have h2 : (∫ z in r..q, ‖g' z * F z‖) = ∫ z in r..q, ‖g' z‖ * ‖F z‖ :=
    intervalIntegral.integral_congr (fun z _ => norm_mul _ _)
  rw [h2]
  have hFcont' : ContinuousOn F (Set.Icc r q) := by rwa [Set.uIcc_of_le hle] at hFcont
  have hint1 : IntervalIntegrable (fun z => ‖g' z‖ * ‖F z‖) volume r q :=
    hg'int.norm.mul_continuousOn hFcont.norm
  have hM : 0 ≤ M := by
    obtain ⟨z, hz⟩ := exists_between hrq
    exact le_trans (norm_nonneg _) (hg'bound z hz)
  have h3 : (∫ z in r..q, ‖g' z‖ * ‖F z‖) ≤ ∫ z in r..q, M * K z := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo hle hint1 (hKint.const_mul M) (fun z hz => ?_)
    have h4 : ‖F z‖ ≤ K z := hKbound z hz
    exact mul_le_mul (hg'bound z hz) h4 (norm_nonneg _) hM
  rw [intervalIntegral.integral_const_mul] at h3
  nlinarith [h3, hB]

lemma integral_mul_le_of_primitive_bound_left {f : ℝ → ℂ} {K : ℝ → ℝ} {g g' : ℝ → ℂ}
    {r q M B : ℝ} (hrq : r < q)
    (hfcont : ContinuousOn f (Set.Icc r q))
    (hKint : IntervalIntegrable K volume r q)
    (hKbound : ∀ z ∈ Set.Ioo r q, ‖∫ y in r..z, f y‖ ≤ K z)
    (hKnn : ∀ z ∈ Set.Ioo r q, 0 ≤ K z)
    (hgcont : ContinuousOn g (Set.Icc r q))
    (hgderiv : ∀ z ∈ Set.Ioo r q, HasDerivAt g (g' z) z)
    (hg'int : IntervalIntegrable g' volume r q)
    (hg'bound : ∀ z ∈ Set.Ioo r q, ‖g' z‖ ≤ M)
    (hgq : g q = 0)
    (hB : (∫ z in r..q, K z) ≤ B) :
    ‖∫ y in r..q, g y * f y‖ ≤ M * B := by
  have hle : r ≤ q := le_of_lt hrq
  set F : ℝ → ℂ := fun z => ∫ y in r..z, f y with hF
  have hFderiv : ∀ z ∈ Set.Ioo r q, HasDerivAt F (f z) z := by
    intro z hz
    have hrz : r ≤ z := le_of_lt hz.1
    have hint : IntervalIntegrable f volume r z :=
      (hfcont.mono (fun x hx => ⟨hx.1, le_trans hx.2 hz.2.le⟩)).intervalIntegrable_of_Icc hrz
    have hcat : ContinuousAt f z :=
      hfcont.continuousAt (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hz) Ioo_subset_Icc_self)
    have hmeas : StronglyMeasurableAtFilter f (𝓝 z) volume :=
      ⟨Set.Ioo r q, isOpen_Ioo.mem_nhds hz,
        ContinuousOn.aestronglyMeasurable
          (hfcont.mono (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)) measurableSet_Ioo⟩
    exact intervalIntegral.integral_hasDerivAt_right hint hmeas hcat
  obtain ⟨Cf, hCf⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc r q) hfcont
  have hCfnn : (0:ℝ) ≤ Cf := le_trans (norm_nonneg _) (hCf r ⟨le_rfl, hle⟩)
  have hFcont : ContinuousOn F (Set.uIcc r q) := by
    rw [Set.uIcc_of_le hle]
    refine LipschitzOnWith.continuousOn (K := Real.toNNReal Cf) ?_
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    rw [Complex.dist_eq, Real.dist_eq, Real.coe_toNNReal Cf hCfnn]
    have hxr : IntervalIntegrable f volume r x :=
      (hfcont.mono (fun u hu => ⟨hu.1, le_trans hu.2 hx.2⟩)).intervalIntegrable_of_Icc hx.1
    have hyr : IntervalIntegrable f volume r y :=
      (hfcont.mono (fun u hu => ⟨hu.1, le_trans hu.2 hy.2⟩)).intervalIntegrable_of_Icc hy.1
    rcases le_total x y with hxy | hyx
    · have hsplit : F y - F x = ∫ z in x..y, f z := by
        change (∫ z in r..y, f z) - (∫ z in r..x, f z) = ∫ z in x..y, f z
        have hadd : (∫ z in r..x, f z) + (∫ z in x..y, f z) = ∫ z in r..y, f z :=
          intervalIntegral.integral_add_adjacent_intervals hxr
            ((hfcont.mono (fun u hu => ⟨le_trans hx.1 hu.1, le_trans hu.2 hy.2⟩)).intervalIntegrable_of_Icc hxy)
        rw [← hadd]; ring
      have heq : ‖F x - F y‖ = ‖∫ z in x..y, f z‖ := by
        rw [← hsplit]
        exact norm_sub_rev (F x) (F y)
      rw [heq, abs_sub_comm x y]
      refine intervalIntegral.norm_integral_le_of_norm_le_const (f := f) (fun z hz => ?_)
      rw [Set.uIoc_of_le hxy] at hz
      exact hCf z ⟨le_trans hx.1 hz.1.le, le_trans hz.2 hy.2⟩
    · have hsplit : F x - F y = ∫ z in y..x, f z := by
        change (∫ z in r..x, f z) - (∫ z in r..y, f z) = ∫ z in y..x, f z
        have hadd : (∫ z in r..y, f z) + (∫ z in y..x, f z) = ∫ z in r..x, f z :=
          intervalIntegral.integral_add_adjacent_intervals hyr
            ((hfcont.mono (fun u hu => ⟨le_trans hy.1 hu.1, le_trans hu.2 hx.2⟩)).intervalIntegrable_of_Icc hyx)
        rw [← hadd]; ring
      rw [hsplit]
      refine intervalIntegral.norm_integral_le_of_norm_le_const (f := f) (fun z hz => ?_)
      rw [Set.uIoc_of_le hyx] at hz
      exact hCf z ⟨le_trans hy.1 hz.1.le, le_trans hz.2 hx.2⟩
  have hu : ContinuousOn g (Set.uIcc r q) := by rwa [Set.uIcc_of_le hle]
  have huu' : ∀ x ∈ Set.Ioo (min r q) (max r q), HasDerivAt g (g' x) x := by
    rw [min_eq_left hle, max_eq_right hle]; exact hgderiv
  have hvv' : ∀ x ∈ Set.Ioo (min r q) (max r q), HasDerivAt F (f x) x := by
    rw [min_eq_left hle, max_eq_right hle]; exact hFderiv
  have hv' : IntervalIntegrable f volume r q := hfcont.intervalIntegrable_of_Icc hle
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := g) (v := F) (u' := g') (v' := f) hu hFcont huu' hvv' hg'int hv'
  have hFr : F r = 0 := by simp [hF]
  rw [hFr, hgq] at hibp
  simp only [mul_zero, zero_mul, zero_sub, sub_zero] at hibp
  have hEq : (∫ z in r..q, g z * f z) = -∫ z in r..q, g' z * F z := hibp
  rw [hEq, norm_neg]
  refine le_trans (intervalIntegral.norm_integral_le_integral_norm hle) ?_
  have h2 : (∫ z in r..q, ‖g' z * F z‖) = ∫ z in r..q, ‖g' z‖ * ‖F z‖ :=
    intervalIntegral.integral_congr (fun z _ => norm_mul _ _)
  rw [h2]
  have hFcont' : ContinuousOn F (Set.Icc r q) := by rwa [Set.uIcc_of_le hle] at hFcont
  have hint1 : IntervalIntegrable (fun z => ‖g' z‖ * ‖F z‖) volume r q :=
    hg'int.norm.mul_continuousOn hFcont.norm
  have hM : 0 ≤ M := by
    obtain ⟨z, hz⟩ := exists_between hrq
    exact le_trans (norm_nonneg _) (hg'bound z hz)
  have h3 : (∫ z in r..q, ‖g' z‖ * ‖F z‖) ≤ ∫ z in r..q, M * K z := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo hle hint1 (hKint.const_mul M) (fun z hz => ?_)
    have h4 : ‖F z‖ ≤ K z := hKbound z hz
    exact mul_le_mul (hg'bound z hz) h4 (norm_nonneg _) hM
  rw [intervalIntegral.integral_const_mul] at h3
  nlinarith [h3, hB]

/-! ### 5. The critical region -/

/-- The oscillatory integrand `E t y = exp (i t (log y - y))`. -/
def Efun (t y : ℝ) : ℂ := Complex.exp (Complex.I * t * (Real.log y - y))

lemma Efun_phase {t s : ℝ} (hs : s ∈ Set.Icc (-(1/4)) (1/4)) :
    Efun t (1 + s) = Complex.exp (-(t : ℂ) * Complex.I)
      * Complex.exp (-(t : ℂ) * Complex.I * (Wfun s : ℂ) ^ 2) := by
  rw [Set.mem_Icc] at hs
  have hW := Wfun_sq (abs_le.mpr ⟨hs.1, hs.2⟩)
  have harg : Real.log (1 + s) - (1 + s) = -(1 + Wfun s ^ 2) := by rw [hW]; ring
  rw [Efun, ← Complex.exp_add]
  congr 1
  have h2 : ((Real.log (1 + s) : ℝ) : ℂ) - ((1 + s : ℝ) : ℂ)
      = ((-(1 + Wfun s ^ 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sub, harg]
  rw [h2]
  push_cast
  ring

lemma continuousOn_Wfun : ContinuousOn Wfun (Set.Icc (-(1/4)) (1/4)) := by
  show ContinuousOn (fun s : ℝ => s * Real.sqrt (Gfun s)) (Set.Icc (-(1/4)) (1/4))
  have hG : ContinuousOn Gfun (Set.Icc (-(1/4)) (1/4)) := by
    intro s hs
    rw [Set.mem_Icc] at hs
    have hs' : |s| < 1/2 := abs_lt.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact (Gfun_hasDerivAt s hs').continuousAt.continuousWithinAt
  have h2 : ContinuousOn (fun s : ℝ => Real.sqrt (Gfun s)) (Set.Icc (-(1/4)) (1/4)) :=
    Real.continuous_sqrt.comp_continuousOn hG
  exact continuousOn_id.mul h2

lemma continuousOn_Wfun' : ContinuousOn Wfun' (Set.Icc (-(1/4)) (1/4)) := by
  show ContinuousOn (fun s : ℝ => Real.sqrt (Gfun s) + s * (Gfun' s * (2 * Real.sqrt (Gfun s))⁻¹))
    (Set.Icc (-(1/4)) (1/4))
  have hG : ContinuousOn Gfun (Set.Icc (-(1/4)) (1/4)) := by
    intro s hs
    rw [Set.mem_Icc] at hs
    have hs' : |s| < 1/2 := abs_lt.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact (Gfun_hasDerivAt s hs').continuousAt.continuousWithinAt
  have hG' : ContinuousOn Gfun' (Set.Icc (-(1/4)) (1/4)) := by
    intro s hs
    rw [Set.mem_Icc] at hs
    have hs' : |s| < 1/2 := abs_lt.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact (Gfun'_hasDerivAt s hs').continuousAt.continuousWithinAt
  have h2 : ContinuousOn (fun s : ℝ => Real.sqrt (Gfun s)) (Set.Icc (-(1/4)) (1/4)) :=
    Real.continuous_sqrt.comp_continuousOn hG
  have hden : ∀ s ∈ Set.Icc (-(1/4)) (1/4), (2 * Real.sqrt (Gfun s)) ≠ 0 := by
    intro s hs
    rw [Set.mem_Icc] at hs
    have h1 : (1/2 : ℝ) ≤ Real.sqrt (Gfun s) :=
      (sqrt_Gfun_bounds (abs_le.mpr ⟨hs.1, hs.2⟩)).1
    positivity
  have h3 : ContinuousOn (fun s : ℝ => (2 * Real.sqrt (Gfun s))⁻¹) (Set.Icc (-(1/4)) (1/4)) :=
    ContinuousOn.inv₀ (continuousOn_const.mul h2) hden
  exact h2.add (continuousOn_id.mul (hG'.mul h3))

/-! ### 5b. Primitives of the phase: the sharp first-derivative-test bound -/

/-- `D y = i (1/y - 1)`, the complexified derivative of the phase. -/
def Dfun (y : ℝ) : ℂ := Complex.I * ((1 / y - 1 : ℝ) : ℂ)

/-- Derivative of `Dfun`. -/
def D'fun (y : ℝ) : ℂ := Complex.I * ((-(1 / y ^ 2) : ℝ) : ℂ)

lemma Dfun_hasDerivAt (y : ℝ) (hy : y ≠ 0) : HasDerivAt Dfun (D'fun y) y := by
  have h1 : HasDerivAt (fun z : ℝ => 1 / z - 1) (-(1 / y ^ 2)) y := by
    have h2 : HasDerivAt (fun z : ℝ => z⁻¹ - 1) (-(y ^ 2)⁻¹) y :=
      (hasDerivAt_inv hy).sub_const 1
    have hf : (fun z : ℝ => 1 / z - 1) = (fun z : ℝ => z⁻¹ - 1) := by
      funext z; rw [one_div]
    rw [hf]
    exact h2.congr_deriv (by rw [one_div])
  have h3 : HasDerivAt (fun z : ℝ => ((1 / z - 1 : ℝ) : ℂ)) (((-(1 / y ^ 2)) : ℝ) : ℂ) y :=
    h1.ofReal_comp
  have h4 := h3.const_mul Complex.I
  have hfun : (fun z : ℝ => Complex.I * ((1 / z - 1 : ℝ) : ℂ)) = Dfun := rfl
  have hval : Complex.I * (((-(1 / y ^ 2)) : ℝ) : ℂ) = D'fun y := rfl
  rw [hfun, hval] at h4
  exact h4

lemma Dfun_norm (y : ℝ) : ‖Dfun y‖ = |1 / y - 1| := by
  rw [Dfun, norm_mul, Complex.norm_I, one_mul]
  rw [show ‖(((1 / y - 1 : ℝ)) : ℂ)‖ = |1 / y - 1| from RCLike.norm_ofReal _]

lemma D'fun_norm (y : ℝ) : ‖D'fun y‖ = 1 / y ^ 2 := by
  rw [D'fun, norm_mul, Complex.norm_I, one_mul]
  rw [show ‖(((-(1 / y ^ 2)) : ℝ) : ℂ)‖ = |-(1 / y ^ 2)| from RCLike.norm_ofReal _]
  rw [abs_neg, abs_of_nonneg (by positivity)]

/-- Pointwise bound for the primitive of the phase on the right of the critical point. -/
lemma primitive_bound_right {t z q : ℝ} (ht : 1 ≤ t) (hz : 1 < z) (hzq : z ≤ q) (hq : q ≤ 2) :
    ‖∫ y in z..q, Efun t y‖ ≤ min (q - z) (6 * q / (t * (z - 1))) := by
  have ht0 : (0:ℝ) < t := by linarith
  have hz1 : (0:ℝ) < z - 1 := by linarith
  have hq1 : (0:ℝ) < q - 1 := by linarith
  refine le_min ?_ ?_
  · have h1 : ‖∫ y in z..q, Efun t y‖ ≤ 1 * |q - z| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (f := fun y => Efun t y) (C := 1)
        (fun y hy => by
          rw [Efun, show Complex.I * t * ((Real.log y : ℂ) - (y : ℂ))
            = ((t * (Real.log y - y) : ℝ) : ℂ) * Complex.I by push_cast; ring]
          exact le_of_eq (Complex.norm_exp_ofReal_mul_I _))
    rwa [one_mul, abs_of_nonneg (by linarith)] at h1
  · set ψ : ℝ → ℂ := fun y => (Dfun y)⁻¹ with hψdef
    set ψ' : ℝ → ℂ := fun y => -(D'fun y) / (Dfun y) ^ 2 with hψ'def
    have hDne : ∀ y ∈ Set.uIcc z q, Dfun y ≠ 0 := by
      intro y hy
      rw [Set.uIcc_of_le hzq] at hy
      have hy1 : 1 < y := lt_of_lt_of_le hz hy.1
      have hy0 : 0 < y := by linarith
      have hyne : y ≠ 1 := by linarith
      rw [Dfun]
      refine mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr ?_)
      intro h
      have h2 : (1:ℝ) / y = 1 := by linarith
      have h3 : y = 1 := by
        rw [div_eq_one_iff_eq (ne_of_gt hy0)] at h2
        linarith
      exact hyne h3
    have hDn : ∀ y ∈ Set.Icc z q, ‖Dfun y‖ = 1 - 1 / y := by
      intro y hy
      have hy1 : 1 < y := lt_of_lt_of_le hz hy.1
      have hy0 : (0:ℝ) < y := by linarith
      rw [Dfun_norm, abs_of_neg (by rw [sub_lt_zero]; rw [div_lt_one hy0]; linarith)]
      ring
    have hψderiv : ∀ x ∈ Set.uIcc z q, HasDerivAt ψ (ψ' x) x := by
      intro x hx
      rw [Set.uIcc_of_le hzq] at hx
      have hx1 : 1 < x := lt_of_lt_of_le hz hx.1
      have hx0 : x ≠ 0 := by linarith
      have h := (Dfun_hasDerivAt x hx0).inv (hDne x (by rw [Set.uIcc_of_le hzq]; exact hx))
      rw [show ψ = fun y => (Dfun y)⁻¹ from hψdef] at *
      refine h.congr_deriv ?_
      rw [hψ'def]
    have hφderiv : ∀ x ∈ Set.uIcc z q, HasDerivAt (fun y : ℝ => Real.log y - y) (1 / x - 1) x := by
      intro x hx
      rw [Set.uIcc_of_le hzq] at hx
      have hx0 : x ≠ 0 := by
        have : 1 < x := lt_of_lt_of_le hz hx.1
        linarith
      exact hasDerivAt_logphase x hx0
    have hcontD : ContinuousOn Dfun (Set.uIcc z q) := by
      rw [Set.uIcc_of_le hzq]
      show ContinuousOn (fun y : ℝ => Complex.I * ((1 / y - 1 : ℝ) : ℂ)) _
      have h1 : ContinuousOn (fun y : ℝ => (1 / y - 1 : ℝ)) (Set.Icc z q) := by
        refine ContinuousOn.sub (continuousOn_const.div continuousOn_id ?_) continuousOn_const
        intro y hy
        have : 1 < y := lt_of_lt_of_le hz hy.1
        exact ne_of_gt (by linarith)
      exact continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn h1)
    have hψcont : ContinuousOn ψ (Set.uIcc z q) := by
      rw [show ψ = fun y => (Dfun y)⁻¹ from hψdef]
      exact hcontD.inv₀ hDne
    have hD'cont : ContinuousOn D'fun (Set.uIcc z q) := by
      rw [Set.uIcc_of_le hzq]
      show ContinuousOn (fun y : ℝ => Complex.I * ((-(1 / y ^ 2) : ℝ) : ℂ)) _
      have h1 : ContinuousOn (fun y : ℝ => (-(1 / y ^ 2) : ℝ)) (Set.Icc z q) := by
        refine ContinuousOn.neg (ContinuousOn.div continuousOn_const (continuousOn_id.pow 2) ?_)
        intro y hy
        have : 1 < y := lt_of_lt_of_le hz hy.1
        exact pow_ne_zero 2 (ne_of_gt (by linarith))
      exact continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn h1)
    have hψ'cont : ContinuousOn ψ' (Set.uIcc z q) := by
      rw [show ψ' = fun y => -(D'fun y) / (Dfun y) ^ 2 from hψ'def]
      exact (hD'cont.neg).div (hcontD.pow 2) (fun y hy => pow_ne_zero 2 (hDne y hy))
    have hψ'int : IntervalIntegrable (fun x => ‖ψ' x‖) volume z q :=
      hψ'cont.norm.intervalIntegrable
    have key := Commons.Analysis.Oscillatory.first_derivative_test_ibp (ψ := ψ) (ψ' := ψ')
      (φ := fun y : ℝ => Real.log y - y) (φ' := fun y : ℝ => 1 / y - 1)
      hzq ht0 hψderiv hφderiv hψcont hψ'cont hψ'int
    have hLHS : (∫ x in z..q, ψ x * (Complex.I * ((1 / x - 1 : ℝ) : ℂ))
        * Complex.exp (Complex.I * (t * ((Real.log x - x : ℝ) : ℂ))))
        = ∫ x in z..q, Efun t x := by
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      have hxD : Dfun x ≠ 0 := by
        rw [Set.uIcc_of_le hzq] at hx
        exact hDne x (by rw [Set.uIcc_of_le hzq]; exact hx)
      rw [Efun]
      rw [show ψ x = (Dfun x)⁻¹ from by rw [hψdef]]
      rw [show Complex.I * ((1 / x - 1 : ℝ) : ℂ) = Dfun x from rfl]
      rw [inv_mul_cancel₀ hxD, one_mul]
      congr 1
      push_cast
      ring
    rw [hLHS] at key
    have hψz : ‖ψ z‖ ≤ z / (z - 1) := by
      have h1 : ψ z = (Dfun z)⁻¹ := by rw [hψdef]
      rw [h1, norm_inv, hDn z ⟨le_rfl, hzq⟩]
      have hthis : (1 - 1 / z)⁻¹ = z / (z - 1) := by
        have hz0 : (0:ℝ) < z := by linarith
        have h1 : (1:ℝ) - 1/z = (z - 1)/z := by field_simp
        rw [h1, inv_div]
      rw [hthis]
    have hψq : ‖ψ q‖ ≤ z / (z - 1) := by
      have h1 : ψ q = (Dfun q)⁻¹ := by rw [hψdef]
      rw [h1, norm_inv, hDn q ⟨hzq, le_rfl⟩]
      have hthis : (1 - 1 / q)⁻¹ = q / (q - 1) := by
        have hq0 : (0:ℝ) < q := by linarith
        have h1 : (1:ℝ) - 1/q = (q - 1)/q := by field_simp
        rw [h1, inv_div]
      rw [hthis]
      rw [div_le_div_iff₀ hq1 hz1]
      nlinarith [hzq, hz1, hq1]
    have hInt : (∫ x in z..q, ‖ψ' x‖) ≤ 1 / (z - 1) := by
      have hpt : ∀ x ∈ Set.Icc z q, ‖ψ' x‖ ≤ 1 / (x - 1) ^ 2 := by
        intro x hx
        have hx1 : 1 < x := lt_of_lt_of_le hz hx.1
        have hx0 : (0:ℝ) < x := by linarith
        have hxne : x ≠ 0 := ne_of_gt hx0
        have h1 : ψ' x = -(D'fun x) / (Dfun x) ^ 2 := by rw [hψ'def]
        rw [h1, norm_div, norm_neg, D'fun_norm, norm_pow, hDn x hx]
        have e1 : (1:ℝ) / x ^ 2 / (1 - 1 / x) ^ 2 = 1 / (x - 1) ^ 2 := by
          field_simp
        rw [e1]
      have hint2 : IntervalIntegrable (fun x : ℝ => 1 / (x - 1) ^ 2) volume z q := by
        refine ContinuousOn.intervalIntegrable_of_Icc hzq ?_
        refine ContinuousOn.div continuousOn_const ((continuousOn_id.sub continuousOn_const).pow 2) ?_
        intro x hx
        have : 1 < x := lt_of_lt_of_le hz hx.1
        exact pow_ne_zero 2 (by linarith)
      have hmono := intervalIntegral.integral_mono_on hzq hψ'int hint2 hpt
      have hval : (∫ x in z..q, 1 / (x - 1) ^ 2) ≤ 1 / (z - 1) := by
        have hderiv : ∀ x ∈ Set.uIcc z q,
            HasDerivAt (fun y : ℝ => -(y - 1)⁻¹) (1 / (x - 1) ^ 2) x := by
          intro x hx
          rw [Set.uIcc_of_le hzq] at hx
          have hx1 : x - 1 ≠ 0 := by
            have hx1' : 1 < x := lt_of_lt_of_le hz hx.1
            intro h
            linarith
          have h := (((hasDerivAt_id x).sub_const 1).inv hx1).neg
          refine h.congr_deriv ?_
          simp only [id_eq]
          ring
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint2]
        rw [show -(q - 1)⁻¹ - -(z - 1)⁻¹ = (z - 1)⁻¹ - (q - 1)⁻¹ by ring]
        rw [show (z - 1)⁻¹ = 1 / (z - 1) by rw [one_div]]
        linarith [inv_nonneg.mpr hq1.le]
      linarith [hmono, hval]
    have hmain : ‖∫ x in z..q, Efun t x‖ ≤ t⁻¹ * (z / (z - 1) + z / (z - 1) + 1 / (z - 1)) :=
      le_trans key (mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr ht0.le))
    refine le_trans hmain ?_
    rw [inv_mul_le_iff₀ ht0]
    rw [show t * (6 * q / (t * (z - 1))) = 6 * q / (z - 1) by field_simp]
    have h2 : z / (z - 1) + z / (z - 1) + 1 / (z - 1) = (2 * z + 1) / (z - 1) := by
      field_simp
      ring
    rw [h2]
    rw [div_le_div_iff₀ hz1 hz1]
    nlinarith [hzq, hz, ht, hq]


/-! ### 5c. Auxiliary estimates -/

lemma integral_inv_sq_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, 1 / x ^ 2) = 1 / a - 1 / b := by
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun y : ℝ => -(y⁻¹)) ((x ^ 2)⁻¹) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx0 : x ≠ 0 := by
      have hx' : 0 < x := lt_of_lt_of_le ha hx.1
      linarith
    exact ((hasDerivAt_inv hx0).neg).congr_deriv (by ring)
  have hint : IntervalIntegrable (fun x : ℝ => (x ^ 2)⁻¹) volume a b := by
    refine ContinuousOn.intervalIntegrable_of_Icc hab ?_
    have h2 : ContinuousOn (fun x : ℝ => x ^ 2) (Set.Icc a b) := continuousOn_id.pow 2
    exact h2.inv₀ (fun x hx => pow_ne_zero 2 (by
      have hx' : 0 < x := lt_of_lt_of_le ha hx.1
      linarith))
  simp only [one_div]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  rw [show -(b⁻¹) - -(a⁻¹) = a⁻¹ - b⁻¹ by ring]

/-- Pointwise bound for the primitive of the phase on the left of the critical point. -/
lemma primitive_bound_left {t p z : ℝ} (ht : 1 ≤ t) (hp : 1/2 ≤ p) (hpz : p ≤ z) (hz : z < 1) :
    ‖∫ y in p..z, Efun t y‖ ≤ min (z - p) (6 / (t * (1 - z))) := by
  have ht0 : (0:ℝ) < t := by linarith
  have hz1 : (0:ℝ) < 1 - z := by linarith
  refine le_min ?_ ?_
  · have h1 : ‖∫ y in p..z, Efun t y‖ ≤ 1 * |z - p| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (f := fun y => Efun t y) (C := 1)
        (fun y hy => by
          rw [Efun, show Complex.I * t * ((Real.log y : ℂ) - (y : ℂ))
            = ((t * (Real.log y - y) : ℝ) : ℂ) * Complex.I by push_cast; ring]
          exact le_of_eq (Complex.norm_exp_ofReal_mul_I _))
    rwa [one_mul, abs_of_nonneg (by linarith)] at h1
  · set ψ : ℝ → ℂ := fun y => (Dfun y)⁻¹ with hψdef
    set ψ' : ℝ → ℂ := fun y => -(D'fun y) / (Dfun y) ^ 2 with hψ'def
    have hDne : ∀ y ∈ Set.uIcc p z, Dfun y ≠ 0 := by
      intro y hy
      rw [Set.uIcc_of_le hpz] at hy
      have hy0 : 0 < y := by linarith [hy.1, hp]
      have hyne : y ≠ 1 := by linarith [hy.2, hz]
      rw [Dfun]
      refine mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr ?_)
      intro h
      have h2 : (1:ℝ) / y = 1 := by linarith
      have h3 : y = 1 := by
        rw [div_eq_one_iff_eq (ne_of_gt hy0)] at h2
        linarith
      exact hyne h3
    have hDn : ∀ y ∈ Set.Icc p z, ‖Dfun y‖ = 1 / y - 1 := by
      intro y hy
      have hy1 : y < 1 := lt_of_le_of_lt hy.2 hz
      have hy0 : (0:ℝ) < y := by linarith [hy.1, hp]
      rw [Dfun_norm, abs_of_nonneg (by
        rw [sub_nonneg, one_le_div hy0]
        linarith)]
    have hψderiv : ∀ x ∈ Set.uIcc p z, HasDerivAt ψ (ψ' x) x := by
      intro x hx
      rw [Set.uIcc_of_le hpz] at hx
      have hx0 : x ≠ 0 := by
        have hx' : 0 < x := by linarith [hx.1, hp]
        linarith
      have h := (Dfun_hasDerivAt x hx0).inv (hDne x (by rw [Set.uIcc_of_le hpz]; exact hx))
      rw [show ψ = fun y => (Dfun y)⁻¹ from hψdef] at *
      refine h.congr_deriv ?_
      rw [hψ'def]
    have hφderiv : ∀ x ∈ Set.uIcc p z, HasDerivAt (fun y : ℝ => Real.log y - y) (1 / x - 1) x := by
      intro x hx
      rw [Set.uIcc_of_le hpz] at hx
      have hx0 : x ≠ 0 := by
        have hx' : 0 < x := by linarith [hx.1, hp]
        linarith
      exact hasDerivAt_logphase x hx0
    have hcontD : ContinuousOn Dfun (Set.uIcc p z) := by
      rw [Set.uIcc_of_le hpz]
      show ContinuousOn (fun y : ℝ => Complex.I * ((1 / y - 1 : ℝ) : ℂ)) _
      have h1 : ContinuousOn (fun y : ℝ => (1 / y - 1 : ℝ)) (Set.Icc p z) := by
        refine ContinuousOn.sub (continuousOn_const.div continuousOn_id ?_) continuousOn_const
        intro y hy
        have hy' : 0 < y := by linarith [hy.1, hp]
        exact ne_of_gt (by linarith)
      exact continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn h1)
    have hψcont : ContinuousOn ψ (Set.uIcc p z) := by
      rw [show ψ = fun y => (Dfun y)⁻¹ from hψdef]
      exact hcontD.inv₀ hDne
    have hD'cont : ContinuousOn D'fun (Set.uIcc p z) := by
      rw [Set.uIcc_of_le hpz]
      show ContinuousOn (fun y : ℝ => Complex.I * ((-(1 / y ^ 2) : ℝ) : ℂ)) _
      have h1 : ContinuousOn (fun y : ℝ => (-(1 / y ^ 2) : ℝ)) (Set.Icc p z) := by
        refine ContinuousOn.neg (ContinuousOn.div continuousOn_const (continuousOn_id.pow 2) ?_)
        intro y hy
        have hy' : 0 < y := by linarith [hy.1, hp]
        exact pow_ne_zero 2 (ne_of_gt (by linarith))
      exact continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn h1)
    have hψ'cont : ContinuousOn ψ' (Set.uIcc p z) := by
      rw [show ψ' = fun y => -(D'fun y) / (Dfun y) ^ 2 from hψ'def]
      exact (hD'cont.neg).div (hcontD.pow 2) (fun y hy => pow_ne_zero 2 (hDne y hy))
    have hψ'int : IntervalIntegrable (fun x => ‖ψ' x‖) volume p z :=
      hψ'cont.norm.intervalIntegrable
    have key := Commons.Analysis.Oscillatory.first_derivative_test_ibp (ψ := ψ) (ψ' := ψ')
      (φ := fun y : ℝ => Real.log y - y) (φ' := fun y : ℝ => 1 / y - 1)
      hpz ht0 hψderiv hφderiv hψcont hψ'cont hψ'int
    have hLHS : (∫ x in p..z, ψ x * (Complex.I * ((1 / x - 1 : ℝ) : ℂ))
        * Complex.exp (Complex.I * (t * ((Real.log x - x : ℝ) : ℂ))))
        = ∫ x in p..z, Efun t x := by
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      have hxD : Dfun x ≠ 0 := by
        rw [Set.uIcc_of_le hpz] at hx
        exact hDne x (by rw [Set.uIcc_of_le hpz]; exact hx)
      rw [Efun]
      rw [show ψ x = (Dfun x)⁻¹ from by rw [hψdef]]
      rw [show Complex.I * ((1 / x - 1 : ℝ) : ℂ) = Dfun x from rfl]
      rw [inv_mul_cancel₀ hxD, one_mul]
      congr 1
      push_cast
      ring
    rw [hLHS] at key
    have hψp : ‖ψ p‖ ≤ z / (1 - z) := by
      have h1 : ψ p = (Dfun p)⁻¹ := by rw [hψdef]
      rw [h1, norm_inv, hDn p ⟨le_rfl, hpz⟩]
      have hp0 : (0:ℝ) < p := by linarith
      have hthis : (1 / p - 1)⁻¹ = p / (1 - p) := by
        have h2 : (1:ℝ) / p - 1 = (1 - p)/p := by field_simp
        rw [h2, inv_div]
      rw [hthis]
      rw [div_le_div_iff₀ (by linarith) hz1]
      nlinarith [hpz]
    have hψz : ‖ψ z‖ ≤ z / (1 - z) := by
      have h1 : ψ z = (Dfun z)⁻¹ := by rw [hψdef]
      rw [h1, norm_inv, hDn z ⟨hpz, le_rfl⟩]
      have hz0' : (0:ℝ) < z := by linarith
      have hthis : (1 / z - 1)⁻¹ = z / (1 - z) := by
        have h2 : (1:ℝ) / z - 1 = (1 - z)/z := by field_simp
        rw [h2, inv_div]
      rw [hthis]
    have hInt : (∫ x in p..z, ‖ψ' x‖) ≤ 1 / (1 - z) := by
      have hpt : ∀ x ∈ Set.Icc p z, ‖ψ' x‖ ≤ 1 / (1 - x) ^ 2 := by
        intro x hx
        have hx1 : x < 1 := lt_of_le_of_lt hx.2 hz
        have hx0 : (0:ℝ) < x := by linarith [hx.1, hp]
        have h1 : ψ' x = -(D'fun x) / (Dfun x) ^ 2 := by rw [hψ'def]
        rw [h1, norm_div, norm_neg, D'fun_norm, norm_pow, hDn x hx]
        have e1 : (1:ℝ) / x ^ 2 / (1 / x - 1) ^ 2 = 1 / (1 - x) ^ 2 := by
          field_simp
        rw [e1]
      have hint2 : IntervalIntegrable (fun x : ℝ => 1 / (1 - x) ^ 2) volume p z := by
        refine ContinuousOn.intervalIntegrable_of_Icc hpz ?_
        refine ContinuousOn.div continuousOn_const ((continuousOn_const.sub continuousOn_id).pow 2) ?_
        intro x hx
        have : x < 1 := lt_of_le_of_lt hx.2 hz
        exact pow_ne_zero 2 (by linarith)
      have hmono := intervalIntegral.integral_mono_on hpz hψ'int hint2 hpt
      have hval : (∫ x in p..z, 1 / (1 - x) ^ 2) ≤ 1 / (1 - z) := by
        have hsub : (∫ x in p..z, 1 / (1 - x) ^ 2) = ∫ u in (1 - z)..(1 - p), 1 / u ^ 2 := by
          have h := intervalIntegral.integral_comp_sub_left (f := fun u : ℝ => 1 / u ^ 2)
            (a := p) (b := z) 1
          simpa using h
        rw [hsub, integral_inv_sq_eq (by linarith : (0:ℝ) < 1 - z) (by linarith)]
        have hp1 : (0:ℝ) < 1 - p := by linarith
        have hpos : (0:ℝ) < 1 / (1 - p) := one_div_pos.mpr hp1
        linarith
      linarith [hmono, hval]
    have hmain : ‖∫ x in p..z, Efun t x‖ ≤ t⁻¹ * (z / (1 - z) + z / (1 - z) + 1 / (1 - z)) :=
      le_trans key (mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr ht0.le))
    refine le_trans hmain ?_
    rw [inv_mul_le_iff₀ ht0]
    rw [show t * (6 / (t * (1 - z))) = 6 / (1 - z) by field_simp]
    have h2 : z / (1 - z) + z / (1 - z) + 1 / (1 - z) = (2 * z + 1) / (1 - z) := by
      field_simp
      ring
    rw [h2]
    rw [div_le_div_iff₀ hz1 hz1]
    nlinarith [hz, hz1, ht]

/-! ### 6. Elementary facts -/

lemma Wfun_zero : Wfun 0 = 0 := by
  rw [Wfun]; ring

lemma continuousOn_Efun (t : ℝ) {c d : ℝ} (hc : 0 < c) :
    ContinuousOn (Efun t) (Set.Icc c d) := by
  have hlog : ContinuousOn (fun y : ℝ => Real.log y) (Set.Icc c d) :=
    Real.continuousOn_log.mono (fun y hy => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [hy.1, hc])
  have key : ContinuousOn
      (fun y : ℝ => Complex.exp (Complex.I * t * ((Real.log y : ℂ) - (y : ℂ)))) (Set.Icc c d) := by
    refine Complex.continuous_exp.comp_continuousOn ?_
    refine continuousOn_const.mul ?_
    exact (Complex.continuous_ofReal.comp_continuousOn hlog).sub
      (Complex.continuous_ofReal.comp_continuousOn continuousOn_id)
  exact key

/-! ### 7. Integrability of the `K`-functions and the two `log`-bounds -/

lemma intervalIntegrable_min_right {t C a b : ℝ} (ht : 0 ≤ t) (hC : 0 ≤ C)
    (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 5/4) :
    IntervalIntegrable (fun z : ℝ => min (5/4 - z) (C / (t * (z - 1)))) volume a b := by
  refine IntervalIntegrable.mono_fun' (f := fun z : ℝ => min (5/4 - z) (C / (t * (z - 1))))
    (g := fun z : ℝ => 5/4 - z) ((continuousOn_const.sub continuousOn_id).intervalIntegrable) ?_ ?_
  · exact (Measurable.min (by fun_prop) (by fun_prop)).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with z hz
    rw [Set.uIoc_of_le hab] at hz
    rw [Real.norm_eq_abs]
    have h1 : (0:ℝ) ≤ 5/4 - z := by linarith [hz.2]
    have h2 : (0:ℝ) ≤ C / (t * (z - 1)) := div_nonneg hC (mul_nonneg ht (by linarith [ha, hz.1]))
    rw [abs_of_nonneg (le_min h1 h2)]
    exact le_trans (min_le_left _ _) (by linarith [hz.1])

lemma intervalIntegrable_min_left {t C : ℝ} (ht : 0 ≤ t) (hC : 0 ≤ C) :
    IntervalIntegrable (fun z : ℝ => min (z - 3/4) (C / (t * (1 - z)))) volume (3/4) 1 := by
  refine IntervalIntegrable.mono_fun' (f := fun z : ℝ => min (z - 3/4) (C / (t * (1 - z))))
    (g := fun z : ℝ => z - 3/4) ((continuousOn_id.sub continuousOn_const).intervalIntegrable) ?_ ?_
  · exact (Measurable.min (by fun_prop) (by fun_prop)).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with z hz
    rw [Set.uIoc_of_le (by norm_num : (3/4:ℝ) ≤ 1)] at hz
    rw [Real.norm_eq_abs]
    have h1 : (0:ℝ) ≤ z - 3/4 := by linarith [hz.1]
    have h2 : (0:ℝ) ≤ C / (t * (1 - z)) := div_nonneg hC (mul_nonneg ht (by linarith [hz.2]))
    rw [abs_of_nonneg (le_min h1 h2)]
    exact le_trans (min_le_left _ _) (by linarith [hz.2])

lemma K_right_integral {t : ℝ} (ht : 2 ≤ t) :
    (∫ z in (1:ℝ)..(5/4), min (5/4 - z) (6 * (5/4) / (t * (z - 1)))) ≤ (8 + 8 * Real.log t) / t := by
  have ht0 : (0:ℝ) < t := by linarith
  have hl : (0:ℝ) ≤ Real.log t := Real.log_nonneg (by linarith)
  set K : ℝ → ℝ := fun z => min (5/4 - z) (6 * (5/4) / (t * (z - 1))) with hKdef
  have hKint : ∀ a b : ℝ, 1 ≤ a → a ≤ b → b ≤ 5/4 → IntervalIntegrable K volume a b := by
    intro a b ha hab hb
    rw [hKdef]
    exact intervalIntegrable_min_right ht0.le (by norm_num) ha hab hb
  rcases le_or_gt 30 t with h30 | h30
  · -- t ≥ 30: split at `1 + 7.5/t`
    have hε0 : (0:ℝ) < 7.5/t := by positivity
    have hε : 1 + 7.5/t ≤ 5/4 := by
      have hε' : 7.5/t ≤ 1/4 := by rw [div_le_iff₀ ht0]; linarith
      linarith
    have h1 : (∫ z in (1:ℝ)..(1 + 7.5/t), K z) ≤ 1/4 * (7.5/t) := by
      have hb : ∀ z ∈ Set.Icc (1:ℝ) (1 + 7.5/t), K z ≤ 1/4 := by
        intro z hz
        rw [Set.mem_Icc] at hz
        rw [hKdef]
        exact le_trans (min_le_left _ _) (by linarith [hz.2])
      have hmono := intervalIntegral.integral_mono_on (by linarith)
        (hKint 1 (1 + 7.5/t) le_rfl (by linarith) hε) intervalIntegrable_const hb
      rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
      refine le_trans hmono (le_of_eq ?_)
      ring
    have h2 : (∫ z in (1 + 7.5/t)..(5/4), K z) ≤ 6 * (5/4) / t * Real.log t := by
      have hcont : ContinuousOn (fun z : ℝ => 6 * (5/4) / (t * (z - 1)))
          (Set.Icc (1 + 7.5/t) (5/4)) := by
        refine ContinuousOn.div continuousOn_const (continuousOn_const.mul (continuousOn_id.sub continuousOn_const)) ?_
        intro z hz
        have : 1 < z := by linarith [hz.1]
        positivity
      have hint2 : IntervalIntegrable (fun z : ℝ => 6 * (5/4) / (t * (z - 1)))
          volume (1 + 7.5/t) (5/4) := by
        rw [← Set.uIcc_of_le (by linarith : (1:ℝ) + 7.5/t ≤ 5/4)] at hcont
        exact hcont.intervalIntegrable
      have hb : ∀ z ∈ Set.Icc (1 + 7.5/t) (5/4), K z ≤ 6 * (5/4) / (t * (z - 1)) := fun z _ => by
        rw [hKdef]; exact min_le_right _ _
      have hmono := intervalIntegral.integral_mono_on (by linarith)
        (hKint _ _ (by linarith) (by linarith) le_rfl) hint2 hb
      have hval : (∫ z in (1 + 7.5/t)..(5/4), 6 * (5/4) / (t * (z - 1)))
          = 6 * (5/4) / t * (Real.log (1/4) - Real.log (7.5/t)) := by
        have hderiv : ∀ z ∈ Set.uIcc (1 + 7.5/t) (5/4),
            HasDerivAt (fun y : ℝ => 6 * (5/4) / t * Real.log (y - 1))
              (6 * (5/4) / (t * (z - 1))) z := by
          intro z hz
          rw [Set.uIcc_of_le (by linarith)] at hz
          have hz1 : z - 1 ≠ 0 := by linarith [hz.1]
          have h := (((hasDerivAt_id z).sub_const 1).log hz1).const_mul (6 * (5/4) / t)
          refine h.congr_deriv ?_
          simp only [id_eq]
          field_simp
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint2]
        rw [show (5/4:ℝ) - 1 = 1/4 by norm_num, show (1 + 7.5/t) - 1 = 7.5/t by ring]
        ring
      refine le_trans hmono ?_
      rw [hval]
      have hbd : Real.log (1/4) - Real.log (7.5/t) ≤ Real.log t := by
        have h1 : Real.log (1/4:ℝ) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
        have h2' : Real.log (7.5/t) = Real.log 7.5 - Real.log t := Real.log_div (by norm_num) (by linarith)
        have h3 : (0:ℝ) ≤ Real.log 7.5 := Real.log_nonneg (by norm_num)
        rw [h2']
        linarith
      have hpos : (0:ℝ) ≤ 6 * (5/4) / t := by positivity
      exact mul_le_mul_of_nonneg_left hbd hpos
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hKint 1 (1 + 7.5/t) le_rfl (by linarith) hε)
      (hKint (1 + 7.5/t) (5/4) (by linarith) (by linarith) le_rfl)
    rw [← hsplit]
    have hsum : 1/4 * (7.5/t) + 6 * (5/4) / t * Real.log t ≤ (8 + 8 * Real.log t) / t := by
      rw [le_div_iff₀ ht0]
      have e1 : 1/4 * (7.5/t) * t = 7.5/4 := by field_simp
      have e2 : 6 * (5/4) / t * Real.log t * t = 6 * (5/4) * Real.log t := by field_simp
      nlinarith [hl, e1, e2]
    linarith [h1, h2]
  · -- t < 30
    have h1 : (∫ z in (1:ℝ)..(5/4), K z) ≤ 1/16 := by
      have hb : ∀ z ∈ Set.Icc (1:ℝ) (5/4), K z ≤ 1/4 := by
        intro z hz
        rw [Set.mem_Icc] at hz
        rw [hKdef]
        exact le_trans (min_le_left _ _) (by linarith [hz.2])
      have hmono := intervalIntegral.integral_mono_on (by norm_num)
        (hKint 1 (5/4) le_rfl (by norm_num) le_rfl) intervalIntegrable_const hb
      rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
      refine le_trans hmono (le_of_eq ?_)
      norm_num
    refine le_trans h1 ?_
    rw [le_div_iff₀ ht0]
    nlinarith [hl, ht, h30]

lemma K_left_integral {t : ℝ} (ht : 2 ≤ t) :
    (∫ z in (3/4:ℝ)..1, min (z - 3/4) (6 / (t * (1 - z)))) ≤ (8 + 8 * Real.log t) / t := by
  have ht0 : (0:ℝ) < t := by linarith
  have htrans : (∫ z in (3/4:ℝ)..1, min (z - 3/4) (6 / (t * (1 - z))))
      = ∫ w in (1:ℝ)..(5/4), min ((2 - w) - 3/4) (6 / (t * (1 - (2 - w)))) := by
    have h := intervalIntegral.integral_comp_sub_left (a := (3/4:ℝ)) (b := 1)
      (f := fun x : ℝ => min ((2 - x) - 3/4) (6 / (t * (1 - (2 - x))))) 2
    have hL : (∫ x in (3/4:ℝ)..1,
          min (2 - (2 - x) - 3/4) (6 / (t * (1 - (2 - (2 - x))))))
        = ∫ x in (3/4:ℝ)..1, min (x - 3/4) (6 / (t * (1 - x))) := by
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      have e1 : 2 - (2 - x) - 3/4 = x - 3/4 := by ring
      have e2 : 1 - (2 - (2 - x)) = 1 - x := by ring
      rw [e1, e2]
    rw [hL] at h
    norm_num at h
    exact h
  rw [htrans]
  have hcongr : (∫ w in (1:ℝ)..(5/4), min ((2 - w) - 3/4) (6 / (t * (1 - (2 - w)))))
      = ∫ w in (1:ℝ)..(5/4), min (5/4 - w) (6 / (t * (w - 1))) := by
    refine intervalIntegral.integral_congr (fun w _ => ?_)
    have h1 : (2 - w) - 3/4 = 5/4 - w := by ring
    have h2 : 1 - (2 - w) = w - 1 := by ring
    rw [h1, h2]
  rw [hcongr]
  have hKi : IntervalIntegrable (fun w : ℝ => min (5/4 - w) (6 / (t * (w - 1)))) volume 1 (5/4) := by
    refine IntervalIntegrable.mono_fun' (f := fun w : ℝ => min (5/4 - w) (6 / (t * (w - 1))))
      (g := fun w : ℝ => 5/4 - w) ((continuousOn_const.sub continuousOn_id).intervalIntegrable) ?_ ?_
    · exact (Measurable.min (by fun_prop) (by fun_prop)).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with w hw
      rw [Set.uIoc_of_le (by norm_num : (1:ℝ) ≤ 5/4)] at hw
      rw [Real.norm_eq_abs]
      have h1 : (0:ℝ) ≤ 5/4 - w := by linarith [hw.2]
      have h2 : (0:ℝ) ≤ 6 / (t * (w - 1)) := div_nonneg (by norm_num) (mul_nonneg ht0.le (by linarith [hw.1]))
      rw [abs_of_nonneg (le_min h1 h2)]
      exact le_trans (min_le_left _ _) (by linarith [hw.1])
  have hKRi : IntervalIntegrable (fun w : ℝ => min (5/4 - w) (6 * (5/4) / (t * (w - 1)))) volume 1 (5/4) :=
    intervalIntegrable_min_right ht0.le (by norm_num) le_rfl (by norm_num) le_rfl
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (1:ℝ) ≤ 5/4) hKi hKRi (fun w hw => ?_)
  · exact le_trans hmono (K_right_integral ht)
  · refine min_le_min le_rfl ?_
    rw [Set.mem_Icc] at hw
    have hz : (0:ℝ) ≤ (t * (w - 1))⁻¹ := inv_nonneg.mpr (mul_nonneg ht0.le (by linarith [hw.1]))
    have h6 : (6:ℝ) ≤ 6 * (5/4) := by norm_num
    calc 6 / (t * (w - 1)) = 6 * (t * (w - 1))⁻¹ := rfl
      _ ≤ (6 * (5/4)) * (t * (w - 1))⁻¹ := mul_le_mul_of_nonneg_right h6 hz
      _ = 6 * (5/4) / (t * (w - 1)) := rfl


/-! ### 8. The amplitude-variation error `γ = A - √2·A(1)·W'` -/

/-- Amplitude variation bound on the right of the critical point. -/
lemma gamma_bound_right {A : ℝ → ℂ} {t : ℝ} (ht : 2 ≤ t)
    (hA : ContDiff ℝ 1 A) (hAc : ∀ y, ‖A y‖ ≤ 1) (hAd : ∀ y, ‖deriv A y‖ ≤ 1) :
    ‖∫ y in (1:ℝ)..(5/4),
        (A y - ((Real.sqrt 2 * A 1) * ((Wfun' (y - 1) : ℝ) : ℂ))) * Efun t y‖
      ≤ (1 + 4 * Real.sqrt 2) * ((8 + 8 * Real.log t) / t) := by
  have ht0 : (0:ℝ) < t := by linarith
  set γ : ℝ → ℂ := fun y => A y - ((Real.sqrt 2 * A 1) * ((Wfun' (y - 1) : ℝ) : ℂ)) with hγ
  set γ' : ℝ → ℂ :=
    fun z => deriv A z - ((Real.sqrt 2 * A 1) * ((deriv Wfun' (z - 1) : ℝ) : ℂ)) with hγ'
  have hγ1 : γ 1 = 0 := by
    show A 1 - ((Real.sqrt 2 * A 1) * ((Wfun' (1 - 1) : ℝ) : ℂ)) = 0
    rw [show (1:ℝ) - 1 = 0 by norm_num, Wfun'_zero]
    have h2 : ((Real.sqrt 2 : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ)) = 1 := by
      rw [← Complex.ofReal_mul]
      rw [show (Real.sqrt 2 * (1 / Real.sqrt 2) : ℝ) = 1 by
        rw [mul_one_div, div_self (ne_of_gt (Real.sqrt_pos_of_pos (by norm_num : (0:ℝ) < 2)))]]
      norm_num
    have h3 : (Real.sqrt 2 * A 1) * ((1 / Real.sqrt 2 : ℝ) : ℂ) = A 1 := by
      calc (Real.sqrt 2 * A 1) * ((1 / Real.sqrt 2 : ℝ) : ℂ)
          = A 1 * ((Real.sqrt 2 : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ)) := by push_cast; ring
        _ = A 1 := by rw [h2, mul_one]
    rw [h3, sub_self]
  have hshift : ContinuousOn (fun y : ℝ => Wfun' (y - 1)) (Set.Icc (1:ℝ) (5/4)) :=
    continuousOn_Wfun'.comp (continuous_id.sub continuous_const).continuousOn (fun y hy => by
      rw [Set.mem_Icc] at hy ⊢
      constructor <;> linarith [hy.1, hy.2])
  have hγcont : ContinuousOn γ (Set.Icc (1:ℝ) (5/4)) := by
    show ContinuousOn (fun y : ℝ => A y - ((Real.sqrt 2 * A 1) * ((Wfun' (y - 1) : ℝ) : ℂ)))
      (Set.Icc (1:ℝ) (5/4))
    exact hA.continuous.continuousOn.sub
      (ContinuousOn.mul continuousOn_const (Complex.continuous_ofReal.comp_continuousOn hshift))
  have hγderiv : ∀ z ∈ Set.Ioo (1:ℝ) (5/4), HasDerivAt γ (γ' z) z := by
    intro z hz
    have hz1 : |z - 1| ≤ 1/4 := by
      rw [abs_le]; constructor <;> linarith [hz.1, hz.2]
    show HasDerivAt (fun y : ℝ => A y - ((Real.sqrt 2 * A 1) * ((Wfun' (y - 1) : ℝ) : ℂ)))
      (deriv A z - ((Real.sqrt 2 * A 1) * ((deriv Wfun' (z - 1) : ℝ) : ℂ))) z
    have hA' : HasDerivAt A (deriv A z) z :=
      (hA.differentiable (by norm_num)).differentiableAt.hasDerivAt
    have hW1 : HasDerivAt (fun y : ℝ => Wfun' (y - 1)) (Wfun'' (z - 1)) z := by
      have h1 : HasDerivAt Wfun' (Wfun'' (z - 1)) (z - 1) := Wfun'_hasDerivAt (s := z - 1) hz1
      have h2 : HasDerivAt (fun y : ℝ => (fun x => x - 1) y) (1:ℝ) z :=
        (hasDerivAt_id z).sub_const 1
      have h := HasDerivAt.comp z h1 h2
      rwa [mul_one] at h
    have hW2 : HasDerivAt (fun y : ℝ => ((Wfun' (y - 1) : ℝ) : ℂ))
        (((deriv Wfun' (z - 1) : ℝ)) : ℂ) z := by
      rw [← (Wfun'_hasDerivAt hz1).deriv] at hW1
      exact hW1.ofReal_comp
    exact hA'.sub (hW2.const_mul (Real.sqrt 2 * A 1))
  have hγ'bound : ∀ z : ℝ, |z - 1| ≤ 1/4 → ‖γ' z‖ ≤ 1 + 4 * Real.sqrt 2 := by
    intro z hz
    have hW : deriv Wfun' (z - 1) = Wfun'' (z - 1) := (Wfun'_hasDerivAt (s := z - 1) hz).deriv
    show ‖deriv A z - ((Real.sqrt 2 * A 1) * ((deriv Wfun' (z - 1) : ℝ) : ℂ))‖ ≤ 1 + 4 * Real.sqrt 2
    rw [hW]
    calc ‖deriv A z - ((Real.sqrt 2 * A 1) * ((Wfun'' (z - 1) : ℝ) : ℂ))‖
        ≤ ‖deriv A z‖ + ‖((Real.sqrt 2 * A 1) * ((Wfun'' (z - 1) : ℝ) : ℂ))‖ := norm_sub_le _ _
      _ ≤ 1 + Real.sqrt 2 * 4 := by
          refine add_le_add (hAd z) ?_
          have h1 : ‖(Real.sqrt 2 * A 1 : ℂ)‖ ≤ Real.sqrt 2 := by
            rw [norm_mul]
            have h2 : ‖((Real.sqrt 2 : ℝ) : ℂ)‖ = Real.sqrt 2 := by simp [Real.sqrt_nonneg]
            rw [h2]
            calc Real.sqrt 2 * ‖A 1‖ ≤ Real.sqrt 2 * 1 :=
                  mul_le_mul_of_nonneg_left (hAc 1) (Real.sqrt_nonneg 2)
              _ = Real.sqrt 2 := mul_one _
          have h2 : ‖((Wfun'' (z - 1) : ℝ) : ℂ)‖ ≤ 4 := by
            have h3 : ‖((Wfun'' (z - 1) : ℝ) : ℂ)‖ = |Wfun'' (z - 1)| := by simp
            rw [h3]; exact Wfun''_abs_le hz
          calc ‖((Real.sqrt 2 * A 1 : ℂ)) * ((Wfun'' (z - 1) : ℝ) : ℂ)‖
              = ‖(Real.sqrt 2 * A 1 : ℂ)‖ * ‖((Wfun'' (z - 1) : ℝ) : ℂ)‖ := norm_mul _ _
            _ ≤ Real.sqrt 2 * 4 := mul_le_mul h1 h2 (norm_nonneg _) (Real.sqrt_nonneg 2)
      _ = 1 + 4 * Real.sqrt 2 := by ring
  have hγ'meas : Measurable γ' := by
    show Measurable (fun z : ℝ => deriv A z -
      ((Real.sqrt 2 * A 1) * ((deriv Wfun' (z - 1) : ℝ) : ℂ)))
    exact (measurable_deriv A).sub (measurable_const.mul
      (Complex.measurable_ofReal.comp ((measurable_deriv Wfun').comp (measurable_id.sub measurable_const))))
  have hγ'int : IntervalIntegrable γ' volume (1:ℝ) (5/4) := by
    refine IntervalIntegrable.mono_fun' (f := γ') (g := fun _ : ℝ => 1 + 4 * Real.sqrt 2)
      intervalIntegrable_const hγ'meas.aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with z hz
    rw [Set.uIoc_of_le (by norm_num : (1:ℝ) ≤ 5/4)] at hz
    have hz1 : |z - 1| ≤ 1/4 := by rw [abs_le]; constructor <;> linarith [hz.1, hz.2]
    exact hγ'bound z hz1
  have hKint : IntervalIntegrable (fun z : ℝ => min (5/4 - z) (6 * (5/4) / (t * (z - 1))))
      volume (1:ℝ) (5/4) :=
    intervalIntegrable_min_right ht0.le (by norm_num) le_rfl (by norm_num) le_rfl
  have hKbound : ∀ z ∈ Set.Ioo (1:ℝ) (5/4),
      ‖∫ y in z..(5/4), Efun t y‖ ≤ min (5/4 - z) (6 * (5/4) / (t * (z - 1))) :=
    fun z hz => primitive_bound_right (q := 5/4) (by linarith) hz.1 hz.2.le (by norm_num)
  have hKnn : ∀ z ∈ Set.Ioo (1:ℝ) (5/4), 0 ≤ min (5/4 - z) (6 * (5/4) / (t * (z - 1))) := by
    intro z hz
    exact le_min (by linarith [hz.2]) (div_nonneg (by norm_num) (mul_nonneg ht0.le (by linarith [hz.1])))
  have key := integral_mul_le_of_primitive_bound_right (f := Efun t)
    (K := fun z : ℝ => min (5/4 - z) (6 * (5/4) / (t * (z - 1)))) (g := γ) (g' := γ')
    (r := 1) (q := 5/4) (M := 1 + 4 * Real.sqrt 2) (B := (8 + 8 * Real.log t) / t)
    (by norm_num) (continuousOn_Efun t (by norm_num)) hKint hKbound hKnn hγcont hγderiv hγ'int
    (fun z hz => hγ'bound z (by rw [abs_le]; constructor <;> linarith [hz.1, hz.2])) hγ1
    (K_right_integral ht)
  simpa only [hγ] using key

/-- Amplitude variation bound on the left of the critical point. -/
lemma gamma_bound_left {A : ℝ → ℂ} {t : ℝ} (ht : 2 ≤ t)
    (hA : ContDiff ℝ 1 A) (hAc : ∀ y, ‖A y‖ ≤ 1) (hAd : ∀ y, ‖deriv A y‖ ≤ 1) :
    ‖∫ y in (3/4:ℝ)..1,
        (A y - ((Real.sqrt 2 * A 1) * ((Wfun' (y - 1) : ℝ) : ℂ))) * Efun t y‖
      ≤ (1 + 4 * Real.sqrt 2) * ((8 + 8 * Real.log t) / t) := by
  have ht0 : (0:ℝ) < t := by linarith
  set γ : ℝ → ℂ := fun y => A y - ((Real.sqrt 2 * A 1) * ((Wfun' (y - 1) : ℝ) : ℂ)) with hγ
  set γ' : ℝ → ℂ :=
    fun z => deriv A z - ((Real.sqrt 2 * A 1) * ((deriv Wfun' (z - 1) : ℝ) : ℂ)) with hγ'
  have hγ1 : γ 1 = 0 := by
    show A 1 - ((Real.sqrt 2 * A 1) * ((Wfun' (1 - 1) : ℝ) : ℂ)) = 0
    rw [show (1:ℝ) - 1 = 0 by norm_num, Wfun'_zero]
    have h2 : ((Real.sqrt 2 : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ)) = 1 := by
      rw [← Complex.ofReal_mul]
      rw [show (Real.sqrt 2 * (1 / Real.sqrt 2) : ℝ) = 1 by
        rw [mul_one_div, div_self (ne_of_gt (Real.sqrt_pos_of_pos (by norm_num : (0:ℝ) < 2)))]]
      norm_num
    have h3 : (Real.sqrt 2 * A 1) * ((1 / Real.sqrt 2 : ℝ) : ℂ) = A 1 := by
      calc (Real.sqrt 2 * A 1) * ((1 / Real.sqrt 2 : ℝ) : ℂ)
          = A 1 * ((Real.sqrt 2 : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ)) := by push_cast; ring
        _ = A 1 := by rw [h2, mul_one]
    rw [h3, sub_self]
  have hshift : ContinuousOn (fun y : ℝ => Wfun' (y - 1)) (Set.Icc (3/4:ℝ) 1) :=
    continuousOn_Wfun'.comp (continuous_id.sub continuous_const).continuousOn (fun y hy => by
      rw [Set.mem_Icc] at hy ⊢
      constructor <;> linarith [hy.1, hy.2])
  have hγcont : ContinuousOn γ (Set.Icc (3/4:ℝ) 1) := by
    show ContinuousOn (fun y : ℝ => A y - ((Real.sqrt 2 * A 1) * ((Wfun' (y - 1) : ℝ) : ℂ)))
      (Set.Icc (3/4:ℝ) 1)
    exact hA.continuous.continuousOn.sub
      (ContinuousOn.mul continuousOn_const (Complex.continuous_ofReal.comp_continuousOn hshift))
  have hγderiv : ∀ z ∈ Set.Ioo (3/4:ℝ) 1, HasDerivAt γ (γ' z) z := by
    intro z hz
    have hz1 : |z - 1| ≤ 1/4 := by
      rw [abs_le]; constructor <;> linarith [hz.1, hz.2]
    show HasDerivAt (fun y : ℝ => A y - ((Real.sqrt 2 * A 1) * ((Wfun' (y - 1) : ℝ) : ℂ)))
      (deriv A z - ((Real.sqrt 2 * A 1) * ((deriv Wfun' (z - 1) : ℝ) : ℂ))) z
    have hA' : HasDerivAt A (deriv A z) z :=
      (hA.differentiable (by norm_num)).differentiableAt.hasDerivAt
    have hW1 : HasDerivAt (fun y : ℝ => Wfun' (y - 1)) (Wfun'' (z - 1)) z := by
      have h1 : HasDerivAt Wfun' (Wfun'' (z - 1)) (z - 1) := Wfun'_hasDerivAt (s := z - 1) hz1
      have h2 : HasDerivAt (fun y : ℝ => (fun x => x - 1) y) (1:ℝ) z :=
        (hasDerivAt_id z).sub_const 1
      have h := HasDerivAt.comp z h1 h2
      rwa [mul_one] at h
    have hW2 : HasDerivAt (fun y : ℝ => ((Wfun' (y - 1) : ℝ) : ℂ))
        (((deriv Wfun' (z - 1) : ℝ)) : ℂ) z := by
      rw [← (Wfun'_hasDerivAt hz1).deriv] at hW1
      exact hW1.ofReal_comp
    exact hA'.sub (hW2.const_mul (Real.sqrt 2 * A 1))
  have hγ'bound : ∀ z : ℝ, |z - 1| ≤ 1/4 → ‖γ' z‖ ≤ 1 + 4 * Real.sqrt 2 := by
    intro z hz
    have hW : deriv Wfun' (z - 1) = Wfun'' (z - 1) := (Wfun'_hasDerivAt (s := z - 1) hz).deriv
    show ‖deriv A z - ((Real.sqrt 2 * A 1) * ((deriv Wfun' (z - 1) : ℝ) : ℂ))‖ ≤ 1 + 4 * Real.sqrt 2
    rw [hW]
    calc ‖deriv A z - ((Real.sqrt 2 * A 1) * ((Wfun'' (z - 1) : ℝ) : ℂ))‖
        ≤ ‖deriv A z‖ + ‖((Real.sqrt 2 * A 1) * ((Wfun'' (z - 1) : ℝ) : ℂ))‖ := norm_sub_le _ _
      _ ≤ 1 + Real.sqrt 2 * 4 := by
          refine add_le_add (hAd z) ?_
          have h1 : ‖(Real.sqrt 2 * A 1 : ℂ)‖ ≤ Real.sqrt 2 := by
            rw [norm_mul]
            have h2 : ‖((Real.sqrt 2 : ℝ) : ℂ)‖ = Real.sqrt 2 := by simp [Real.sqrt_nonneg]
            rw [h2]
            calc Real.sqrt 2 * ‖A 1‖ ≤ Real.sqrt 2 * 1 :=
                  mul_le_mul_of_nonneg_left (hAc 1) (Real.sqrt_nonneg 2)
              _ = Real.sqrt 2 := mul_one _
          have h2 : ‖((Wfun'' (z - 1) : ℝ) : ℂ)‖ ≤ 4 := by
            have h3 : ‖((Wfun'' (z - 1) : ℝ) : ℂ)‖ = |Wfun'' (z - 1)| := by simp
            rw [h3]; exact Wfun''_abs_le hz
          calc ‖((Real.sqrt 2 * A 1 : ℂ)) * ((Wfun'' (z - 1) : ℝ) : ℂ)‖
              = ‖(Real.sqrt 2 * A 1 : ℂ)‖ * ‖((Wfun'' (z - 1) : ℝ) : ℂ)‖ := norm_mul _ _
            _ ≤ Real.sqrt 2 * 4 := mul_le_mul h1 h2 (norm_nonneg _) (Real.sqrt_nonneg 2)
      _ = 1 + 4 * Real.sqrt 2 := by ring
  have hγ'meas : Measurable γ' := by
    show Measurable (fun z : ℝ => deriv A z -
      ((Real.sqrt 2 * A 1) * ((deriv Wfun' (z - 1) : ℝ) : ℂ)))
    exact (measurable_deriv A).sub (measurable_const.mul
      (Complex.measurable_ofReal.comp ((measurable_deriv Wfun').comp (measurable_id.sub measurable_const))))
  have hγ'int : IntervalIntegrable γ' volume (3/4:ℝ) 1 := by
    refine IntervalIntegrable.mono_fun' (f := γ') (g := fun _ : ℝ => 1 + 4 * Real.sqrt 2)
      intervalIntegrable_const hγ'meas.aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with z hz
    rw [Set.uIoc_of_le (by norm_num : (3/4:ℝ) ≤ 1)] at hz
    have hz1 : |z - 1| ≤ 1/4 := by rw [abs_le]; constructor <;> linarith [hz.1, hz.2]
    exact hγ'bound z hz1
  have hKint : IntervalIntegrable (fun z : ℝ => min (z - 3/4) (6 / (t * (1 - z))))
      volume (3/4:ℝ) 1 :=
    intervalIntegrable_min_left ht0.le (by norm_num)
  have hKbound : ∀ z ∈ Set.Ioo (3/4:ℝ) 1,
      ‖∫ y in (3/4)..z, Efun t y‖ ≤ min (z - 3/4) (6 / (t * (1 - z))) :=
    fun z hz => primitive_bound_left (p := 3/4) (by linarith) (by norm_num) hz.1.le hz.2
  have hKnn : ∀ z ∈ Set.Ioo (3/4:ℝ) 1, 0 ≤ min (z - 3/4) (6 / (t * (1 - z))) := by
    intro z hz
    exact le_min (by linarith [hz.1]) (div_nonneg (by norm_num) (mul_nonneg ht0.le (by linarith [hz.2])))
  have key := integral_mul_le_of_primitive_bound_left (f := Efun t)
    (K := fun z : ℝ => min (z - 3/4) (6 / (t * (1 - z)))) (g := γ) (g' := γ')
    (r := 3/4) (q := 1) (M := 1 + 4 * Real.sqrt 2) (B := (8 + 8 * Real.log t) / t)
    (by norm_num) (continuousOn_Efun t (by norm_num)) hKint hKbound hKnn hγcont hγderiv hγ'int
    (fun z hz => hγ'bound z (by rw [abs_le]; constructor <;> linarith [hz.1, hz.2])) hγ1
    (K_left_integral ht)
  simpa only [hγ] using key


/-! ### 9. The critical region `∫_{3/4}^{5/4} A·Efun` -/

/-- Continuity of `y ↦ Wfun' (y - 1)` on intervals inside `[3/4, 5/4]`. -/
lemma continuousOn_Wfun'_sub_one {c d : ℝ} (hc : 3/4 ≤ c) (hd : d ≤ 5/4) :
    ContinuousOn (fun y : ℝ => Wfun' (y - 1)) (Set.Icc c d) :=
  continuousOn_Wfun'.comp (continuous_id.sub continuous_const).continuousOn (fun y hy => by
    rw [Set.mem_Icc] at hy ⊢
    constructor <;> linarith [hy.1, hy.2])

/-- Substitution `u = Wfun (y - 1)` on the right half of the critical region. -/
lemma subst_right (t : ℝ) :
    (∫ y in (1:ℝ)..(5/4), ((Wfun' (y - 1) : ℝ) : ℂ) * Efun t y)
      = Complex.exp (-(t : ℂ) * Complex.I)
          * (∫ u in (0:ℝ)..Wfun (1/4),
              Complex.exp (-((t : ℂ) * Complex.I) * (u : ℂ) ^ 2)) := by
  set g : ℝ → ℂ := fun u => Complex.exp (-((t : ℂ) * Complex.I) * (u : ℂ) ^ 2) with hg
  set F : ℝ → ℂ := fun y => ((Wfun' (y - 1) : ℝ) : ℂ) * Efun t y with hF
  have h1 : (∫ y in (1:ℝ)..(5/4), F y) = ∫ s in (0:ℝ)..(1/4), F (s + 1) := by
    have h := intervalIntegral.integral_comp_add_right (a := (0:ℝ)) (b := (1/4:ℝ)) (f := F) 1
    have h2 : (∫ s in (0:ℝ)..(1/4), F (s + 1)) = ∫ y in (1:ℝ)..(5/4), F y := by
      rw [h]; norm_num
    exact h2.symm
  have h2 : (∫ s in (0:ℝ)..(1/4), F (s + 1))
      = ∫ s in (0:ℝ)..(1/4), Complex.exp (-(t : ℂ) * Complex.I) * (Wfun' s • g (Wfun s)) := by
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/4)] at hs
    have hs' : s ∈ Set.Icc (-(1/4)) (1/4) := by
      rw [Set.mem_Icc] at hs ⊢; constructor <;> linarith [hs.1, hs.2]
    show ((Wfun' (s + 1 - 1) : ℝ) : ℂ) * Efun t (s + 1)
        = Complex.exp (-(t : ℂ) * Complex.I) * (Wfun' s • g (Wfun s))
    rw [show s + 1 - 1 = s by ring, show s + 1 = 1 + s by ring, Efun_phase hs', hg]
    simp only [Complex.real_smul]
    ring
  have h3 : (∫ s in (0:ℝ)..(1/4), Complex.exp (-(t : ℂ) * Complex.I) * (Wfun' s • g (Wfun s)))
      = Complex.exp (-(t : ℂ) * Complex.I) * (∫ s in (0:ℝ)..(1/4), Wfun' s • g (Wfun s)) :=
    intervalIntegral.integral_const_mul _ _
  have h4 : (∫ s in (0:ℝ)..(1/4), Wfun' s • g (Wfun s))
      = ∫ u in Wfun (0:ℝ)..Wfun (1/4), g u := by
    have h := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg (a := (0:ℝ)) (b := (1/4:ℝ))
      (f := Wfun) (f' := Wfun') (g := g)
      (by
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/4)]
        exact continuousOn_Wfun.mono (fun y hy => by
          rw [Set.mem_Icc] at hy ⊢; constructor <;> linarith [hy.1, hy.2]))
      (by
        intro x hx
        rw [min_eq_left (by norm_num : (0:ℝ) ≤ 1/4), max_eq_right (by norm_num)] at hx
        exact Wfun_hasDerivAt (by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]))
      (by
        intro x hx
        rw [min_eq_left (by norm_num : (0:ℝ) ≤ 1/4), max_eq_right (by norm_num)] at hx
        exact le_of_lt (Wfun'_pos (by rw [abs_le]; constructor <;> linarith [hx.1, hx.2])))
    simpa only [Function.comp_apply] using h
  have key : (∫ y in (1:ℝ)..(5/4), F y)
      = Complex.exp (-(t : ℂ) * Complex.I) * (∫ u in (0:ℝ)..Wfun (1/4), g u) := by
    rw [h1, h2, h3, h4, Wfun_zero]
  simpa only [hF, hg] using key

/-- Substitution `u = Wfun (y - 1)` on the left half of the critical region. -/
lemma subst_left (t : ℝ) :
    (∫ y in (3/4:ℝ)..1, ((Wfun' (y - 1) : ℝ) : ℂ) * Efun t y)
      = Complex.exp (-(t : ℂ) * Complex.I)
          * (∫ u in Wfun (-(1/4))..(0:ℝ),
              Complex.exp (-((t : ℂ) * Complex.I) * (u : ℂ) ^ 2)) := by
  set g : ℝ → ℂ := fun u => Complex.exp (-((t : ℂ) * Complex.I) * (u : ℂ) ^ 2) with hg
  set F : ℝ → ℂ := fun y => ((Wfun' (y - 1) : ℝ) : ℂ) * Efun t y with hF
  have h1 : (∫ y in (3/4:ℝ)..1, F y) = ∫ s in (-(1/4):ℝ)..0, F (s + 1) := by
    have h := intervalIntegral.integral_comp_add_right (a := (-(1/4):ℝ)) (b := (0:ℝ)) (f := F) 1
    have h' : (∫ x in (-(1/4):ℝ)..0, F (x + 1)) = ∫ x in (3/4:ℝ)..1, F x := by
      rw [h]; norm_num
    exact h'.symm
  have h2 : (∫ s in (-(1/4):ℝ)..0, F (s + 1))
      = ∫ s in (-(1/4):ℝ)..0, Complex.exp (-(t : ℂ) * Complex.I) * (Wfun' s • g (Wfun s)) := by
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    rw [Set.uIcc_of_le (by norm_num : (-(1/4):ℝ) ≤ 0)] at hs
    have hs' : s ∈ Set.Icc (-(1/4)) (1/4) := by
      rw [Set.mem_Icc] at hs ⊢; constructor <;> linarith [hs.1, hs.2]
    show ((Wfun' (s + 1 - 1) : ℝ) : ℂ) * Efun t (s + 1)
        = Complex.exp (-(t : ℂ) * Complex.I) * (Wfun' s • g (Wfun s))
    rw [show s + 1 - 1 = s by ring, show s + 1 = 1 + s by ring, Efun_phase hs', hg]
    simp only [Complex.real_smul]
    ring
  have h3 : (∫ s in (-(1/4):ℝ)..0, Complex.exp (-(t : ℂ) * Complex.I) * (Wfun' s • g (Wfun s)))
      = Complex.exp (-(t : ℂ) * Complex.I) * (∫ s in (-(1/4):ℝ)..0, Wfun' s • g (Wfun s)) :=
    intervalIntegral.integral_const_mul _ _
  have h4 : (∫ s in (-(1/4):ℝ)..0, Wfun' s • g (Wfun s))
      = ∫ u in Wfun (-(1/4))..Wfun (0:ℝ), g u := by
    have h := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg (a := (-(1/4):ℝ)) (b := (0:ℝ))
      (f := Wfun) (f' := Wfun') (g := g)
      (by
        rw [Set.uIcc_of_le (by norm_num : (-(1/4):ℝ) ≤ 0)]
        exact continuousOn_Wfun.mono (fun y hy => by
          rw [Set.mem_Icc] at hy ⊢; constructor <;> linarith [hy.1, hy.2]))
      (by
        intro x hx
        rw [min_eq_left (by norm_num : (-(1/4):ℝ) ≤ 0), max_eq_right (by norm_num)] at hx
        exact Wfun_hasDerivAt (by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]))
      (by
        intro x hx
        rw [min_eq_left (by norm_num : (-(1/4):ℝ) ≤ 0), max_eq_right (by norm_num)] at hx
        exact le_of_lt (Wfun'_pos (by rw [abs_le]; constructor <;> linarith [hx.1, hx.2])))
    simpa only [Function.comp_apply] using h
  have key : (∫ y in (3/4:ℝ)..1, F y)
      = Complex.exp (-(t : ℂ) * Complex.I) * (∫ u in Wfun (-(1/4))..(0:ℝ), g u) := by
    rw [h1, h2, h3, h4, Wfun_zero]
  simpa only [hF, hg] using key

/-- Fresnel approximation error on the right half. -/
lemma fresnel_right {t : ℝ} (ht : 0 < t) :
    ‖(∫ u in (0:ℝ)..Wfun (1/4), Complex.exp (-((t : ℂ) * Complex.I) * (u : ℂ) ^ 2))
      - ((Real.sqrt (Real.pi / t) / 2 : ℝ) : ℂ) * Complex.exp (-(Real.pi / 4) * Complex.I)‖
      ≤ 24 / t := by
  have hU : (0:ℝ) < Wfun (1/4) := lt_of_lt_of_le (by norm_num) Wfun_quarter
  have h := Commons.Analysis.Fresnel.fresnel_interval t (Wfun (1/4)) ht hU
  refine le_trans h ?_
  rw [div_le_iff₀ (mul_pos ht hU)]
  have h2 : (24:ℝ)/t * (t * Wfun (1/4)) = 24 * Wfun (1/4) := by field_simp
  rw [h2]
  nlinarith [Wfun_quarter]

/-- Fresnel approximation error on the left half. -/
lemma fresnel_left {t : ℝ} (ht : 0 < t) :
    ‖(∫ u in Wfun (-(1/4))..(0:ℝ), Complex.exp (-((t : ℂ) * Complex.I) * (u : ℂ) ^ 2))
      - ((Real.sqrt (Real.pi / t) / 2 : ℝ) : ℂ) * Complex.exp (-(Real.pi / 4) * Complex.I)‖
      ≤ 24 / t := by
  set g : ℝ → ℂ := fun u => Complex.exp (-((t : ℂ) * Complex.I) * (u : ℂ) ^ 2) with hg
  have heven : (∫ u in Wfun (-(1/4))..(0:ℝ), g u)
      = ∫ u in (0:ℝ)..(-Wfun (-(1/4))), g u := by
    have h := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := -Wfun (-(1/4))) (f := g)
    simp only [neg_neg, neg_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    show g (-x) = g x
    simp only [hg]
    have hxx : (((-x : ℝ)) : ℂ) ^ 2 = (((x : ℝ)) : ℂ) ^ 2 := by push_cast; ring
    rw [hxx]
  rw [heven]
  have hU : (0:ℝ) < -Wfun (-(1/4)) := by linarith [Wfun_neg_quarter]
  have h := Commons.Analysis.Fresnel.fresnel_interval t (-Wfun (-(1/4))) ht hU
  refine le_trans h ?_
  rw [div_le_iff₀ (mul_pos ht hU)]
  have h2 : (24:ℝ)/t * (t * -Wfun (-(1/4))) = 24 * -Wfun (-(1/4)) := by field_simp
  rw [h2]
  nlinarith [Wfun_neg_quarter]


/-- **Critical region.** The oscillatory integral over `[3/4, 5/4]` is the stationary-phase main
term plus an error of order `log t / t`. -/
lemma critical_region_bound {A : ℝ → ℂ} {t : ℝ} (ht : 2 ≤ t)
    (hA : ContDiff ℝ 1 A) (hAc : ∀ y, ‖A y‖ ≤ 1) (hAd : ∀ y, ‖deriv A y‖ ≤ 1) :
    ‖(∫ y in (3/4:ℝ)..(5/4), A y * Efun t y)
        - A 1 * Complex.exp (-(t : ℂ) * Complex.I)
            * ((Real.sqrt (2 * Real.pi / t) : ℝ) : ℂ) * Complex.exp (-(Real.pi / 4) * Complex.I)‖
      ≤ 1000 * (Real.log t / t) := by
  have ht0 : (0:ℝ) < t := by linarith
  set g : ℝ → ℂ := fun u => Complex.exp (-((t : ℂ) * Complex.I) * (u : ℂ) ^ 2) with hg
  set γ : ℝ → ℂ := fun y => A y - ((Real.sqrt 2 * A 1) * ((Wfun' (y - 1) : ℝ) : ℂ)) with hγ
  set Φ : ℂ := ((Real.sqrt (Real.pi / t) / 2 : ℝ) : ℂ) * Complex.exp (-(Real.pi / 4) * Complex.I)
    with hΦ
  set B : ℝ := (8 + 8 * Real.log t) / t with hB
  -- continuity of `γ` on the critical region
  have hγc : ContinuousOn γ (Set.Icc (3/4:ℝ) (5/4)) := by
    show ContinuousOn (fun y : ℝ => A y - ((Real.sqrt 2 * A 1) * ((Wfun' (y - 1) : ℝ) : ℂ)))
      (Set.Icc (3/4:ℝ) (5/4))
    exact hA.continuous.continuousOn.sub (ContinuousOn.mul continuousOn_const
      (Complex.continuous_ofReal.comp_continuousOn
        (continuousOn_Wfun'_sub_one (by norm_num) (by norm_num))))
  -- a subset computation
  have hsub : ∀ a b : ℝ, 3/4 ≤ a → a ≤ b → b ≤ 5/4 →
      Set.uIcc a b ⊆ Set.Icc (3/4:ℝ) (5/4) := by
    intro a b ha hab hb x hx
    rw [Set.uIcc_of_le hab] at hx
    rw [Set.mem_Icc] at hx ⊢
    exact ⟨by linarith [hx.1, ha], by linarith [hx.2, hb]⟩
  -- integrability of the three pieces
  have hAE : ∀ a b : ℝ, 3/4 ≤ a → a ≤ b → b ≤ 5/4 →
      IntervalIntegrable (fun y : ℝ => A y * Efun t y) volume a b := by
    intro a b ha hab hb
    exact (((hA.continuous.continuousOn).mul
      (continuousOn_Efun t (c := 3/4) (d := 5/4) (by norm_num : (0:ℝ) < 3/4))).mono
        (hsub a b ha hab hb)).intervalIntegrable
  have hγE : ∀ a b : ℝ, 3/4 ≤ a → a ≤ b → b ≤ 5/4 →
      IntervalIntegrable (fun y : ℝ => γ y * Efun t y) volume a b := by
    intro a b ha hab hb
    exact ((hγc.mul
      (continuousOn_Efun t (c := 3/4) (d := 5/4) (by norm_num : (0:ℝ) < 3/4))).mono
        (hsub a b ha hab hb)).intervalIntegrable
  have hWE : ∀ a b : ℝ, 3/4 ≤ a → a ≤ b → b ≤ 5/4 →
      IntervalIntegrable (fun y : ℝ => ((Wfun' (y - 1) : ℝ) : ℂ) * Efun t y) volume a b := by
    intro a b ha hab hb
    exact (((Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_Wfun'_sub_one (by linarith [ha]) (by linarith [hb]))).mul
      (continuousOn_Efun t (c := 3/4) (d := 5/4) (by norm_num : (0:ℝ) < 3/4))).mono
        (hsub a b ha hab hb)).intervalIntegrable
  -- the two halves
  have hRr : (∫ y in (1:ℝ)..(5/4), A y * Efun t y)
      = (∫ y in (1:ℝ)..(5/4), γ y * Efun t y)
        + (Real.sqrt 2 * A 1) * Complex.exp (-(t : ℂ) * Complex.I)
          * (∫ u in (0:ℝ)..Wfun (1/4), g u) := by
    have hcomp : (∫ y in (1:ℝ)..(5/4), A y * Efun t y)
        = (∫ y in (1:ℝ)..(5/4), γ y * Efun t y)
          + (Real.sqrt 2 * A 1)
            * (∫ y in (1:ℝ)..(5/4), ((Wfun' (y - 1) : ℝ) : ℂ) * Efun t y) := by
      rw [← intervalIntegral.integral_const_mul]
      rw [← intervalIntegral.integral_add]
      · refine intervalIntegral.integral_congr (fun y hy => ?_)
        show A y * Efun t y
            = γ y * Efun t y + (Real.sqrt 2 * A 1) * (((Wfun' (y - 1) : ℝ) : ℂ) * Efun t y)
        rw [hγ]; ring
      · exact hγE 1 (5/4) (by norm_num) (by norm_num) (by norm_num)
      · exact (hWE 1 (5/4) (by norm_num) (by norm_num) (by norm_num)).const_mul _
    have hsub2 : (∫ y in (1:ℝ)..(5/4), ((Wfun' (y - 1) : ℝ) : ℂ) * Efun t y)
        = Complex.exp (-(t : ℂ) * Complex.I) * (∫ u in (0:ℝ)..Wfun (1/4), g u) := by
      simpa only [hg] using subst_right t
    rw [hcomp, hsub2]; ring
  have hLr : (∫ y in (3/4:ℝ)..(1:ℝ), A y * Efun t y)
      = (∫ y in (3/4:ℝ)..(1:ℝ), γ y * Efun t y)
        + (Real.sqrt 2 * A 1) * Complex.exp (-(t : ℂ) * Complex.I)
          * (∫ u in Wfun (-(1/4))..(0:ℝ), g u) := by
    have hcomp : (∫ y in (3/4:ℝ)..(1:ℝ), A y * Efun t y)
        = (∫ y in (3/4:ℝ)..(1:ℝ), γ y * Efun t y)
          + (Real.sqrt 2 * A 1)
            * (∫ y in (3/4:ℝ)..(1:ℝ), ((Wfun' (y - 1) : ℝ) : ℂ) * Efun t y) := by
      rw [← intervalIntegral.integral_const_mul]
      rw [← intervalIntegral.integral_add]
      · refine intervalIntegral.integral_congr (fun y hy => ?_)
        show A y * Efun t y
            = γ y * Efun t y + (Real.sqrt 2 * A 1) * (((Wfun' (y - 1) : ℝ) : ℂ) * Efun t y)
        rw [hγ]; ring
      · exact hγE (3/4) 1 (by norm_num) (by norm_num) (by norm_num)
      · exact (hWE (3/4) 1 (by norm_num) (by norm_num) (by norm_num)).const_mul _
    have hsub2 : (∫ y in (3/4:ℝ)..(1:ℝ), ((Wfun' (y - 1) : ℝ) : ℂ) * Efun t y)
        = Complex.exp (-(t : ℂ) * Complex.I) * (∫ u in Wfun (-(1/4))..(0:ℝ), g u) := by
      simpa only [hg] using subst_left t
    rw [hcomp, hsub2]; ring
  -- the whole integral
  have hwhole : (∫ y in (3/4:ℝ)..(5/4), A y * Efun t y)
      = ((∫ y in (3/4:ℝ)..(1:ℝ), γ y * Efun t y) + (∫ y in (1:ℝ)..(5/4), γ y * Efun t y))
        + (Real.sqrt 2 * A 1) * Complex.exp (-(t : ℂ) * Complex.I)
          * ((∫ u in Wfun (-(1/4))..(0:ℝ), g u) + (∫ u in (0:ℝ)..Wfun (1/4), g u)) := by
    have hadj : (∫ y in (3/4:ℝ)..(1:ℝ), A y * Efun t y) + (∫ y in (1:ℝ)..(5/4), A y * Efun t y)
        = ∫ y in (3/4:ℝ)..(5/4), A y * Efun t y :=
      intervalIntegral.integral_add_adjacent_intervals
        (hAE (3/4) 1 (by norm_num) (by norm_num) (by norm_num))
        (hAE 1 (5/4) (by norm_num) (by norm_num) (by norm_num))
    rw [← hadj, hLr, hRr]
    ring
  -- the norm of the constant
  have hCn : ‖(Real.sqrt 2 * A 1) * Complex.exp (-(t : ℂ) * Complex.I)‖ ≤ Real.sqrt 2 := by
    rw [norm_mul, norm_mul]
    have h2 : ‖Complex.exp (-(t : ℂ) * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]; simp
    have h3 : ‖(((Real.sqrt 2 : ℝ)) : ℂ)‖ = Real.sqrt 2 := by simp [Real.sqrt_nonneg]
    rw [h2, mul_one, h3]
    calc Real.sqrt 2 * ‖A 1‖ ≤ Real.sqrt 2 * 1 :=
          mul_le_mul_of_nonneg_left (hAc 1) (Real.sqrt_nonneg 2)
      _ = Real.sqrt 2 := mul_one _
  -- main estimate
  have hEb : ‖(∫ y in (3/4:ℝ)..(5/4), A y * Efun t y)
        - (Real.sqrt 2 * A 1) * Complex.exp (-(t : ℂ) * Complex.I) * (Φ + Φ)‖
      ≤ 2 * ((1 + 4 * Real.sqrt 2) * B) + 48 * Real.sqrt 2 / t := by
    have hval : (∫ y in (3/4:ℝ)..(5/4), A y * Efun t y)
        - (Real.sqrt 2 * A 1) * Complex.exp (-(t : ℂ) * Complex.I) * (Φ + Φ)
        = ((∫ y in (3/4:ℝ)..(1:ℝ), γ y * Efun t y) + (∫ y in (1:ℝ)..(5/4), γ y * Efun t y))
          + (Real.sqrt 2 * A 1) * Complex.exp (-(t : ℂ) * Complex.I)
            * ((∫ u in Wfun (-(1/4))..(0:ℝ), g u) - Φ
               + ((∫ u in (0:ℝ)..Wfun (1/4), g u) - Φ)) := by
      rw [hwhole]; ring
    rw [hval]
    have ha : ‖(∫ y in (3/4:ℝ)..(1:ℝ), γ y * Efun t y)‖ ≤ (1 + 4 * Real.sqrt 2) * B := by
      rw [hB]; simpa only [hγ] using gamma_bound_left ht hA hAc hAd
    have hb : ‖(∫ y in (1:ℝ)..(5/4), γ y * Efun t y)‖ ≤ (1 + 4 * Real.sqrt 2) * B := by
      rw [hB]; simpa only [hγ] using gamma_bound_right ht hA hAc hAd
    have hc1 : ‖(∫ u in Wfun (-(1/4))..(0:ℝ), g u) - Φ‖ ≤ 24 / t := by
      rw [hΦ]; simpa only [hg] using fresnel_left ht0
    have hc2 : ‖(∫ u in (0:ℝ)..Wfun (1/4), g u) - Φ‖ ≤ 24 / t := by
      rw [hΦ]; simpa only [hg] using fresnel_right ht0
    calc ‖((∫ y in (3/4:ℝ)..(1:ℝ), γ y * Efun t y) + (∫ y in (1:ℝ)..(5/4), γ y * Efun t y))
          + (Real.sqrt 2 * A 1) * Complex.exp (-(t : ℂ) * Complex.I)
            * ((∫ u in Wfun (-(1/4))..(0:ℝ), g u) - Φ
               + ((∫ u in (0:ℝ)..Wfun (1/4), g u) - Φ))‖
        ≤ ‖(∫ y in (3/4:ℝ)..(1:ℝ), γ y * Efun t y)
            + (∫ y in (1:ℝ)..(5/4), γ y * Efun t y)‖
          + ‖(Real.sqrt 2 * A 1) * Complex.exp (-(t : ℂ) * Complex.I)
            * ((∫ u in Wfun (-(1/4))..(0:ℝ), g u) - Φ
               + ((∫ u in (0:ℝ)..Wfun (1/4), g u) - Φ))‖ := norm_add_le _ _
      _ ≤ ((1 + 4 * Real.sqrt 2) * B + (1 + 4 * Real.sqrt 2) * B)
            + Real.sqrt 2 * (24 / t + 24 / t) :=
          add_le_add (le_trans (norm_add_le _ _) (add_le_add ha hb))
            (le_trans (norm_mul_le _ _) (mul_le_mul hCn
              (le_trans (norm_add_le _ _) (add_le_add hc1 hc2))
              (norm_nonneg _) (Real.sqrt_nonneg 2)))
      _ = 2 * ((1 + 4 * Real.sqrt 2) * B) + 48 * Real.sqrt 2 / t := by ring
  -- the ideal term is the main term
  have hΦ2 : Φ + Φ
      = ((Real.sqrt (Real.pi / t) : ℝ) : ℂ) * Complex.exp (-(Real.pi / 4) * Complex.I) := by
    rw [hΦ]
    have h2 : (((Real.sqrt (Real.pi / t) / 2 : ℝ)) : ℂ)
        = ((Real.sqrt (Real.pi / t) : ℝ) : ℂ) / 2 := by push_cast; ring
    rw [h2]; ring
  have hsq : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt (Real.pi / t) : ℝ) : ℂ)
      = ((Real.sqrt (2 * Real.pi / t) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    rw [show (2 * Real.pi / t : ℝ) = 2 * (Real.pi / t) by ring,
        Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  have hideal : (Real.sqrt 2 * A 1) * Complex.exp (-(t : ℂ) * Complex.I) * (Φ + Φ)
      = A 1 * Complex.exp (-(t : ℂ) * Complex.I)
          * ((Real.sqrt (2 * Real.pi / t) : ℝ) : ℂ) * Complex.exp (-(Real.pi / 4) * Complex.I) := by
    rw [hΦ2]
    rw [show (Real.sqrt 2 * A 1) * Complex.exp (-(t : ℂ) * Complex.I)
          * (((Real.sqrt (Real.pi / t) : ℝ) : ℂ) * Complex.exp (-(Real.pi / 4) * Complex.I))
        = A 1 * Complex.exp (-(t : ℂ) * Complex.I)
          * (((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt (Real.pi / t) : ℝ) : ℂ))
          * Complex.exp (-(Real.pi / 4) * Complex.I) by ring, hsq]
  calc ‖(∫ y in (3/4:ℝ)..(5/4), A y * Efun t y)
        - A 1 * Complex.exp (-(t : ℂ) * Complex.I)
            * ((Real.sqrt (2 * Real.pi / t) : ℝ) : ℂ) * Complex.exp (-(Real.pi / 4) * Complex.I)‖
      = ‖(∫ y in (3/4:ℝ)..(5/4), A y * Efun t y)
          - (Real.sqrt 2 * A 1) * Complex.exp (-(t : ℂ) * Complex.I) * (Φ + Φ)‖ := by
        rw [hideal]
    _ ≤ 2 * ((1 + 4 * Real.sqrt 2) * B) + 48 * Real.sqrt 2 / t := hEb
    _ ≤ 1000 * (Real.log t / t) := by
        rw [hB]
        have hlog2 : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht
        have hlog2lb : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
        have hs : Real.sqrt 2 ≤ 3/2 := by
          nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
        have hsnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
        have hkey : 2 * ((1 + 4 * Real.sqrt 2) * ((8 + 8 * Real.log t) / t))
            + 48 * Real.sqrt 2 / t
            = (2 * (1 + 4 * Real.sqrt 2) * (8 + 8 * Real.log t) + 48 * Real.sqrt 2) / t := by
          field_simp
        rw [hkey, show (1000:ℝ) * (Real.log t / t) = (1000 * Real.log t) / t by ring,
          div_le_div_iff_of_pos_right ht0]
        nlinarith [hs, hsnn, hlog2, hlog2lb]


/-! ### 10. Support reduction, outer regions, and the main theorem -/

lemma intervalIntegral_eq_zero_of_vanishing {f : ℝ → ℂ} {p a : ℝ} (hpa : p ≤ a)
    (hf : ∀ y ∈ Set.Ioo p a, f y = 0) : (∫ y in p..a, f y) = 0 := by
  rw [← intervalIntegral.integral_zero]
  exact intervalIntegral.integral_congr_Ioo_of_le hpa (fun y hy => hf y hy)

lemma intervalIntegral_eq_of_vanishing_off {f : ℝ → ℂ} {a b p q : ℝ} (hpa : p ≤ a)
    (hab : a ≤ b) (hbq : b ≤ q) (hf : ∀ y, y ∉ Set.Icc a b → f y = 0)
    (h1 : IntervalIntegrable f volume p a) (h2 : IntervalIntegrable f volume a b)
    (h3 : IntervalIntegrable f volume b q) :
    (∫ y in a..b, f y) = ∫ y in p..q, f y := by
  have hpa0 : (∫ y in p..a, f y) = 0 :=
    intervalIntegral_eq_zero_of_vanishing hpa (fun y hy => hf y (fun hmem => by
      rw [Set.mem_Icc] at hmem; exact absurd hmem.1 (not_le.mpr hy.2)))
  have hbq0 : (∫ y in b..q, f y) = 0 :=
    intervalIntegral_eq_zero_of_vanishing hbq (fun y hy => hf y (fun hmem => by
      rw [Set.mem_Icc] at hmem; exact absurd hmem.2 (not_le.mpr hy.1)))
  have hpb : IntervalIntegrable f volume p b := h1.trans h2
  have hA1 := intervalIntegral.integral_add_adjacent_intervals h1 h2
  have hA2 := intervalIntegral.integral_add_adjacent_intervals hpb h3
  rw [← hA2, ← hA1, hpa0, hbq0]
  ring

lemma outer_bound_left {A : ℝ → ℂ} {t p : ℝ} (hA : ContDiff ℝ 1 A) (hAc : ∀ y, ‖A y‖ ≤ 1)
    (hAd : ∀ y, ‖deriv A y‖ ≤ 1) (ht : 0 < t) (hp : 1/2 ≤ p) (hp2 : p ≤ 3/4) :
    ‖∫ y in p..(3/4), A y * Efun t y‖ ≤ 240 / t := by
  have h := logphase_outer_bound (c := p) (d := (3/4:ℝ)) (t := t) (lam := 1/3) hp2 ht
    (by norm_num) hA hAc hAd ?_ ?_ ?_
  · refine le_trans h ?_
    rw [show (240:ℝ)/t = t⁻¹ * 240 by rw [div_eq_mul_inv, mul_comm]]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr ht.le)
    have he : 2 / (1/3:ℝ) + (3/4 - p) * (1/(1/3) + 4/(1/3)^2) = 6 + (3/4 - p) * 39 := by
      norm_num
    rw [he]
    nlinarith [hp2]
  · intro y hy
    rw [Set.mem_Icc] at hy
    have hy0 : (0:ℝ) < y := by linarith [hy.1, hp]
    have h1 : (1:ℝ)/3 ≤ 1/y - 1 := by
      have h2 : (1:ℝ)/y - 1 = (1 - y)/y := by field_simp
      rw [h2, le_div_iff₀ hy0]
      nlinarith [hy.2]
    rwa [abs_of_nonneg (by linarith)]
  · intro y hy
    rw [Set.mem_Icc] at hy
    linarith [hy.1, hp]
  · intro y hy
    rw [Set.mem_Icc] at hy
    have hy0 : (0:ℝ) < y := by linarith [hy.1, hp]
    rw [div_le_iff₀ (pow_pos hy0 2)]
    nlinarith [hy.1]

lemma outer_bound_right {A : ℝ → ℂ} {t q : ℝ} (hA : ContDiff ℝ 1 A) (hAc : ∀ y, ‖A y‖ ≤ 1)
    (hAd : ∀ y, ‖deriv A y‖ ≤ 1) (ht : 0 < t) (hq : 5/4 ≤ q) (hq6 : q ≤ 6) :
    ‖∫ y in (5/4)..q, A y * Efun t y‖ ≤ 535 / t := by
  have h := logphase_outer_bound (c := (5/4:ℝ)) (d := q) (t := t) (lam := 1/5) hq ht
    (by norm_num) hA hAc hAd ?_ ?_ ?_
  · refine le_trans h ?_
    rw [show (535:ℝ)/t = t⁻¹ * 535 by rw [div_eq_mul_inv, mul_comm]]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr ht.le)
    have he : 2 / (1/5:ℝ) + (q - 5/4) * (1/(1/5) + 4/(1/5)^2) = 10 + (q - 5/4) * 105 := by
      norm_num
    rw [he]
    nlinarith [hq6]
  · intro y hy
    rw [Set.mem_Icc] at hy
    have hy0 : (0:ℝ) < y := by linarith [hy.1]
    have h1 : (1:ℝ)/5 ≤ 1 - 1/y := by
      have h2 : 1 - (1:ℝ)/y = (y - 1)/y := by field_simp
      rw [h2, le_div_iff₀ hy0]
      nlinarith [hy.1]
    have habs : |1 / y - 1| = 1 - 1/y := by
      rw [abs_of_nonpos (by linarith)]; ring
    rw [habs]
    exact h1
  · intro y hy
    rw [Set.mem_Icc] at hy
    linarith [hy.1]
  · intro y hy
    rw [Set.mem_Icc] at hy
    have hy0 : (0:ℝ) < y := by linarith [hy.1]
    rw [div_le_iff₀ (pow_pos hy0 2)]
    nlinarith [hy.1]

/-- **Stationary phase for the log phase `h(y) = log y - y`.** -/
theorem log_phase_stationary_phase :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : ℝ → ℂ) (a b t : ℝ),
      (1/2 : ℝ) ≤ a → a < 1 → 1 < b → b ≤ 6 →
      ContDiff ℝ 2 A → (∀ y, y ∉ Set.Icc a b → A y = 0) →
      (∀ y, ‖A y‖ ≤ 1) → (∀ y, ‖deriv A y‖ ≤ 1) →
      2 ≤ t →
      ‖(∫ y in a..b, A y * Complex.exp (Complex.I * t * (Real.log y - y)))
        - A 1 * Complex.exp (-(t : ℂ) * Complex.I) * ((Real.sqrt (2 * Real.pi / t) : ℝ) : ℂ)
            * Complex.exp (-(Real.pi / 4) * Complex.I)‖
      ≤ C * (Real.log t / t) := by
  refine ⟨1000000, by norm_num, ?_⟩
  intro A a b t ha ha1 h1b hb6 hA hsupp hAc hAd ht
  have ht0 : (0:ℝ) < t := by linarith
  have hA1 : ContDiff ℝ 1 A := hA.of_le (by norm_num)
  set p : ℝ := min a (3/4) with hpdef
  set q : ℝ := max b (5/4) with hqdef
  have hpa : p ≤ a := min_le_left _ _
  have hp34 : p ≤ 3/4 := min_le_right _ _
  have hp12 : (1/2:ℝ) ≤ p := le_min ha (by norm_num)
  have hbq : b ≤ q := le_max_left _ _
  have hq54 : (5/4:ℝ) ≤ q := le_max_right _ _
  have hq6 : q ≤ 6 := max_le hb6 (by norm_num)
  have hab : a ≤ b := by linarith
  have hint : ∀ c d : ℝ, 1/2 ≤ c → c ≤ d → d ≤ 6 →
      IntervalIntegrable (fun y : ℝ => A y * Efun t y) volume c d := by
    intro c d hc hcd hd
    refine ((hA1.continuous.continuousOn.mul
      (continuousOn_Efun t (c := 1/2) (d := 6) (by norm_num : (0:ℝ) < 1/2))).mono
        ?_).intervalIntegrable
    intro y hy
    rw [Set.uIcc_of_le hcd] at hy
    rw [Set.mem_Icc] at hy ⊢
    exact ⟨by linarith [hy.1, hc], by linarith [hy.2, hd]⟩
  have hs : (∫ y in a..b, A y * Efun t y) = ∫ y in p..q, A y * Efun t y :=
    intervalIntegral_eq_of_vanishing_off hpa hab hbq (fun y hy => by
      rw [Efun]; exact mul_eq_zero_of_left (hsupp y hy) _)
      (hint p a hp12 hpa (by linarith)) (hint a b ha hab (by linarith))
      (hint b q (by linarith) hbq hq6)
  have hsplit : (∫ y in p..q, A y * Efun t y)
      = (∫ y in p..(3/4), A y * Efun t y) + (∫ y in (3/4)..(5/4), A y * Efun t y)
        + (∫ y in (5/4)..q, A y * Efun t y) := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (hint p (3/4) hp12 hp34 (by norm_num))
      (hint (3/4) (5/4) (by norm_num) (by norm_num) (by norm_num))
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      ((hint p (3/4) hp12 hp34 (by norm_num)).trans
        (hint (3/4) (5/4) (by norm_num) (by norm_num) (by norm_num)))
      (hint (5/4) q (by norm_num) hq54 hq6)
    rw [← h2, ← h1]
  have houtL := outer_bound_left (A := A) (t := t) (p := p) hA1 hAc hAd ht0 hp12 hp34
  have houtR := outer_bound_right (A := A) (t := t) (q := q) hA1 hAc hAd ht0 hq54 hq6
  have hcrit := critical_region_bound (A := A) (t := t) ht hA1 hAc hAd
  calc ‖(∫ y in a..b, A y * Efun t y)
        - A 1 * Complex.exp (-(t : ℂ) * Complex.I) * ((Real.sqrt (2 * Real.pi / t) : ℝ) : ℂ)
            * Complex.exp (-(Real.pi / 4) * Complex.I)‖
      = ‖((∫ y in p..(3/4), A y * Efun t y) + (∫ y in (5/4)..q, A y * Efun t y))
          + ((∫ y in (3/4)..(5/4), A y * Efun t y)
            - A 1 * Complex.exp (-(t : ℂ) * Complex.I) * ((Real.sqrt (2 * Real.pi / t) : ℝ) : ℂ)
              * Complex.exp (-(Real.pi / 4) * Complex.I))‖ := by
        rw [hs, hsplit]
        congr 1
        ring
    _ ≤ ‖(∫ y in p..(3/4), A y * Efun t y) + (∫ y in (5/4)..q, A y * Efun t y)‖
          + ‖(∫ y in (3/4)..(5/4), A y * Efun t y)
            - A 1 * Complex.exp (-(t : ℂ) * Complex.I) * ((Real.sqrt (2 * Real.pi / t) : ℝ) : ℂ)
              * Complex.exp (-(Real.pi / 4) * Complex.I)‖ := norm_add_le _ _
    _ ≤ (240/t + 535/t) + 1000*(Real.log t / t) := by
        refine add_le_add ?_ hcrit
        exact le_trans (norm_add_le _ _) (add_le_add houtL houtR)
    _ ≤ 1000000 * (Real.log t / t) := by
        have hlog2 : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht
        have hlog2lb : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
        rw [show (240:ℝ)/t + 535/t + 1000*(Real.log t/t) = (775 + 1000*Real.log t)/t by
              field_simp; ring,
          show (1000000:ℝ) * (Real.log t / t) = (1000000 * Real.log t)/t by ring,
          div_le_div_iff_of_pos_right ht0]
        nlinarith [hlog2, hlog2lb]


end
end Commons.Analysis.StationaryPhase