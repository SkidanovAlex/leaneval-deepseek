/-
# `Work.FITop4.Witness6.step9_props` — the analytic properties of the clamped nonic step

`Work.FITop4.Witness6.step9` (`Step9Defs`) is the clamped nonic Hermite step

  `step9 t = 0` for `t ≤ 0`, `= 1` for `1 ≤ t`, `= p9 t` on `[0,1]`,

with `p9 = 126t⁵ − 420t⁶ + 540t⁷ − 315t⁸ + 70t⁹ = 630∫₀ᵗ s⁴(1−s)⁴ ds`.  Since `p9` has a
five-fold zero at `0` and `p9 − 1` has a five-fold zero at `1`, clamping the polynomial to the
constants `0`, `1` outside `[0,1]` produces a `C⁴` function whose first four derivatives are the
clamped polynomials `p8 = p9'`, `p7 = p9''`, `p6 = p9'''`, `p5 = p9''''`.

This file proves the target

  `step9_props : ContDiff ℝ 4 step9 ∧ (0 ≤ step9 ≤ 1) ∧ step9 = 0 on (-∞,0] ∧ step9 = 1 on
   [1,∞) ∧ |deriv step9| ≤ 5/2 ∧ |deriv² step9| ≤ 25`.

The smoothness is obtained by gluing the one-sided derivatives at the two junction points `0` and
`1` (`Work.FITop4.Bump4.hasDerivAt_clamp`) and then identifying the iterated derivatives with the
clamped polynomials.  The bounds are explicit polynomial estimates: `p8 = 630 (t(1−t))⁴ ≤ 630/256`
and `p7 = 2520 (t(1−t))³(1−2t)` with `|p7| ≤ 2520·(t(1−t))³(1−2t(1−t)) ≤ 2520/128 < 25`.
-/
import Mathlib
import Submission.Work.FITop4.Witness6.Step9Defs
import Submission.Work.FITop4.Bump4.QuinticAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FITop4.Witness6

noncomputable section

open Work.FITop4.Bump4

/-! ## Derivatives of the underlying polynomials -/

lemma p9_hasDerivAt (x : ℝ) : HasDerivAt p9 (p8 x) x := by
  have h1 : HasDerivAt (fun t : ℝ => 126 * t ^ 5) (126 * (5 * x ^ 4)) x := by
    simpa using (hasDerivAt_pow 5 x).const_mul 126
  have h2 : HasDerivAt (fun t : ℝ => -420 * t ^ 6) ((-420) * (6 * x ^ 5)) x := by
    simpa using (hasDerivAt_pow 6 x).const_mul (-420)
  have h3 : HasDerivAt (fun t : ℝ => 540 * t ^ 7) (540 * (7 * x ^ 6)) x := by
    simpa using (hasDerivAt_pow 7 x).const_mul 540
  have h4 : HasDerivAt (fun t : ℝ => -315 * t ^ 8) ((-315) * (8 * x ^ 7)) x := by
    simpa using (hasDerivAt_pow 8 x).const_mul (-315)
  have h5 : HasDerivAt (fun t : ℝ => 70 * t ^ 9) (70 * (9 * x ^ 8)) x := by
    simpa using (hasDerivAt_pow 9 x).const_mul 70
  have h := (((h1.add h2).add h3).add h4).add h5
  have hfun : ((fun t : ℝ => 126 * t^5) + (fun t : ℝ => -420 * t^6) + (fun t : ℝ => 540 * t^7)
      + (fun t : ℝ => -315 * t^8) + (fun t : ℝ => 70 * t^9)) = p9 := by
    funext t; simp only [Pi.add_apply]; unfold p9; ring
  have hval : 126 * (5 * x^4) + (-420) * (6 * x^5) + 540 * (7 * x^6) + (-315) * (8 * x^7)
      + 70 * (9 * x^8) = p8 x := by
    unfold p8; ring
  rw [hfun, hval] at h
  exact h

lemma p8_hasDerivAt (x : ℝ) : HasDerivAt p8 (p7 x) x := by
  have h1 : HasDerivAt (fun t : ℝ => 630 * t ^ 4) (630 * (4 * x ^ 3)) x := by
    simpa using (hasDerivAt_pow 4 x).const_mul 630
  have h2 : HasDerivAt (fun t : ℝ => -2520 * t ^ 5) ((-2520) * (5 * x ^ 4)) x := by
    simpa using (hasDerivAt_pow 5 x).const_mul (-2520)
  have h3 : HasDerivAt (fun t : ℝ => 3780 * t ^ 6) (3780 * (6 * x ^ 5)) x := by
    simpa using (hasDerivAt_pow 6 x).const_mul 3780
  have h4 : HasDerivAt (fun t : ℝ => -2520 * t ^ 7) ((-2520) * (7 * x ^ 6)) x := by
    simpa using (hasDerivAt_pow 7 x).const_mul (-2520)
  have h5 : HasDerivAt (fun t : ℝ => 630 * t ^ 8) (630 * (8 * x ^ 7)) x := by
    simpa using (hasDerivAt_pow 8 x).const_mul 630
  have h := (((h1.add h2).add h3).add h4).add h5
  have hfun : ((fun t : ℝ => 630 * t^4) + (fun t : ℝ => -2520 * t^5) + (fun t : ℝ => 3780 * t^6)
      + (fun t : ℝ => -2520 * t^7) + (fun t : ℝ => 630 * t^8)) = p8 := by
    funext t; simp only [Pi.add_apply]; unfold p8; ring
  have hval : 630 * (4 * x^3) + (-2520) * (5 * x^4) + 3780 * (6 * x^5) + (-2520) * (7 * x^6)
      + 630 * (8 * x^7) = p7 x := by
    unfold p7; ring
  rw [hfun, hval] at h
  exact h

lemma p7_hasDerivAt (x : ℝ) : HasDerivAt p7 (p6 x) x := by
  have h1 : HasDerivAt (fun t : ℝ => 2520 * t ^ 3) (2520 * (3 * x ^ 2)) x := by
    simpa using (hasDerivAt_pow 3 x).const_mul 2520
  have h2 : HasDerivAt (fun t : ℝ => -12600 * t ^ 4) ((-12600) * (4 * x ^ 3)) x := by
    simpa using (hasDerivAt_pow 4 x).const_mul (-12600)
  have h3 : HasDerivAt (fun t : ℝ => 22680 * t ^ 5) (22680 * (5 * x ^ 4)) x := by
    simpa using (hasDerivAt_pow 5 x).const_mul 22680
  have h4 : HasDerivAt (fun t : ℝ => -17640 * t ^ 6) ((-17640) * (6 * x ^ 5)) x := by
    simpa using (hasDerivAt_pow 6 x).const_mul (-17640)
  have h5 : HasDerivAt (fun t : ℝ => 5040 * t ^ 7) (5040 * (7 * x ^ 6)) x := by
    simpa using (hasDerivAt_pow 7 x).const_mul 5040
  have h := (((h1.add h2).add h3).add h4).add h5
  have hfun : ((fun t : ℝ => 2520 * t^3) + (fun t : ℝ => -12600 * t^4) + (fun t : ℝ => 22680 * t^5)
      + (fun t : ℝ => -17640 * t^6) + (fun t : ℝ => 5040 * t^7)) = p7 := by
    funext t; simp only [Pi.add_apply]; unfold p7; ring
  have hval : 2520 * (3 * x^2) + (-12600) * (4 * x^3) + 22680 * (5 * x^4) + (-17640) * (6 * x^5)
      + 5040 * (7 * x^6) = p6 x := by
    unfold p6; ring
  rw [hfun, hval] at h
  exact h

lemma p6_hasDerivAt (x : ℝ) : HasDerivAt p6 (p5 x) x := by
  have h1 : HasDerivAt (fun t : ℝ => 7560 * t ^ 2) (7560 * (2 * x ^ 1)) x := by
    simpa using (hasDerivAt_pow 2 x).const_mul 7560
  have h2 : HasDerivAt (fun t : ℝ => -50400 * t ^ 3) ((-50400) * (3 * x ^ 2)) x := by
    simpa using (hasDerivAt_pow 3 x).const_mul (-50400)
  have h3 : HasDerivAt (fun t : ℝ => 113400 * t ^ 4) (113400 * (4 * x ^ 3)) x := by
    simpa using (hasDerivAt_pow 4 x).const_mul 113400
  have h4 : HasDerivAt (fun t : ℝ => -105840 * t ^ 5) ((-105840) * (5 * x ^ 4)) x := by
    simpa using (hasDerivAt_pow 5 x).const_mul (-105840)
  have h5 : HasDerivAt (fun t : ℝ => 35280 * t ^ 6) (35280 * (6 * x ^ 5)) x := by
    simpa using (hasDerivAt_pow 6 x).const_mul 35280
  have h := (((h1.add h2).add h3).add h4).add h5
  have hfun : ((fun t : ℝ => 7560 * t^2) + (fun t : ℝ => -50400 * t^3) + (fun t : ℝ => 113400 * t^4)
      + (fun t : ℝ => -105840 * t^5) + (fun t : ℝ => 35280 * t^6)) = p6 := by
    funext t; simp only [Pi.add_apply]; unfold p6; ring
  have hval : 7560 * (2 * x^1) + (-50400) * (3 * x^2) + 113400 * (4 * x^3) + (-105840) * (5 * x^4)
      + 35280 * (6 * x^5) = p5 x := by
    unfold p5; ring
  rw [hfun, hval] at h
  exact h

/-! ## Values of the polynomials at the two junction points -/

lemma p9_zero : p9 0 = 0 := by unfold p9; norm_num
lemma p9_one : p9 1 = 1 := by unfold p9; norm_num
lemma p8_zero : p8 0 = 0 := by unfold p8; norm_num
lemma p8_one : p8 1 = 0 := by unfold p8; norm_num
lemma p7_zero : p7 0 = 0 := by unfold p7; norm_num
lemma p7_one : p7 1 = 0 := by unfold p7; norm_num
lemma p6_zero : p6 0 = 0 := by unfold p6; norm_num
lemma p6_one : p6 1 = 0 := by unfold p6; norm_num
lemma p5_zero : p5 0 = 0 := by unfold p5; norm_num
lemma p5_one : p5 1 = 0 := by unfold p5; norm_num

/-! ## The clamped derivative chain -/

lemma step9_hasDerivAt (x : ℝ) : HasDerivAt step9 (st8 x) x := by
  have hq : step9 = (fun t : ℝ => if t ≤ 0 then (0:ℝ) else if 1 ≤ t then 1 else p9 t) := by
    funext t; unfold step9; rfl
  rw [hq]
  exact hasDerivAt_clamp (p := p9) (p' := p8) (c0 := 0) (c1 := 1)
    p9_hasDerivAt p9_zero p9_one p8_zero p8_one x

lemma st8_hasDerivAt (x : ℝ) : HasDerivAt st8 (st7 x) x := by
  have hq : st8 = (fun t : ℝ => if t ≤ 0 then (0:ℝ) else if 1 ≤ t then 0 else p8 t) := by
    funext t; unfold st8; rfl
  rw [hq]
  exact hasDerivAt_clamp (p := p8) (p' := p7) (c0 := 0) (c1 := 0)
    p8_hasDerivAt p8_zero p8_one p7_zero p7_one x

lemma st7_hasDerivAt (x : ℝ) : HasDerivAt st7 (st6 x) x := by
  have hq : st7 = (fun t : ℝ => if t ≤ 0 then (0:ℝ) else if 1 ≤ t then 0 else p7 t) := by
    funext t; unfold st7; rfl
  rw [hq]
  exact hasDerivAt_clamp (p := p7) (p' := p6) (c0 := 0) (c1 := 0)
    p7_hasDerivAt p7_zero p7_one p6_zero p6_one x

lemma st6_hasDerivAt (x : ℝ) : HasDerivAt st6 (st5 x) x := by
  have hq : st6 = (fun t : ℝ => if t ≤ 0 then (0:ℝ) else if 1 ≤ t then 0 else p6 t) := by
    funext t; unfold st6; rfl
  rw [hq]
  exact hasDerivAt_clamp (p := p6) (p' := p5) (c0 := 0) (c1 := 0)
    p6_hasDerivAt p6_zero p6_one p5_zero p5_one x

/-! ## Continuity of the clamped functions -/

/-- **Continuity of a clamped function.**  If `p` is continuous and takes the values `c0`, `c1` at
`0`, `1`, then the function which is `c0` on `(-∞,0]`, `c1` on `[1,∞)` and `p` in between is
continuous. -/
lemma continuous_clamp {p : ℝ → ℝ} {c0 c1 : ℝ} (hp : Continuous p)
    (h0 : p 0 = c0) (h1 : p 1 = c1) :
    Continuous (fun t : ℝ => if t ≤ 0 then c0 else if 1 ≤ t then c1 else p t) := by
  have hIcc : ContinuousOn (fun t : ℝ => if t ≤ 0 then c0 else if 1 ≤ t then c1 else p t)
      (Set.Icc (0:ℝ) 1) := by
    apply ContinuousOn.congr hp.continuousOn
    intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    show (if t ≤ 0 then c0 else if 1 ≤ t then c1 else p t) = p t
    by_cases h : t ≤ 0
    · rw [if_pos h]
      have : t = 0 := le_antisymm h ht0
      subst this; exact h0.symm
    · rw [if_neg h]
      by_cases h' : 1 ≤ t
      · rw [if_pos h']
        have : t = 1 := le_antisymm ht1 h'
        subst this; exact h1.symm
      · rw [if_neg h']
  have hIci1 : ContinuousOn (fun t : ℝ => if t ≤ 0 then c0 else if 1 ≤ t then c1 else p t)
      (Set.Ici (1:ℝ)) := by
    refine ContinuousOn.congr (f := fun _ : ℝ => c1) continuousOn_const ?_
    intro t ht
    rw [Set.mem_Ici] at ht
    show (if t ≤ 0 then c0 else if 1 ≤ t then c1 else p t) = c1
    rw [if_neg (by linarith : ¬ t ≤ 0), if_pos ht]
  have hIic0 : ContinuousOn (fun t : ℝ => if t ≤ 0 then c0 else if 1 ≤ t then c1 else p t)
      (Set.Iic (0:ℝ)) := by
    refine ContinuousOn.congr (f := fun _ : ℝ => c0) continuousOn_const ?_
    intro t ht
    rw [Set.mem_Iic] at ht
    show (if t ≤ 0 then c0 else if 1 ≤ t then c1 else p t) = c0
    rw [if_pos ht]
  have hIci0 : ContinuousOn (fun t : ℝ => if t ≤ 0 then c0 else if 1 ≤ t then c1 else p t)
      (Set.Ici (0:ℝ)) := by
    have hun := ContinuousOn.union_of_isClosed hIcc hIci1 isClosed_Icc isClosed_Ici
    rwa [Set.Icc_union_Ici (a := (0:ℝ)) (b := 1) (c := 1) (by norm_num),
      min_eq_left (by norm_num)] at hun
  have hun := ContinuousOn.union_of_isClosed hIic0 hIci0 isClosed_Iic isClosed_Ici
  rw [Set.Iic_union_Ici (a := (0:ℝ))] at hun
  exact continuousOn_univ.mp hun

lemma continuous_step9 : Continuous step9 := by
  rw [show step9 = (fun t : ℝ => if t ≤ 0 then (0:ℝ) else if 1 ≤ t then 1 else p9 t) from by
    funext t; unfold step9; rfl]
  exact continuous_clamp (by unfold p9; fun_prop) p9_zero p9_one

lemma continuous_st8 : Continuous st8 := by
  rw [show st8 = (fun t : ℝ => if t ≤ 0 then (0:ℝ) else if 1 ≤ t then 0 else p8 t) from by
    funext t; unfold st8; rfl]
  exact continuous_clamp (by unfold p8; fun_prop) p8_zero p8_one

lemma continuous_st7 : Continuous st7 := by
  rw [show st7 = (fun t : ℝ => if t ≤ 0 then (0:ℝ) else if 1 ≤ t then 0 else p7 t) from by
    funext t; unfold st7; rfl]
  exact continuous_clamp (by unfold p7; fun_prop) p7_zero p7_one

lemma continuous_st6 : Continuous st6 := by
  rw [show st6 = (fun t : ℝ => if t ≤ 0 then (0:ℝ) else if 1 ≤ t then 0 else p6 t) from by
    funext t; unfold st6; rfl]
  exact continuous_clamp (by unfold p6; fun_prop) p6_zero p6_one

lemma continuous_st5 : Continuous st5 := by
  rw [show st5 = (fun t : ℝ => if t ≤ 0 then (0:ℝ) else if 1 ≤ t then 0 else p5 t) from by
    funext t; unfold st5; rfl]
  exact continuous_clamp (by unfold p5; fun_prop) p5_zero p5_one

/-! ## The derivative identifications -/

lemma deriv_step9 : deriv step9 = st8 := funext (fun x => (step9_hasDerivAt x).deriv)
lemma deriv_st8 : deriv st8 = st7 := funext (fun x => (st8_hasDerivAt x).deriv)
lemma deriv_st7 : deriv st7 = st6 := funext (fun x => (st7_hasDerivAt x).deriv)
lemma deriv_st6 : deriv st6 = st5 := funext (fun x => (st6_hasDerivAt x).deriv)

/-! ## Values and bounds of `step9` and its derivatives -/

/-- The middle branch `p9` is nonnegative on `[0,1]`: it is `630 ∫₀ᵗ s⁴(1−s)⁴ ds`. -/
lemma p9_nonneg (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 ≤ p9 t := by
  have hr : 1 ≤ 56 - 140*t + 120*t^2 - 35*t^3 := by
    have h : 56 - 140*t + 120*t^2 - 35*t^3 - 1 = 5*(1-t)*(7*t^2 - 17*t + 11) := by ring
    have h2 : 0 ≤ (t - 1)*(7*t - 10) := by nlinarith
    have h3 : 1 ≤ 7*t^2 - 17*t + 11 := by nlinarith
    have h4 : 0 ≤ 1 - t := by linarith
    nlinarith [h]
  have hfac : p9 t = t^5 * (70*(t-1)^4 + (56 - 140*t + 120*t^2 - 35*t^3)) := by
    unfold p9; ring
  have ht5 : 0 ≤ t^5 := pow_nonneg ht0 5
  have h4 : 0 ≤ 70*(t-1)^4 := by positivity
  rw [hfac]
  exact mul_nonneg ht5 (by linarith)

lemma p9_le_one (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : p9 t ≤ 1 := by
  have h := p9_nonneg (1 - t) (by linarith) (by linarith)
  have hid : p9 t + p9 (1 - t) = 1 := by unfold p9; ring
  linarith

lemma step9_mem01 (t : ℝ) : 0 ≤ step9 t ∧ step9 t ≤ 1 := by
  unfold step9
  by_cases h : t ≤ 0
  · rw [if_pos h]; norm_num
  · rw [if_neg h]
    by_cases h' : 1 ≤ t
    · rw [if_pos h']; norm_num
    · rw [if_neg h']
      exact ⟨p9_nonneg t (not_le.mp h).le (not_le.mp h').le,
        p9_le_one t (not_le.mp h).le (not_le.mp h').le⟩

lemma step9_eq_zero (t : ℝ) (ht : t ≤ 0) : step9 t = 0 := by
  unfold step9; rw [if_pos ht]

lemma step9_eq_one (t : ℝ) (ht : 1 ≤ t) : step9 t = 1 := by
  unfold step9
  rw [if_neg (by linarith : ¬ t ≤ 0), if_pos ht]

lemma abs_p8_le (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : |p8 t| ≤ 5 / 2 := by
  have h1 : 0 ≤ t * (1 - t) := by nlinarith
  have h2 : t * (1 - t) ≤ 1 / 4 := by nlinarith [sq_nonneg (t - 1/2)]
  have h3 : (t*(1-t))^4 ≤ (1/4)^4 := pow_le_pow_left₀ h1 h2 4
  have h4 : p8 t = 630 * (t*(1-t))^4 := by unfold p8; ring
  rw [h4, abs_of_nonneg (by positivity)]
  nlinarith

lemma abs_p7_le (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : |p7 t| ≤ 25 := by
  have h1 : 0 ≤ t * (1 - t) := by nlinarith
  have h2 : t * (1 - t) ≤ 1/4 := by nlinarith [sq_nonneg (t - 1/2)]
  have h5 : (t*(1-t))^5 ≤ (1/4)^5 := pow_le_pow_left₀ h1 h2 5
  have h6 : (t*(1-t)) * (1 - 4*(t*(1-t))) ≤ 1/16 := by
    nlinarith [sq_nonneg (t*(1-t) - 1/8)]
  have h6' : 0 ≤ (t*(1-t)) * (1 - 4*(t*(1-t))) := by nlinarith
  have h7 : p7 t ^ 2 = 6350400 * ((t*(1-t))^5 * ((t*(1-t)) * (1-4*(t*(1-t))))) := by
    unfold p7; ring
  have h8 : p7 t ^ 2 ≤ 6350400 * ((1/4)^5 * (1/16)) := by
    rw [h7]
    exact mul_le_mul_of_nonneg_left (mul_le_mul h5 h6 h6' (by norm_num)) (by norm_num)
  have h9 : p7 t ^ 2 ≤ (25:ℝ)^2 := by nlinarith
  exact abs_le_of_sq_le_sq h9 (by norm_num)

lemma abs_st8_le (t : ℝ) : |st8 t| ≤ 5 / 2 := by
  unfold st8
  by_cases h : t ≤ 0
  · rw [if_pos h]; norm_num
  · rw [if_neg h]
    by_cases h' : 1 ≤ t
    · rw [if_pos h']; norm_num
    · rw [if_neg h']
      exact abs_p8_le t (not_le.mp h).le (not_le.mp h').le

lemma abs_st7_le (t : ℝ) : |st7 t| ≤ 25 := by
  unfold st7
  by_cases h : t ≤ 0
  · rw [if_pos h]; norm_num
  · rw [if_neg h]
    by_cases h' : 1 ≤ t
    · rw [if_pos h']; norm_num
    · rw [if_neg h']
      exact abs_p7_le t (not_le.mp h).le (not_le.mp h').le

/-! ## `C⁴`-regularity -/

lemma step9_contDiff4 : ContDiff ℝ 4 step9 := by
  have hd1 : Differentiable ℝ step9 := fun x => (step9_hasDerivAt x).differentiableAt
  have hd2 : Differentiable ℝ st8 := fun x => (st8_hasDerivAt x).differentiableAt
  have hd3 : Differentiable ℝ st7 := fun x => (st7_hasDerivAt x).differentiableAt
  have hd4 : Differentiable ℝ st6 := fun x => (st6_hasDerivAt x).differentiableAt
  have hi1 : iteratedDeriv 1 step9 = st8 := by
    rw [iteratedDeriv_one]; exact deriv_step9
  have hi2 : iteratedDeriv 2 step9 = st7 := by
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, deriv_step9,
      deriv_st8]
  have hi3 : iteratedDeriv 3 step9 = st6 := by
    rw [show (3:ℕ) = 2 + 1 from rfl, iteratedDeriv_succ, hi2, deriv_st7]
  have hi4 : iteratedDeriv 4 step9 = st5 := by
    rw [show (4:ℕ) = 3 + 1 from rfl, iteratedDeriv_succ, hi3, deriv_st6]
  refine (contDiff_nat_iff_iteratedDeriv (n := 4)).mpr ⟨?_, ?_⟩
  · intro m hm
    interval_cases m
    · rw [iteratedDeriv_zero]; exact continuous_step9
    · rw [hi1]; exact continuous_st8
    · rw [hi2]; exact continuous_st7
    · rw [hi3]; exact continuous_st6
    · rw [hi4]; exact continuous_st5
  · intro m hm
    interval_cases m
    · rw [iteratedDeriv_zero]; exact hd1
    · rw [hi1]; exact hd2
    · rw [hi2]; exact hd3
    · rw [hi3]; exact hd4

end

/-- The clamped nonic step `step9` is `C⁴`, takes values in `[0,1]`, equals `0` on `(-∞,0]` and
`1` on `[1,∞)`, and its first two derivatives are bounded by `5/2` and `25`. -/
theorem step9_props :
    ContDiff ℝ 4 Work.FITop4.Witness6.step9 ∧
    (∀ t : ℝ, 0 ≤ Work.FITop4.Witness6.step9 t ∧ Work.FITop4.Witness6.step9 t ≤ 1) ∧
    (∀ t : ℝ, t ≤ 0 → Work.FITop4.Witness6.step9 t = 0) ∧
    (∀ t : ℝ, 1 ≤ t → Work.FITop4.Witness6.step9 t = 1) ∧
    (∀ t : ℝ, |deriv Work.FITop4.Witness6.step9 t| ≤ 5 / 2) ∧
    (∀ t : ℝ, |deriv (deriv Work.FITop4.Witness6.step9) t| ≤ 25) := by
  refine ⟨step9_contDiff4, fun t => step9_mem01 t, fun t ht => step9_eq_zero t ht,
    fun t ht => step9_eq_one t ht, fun t => ?_, fun t => ?_⟩
  · rw [deriv_step9]; exact abs_st8_le t
  · rw [deriv_step9, deriv_st8]; exact abs_st7_le t

end Work.FITop4.Witness6
