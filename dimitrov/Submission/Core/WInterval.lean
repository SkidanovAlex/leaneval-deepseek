import Mathlib

/-!
# D2-L3: every interval integral of `w_s` is at least the window integral

For `0 ≤ s < 1` and `a` with `cos a = s`, `0 ≤ a ≤ π/2`, set

    w_s(t) := (s - cos t) / (1 - 2s cos t + s²)   (= ∂G/∂q at q = s).

Then `w_s` is `2π`-periodic and even, and `w_s(t) < 0` exactly when
`cos t > s`, i.e. when `t ≡ u (mod 2π)` with `|u| < a`.  Its (odd) primitive
`W_s(t) := ∫_0^t w_s` is periodic (period-mean 0 for `s < 1`) with maximum
`C(s)/2` at `t ≡ -a` and minimum `-C(s)/2` at `t ≡ a`, where
`C(s) := -∫_{-a}^{a} w_s(t) dt > 0`.  Consequently for EVERY interval
`[u,v]` (u ≤ v):

    ∫_u^v w_s(t) dt = W_s(v) - W_s(u) ≥ -C(s) = ∫_{-a}^{a} w_s(t) dt,

i.e. the (centered) window integral is the minimum.  This is step L3 of the
D2 proof (see Submission/Core/D2.lean); it is where the "unimodality ⇒
superlevel is an interval" fact becomes effective, because any interval
achieves at least the window minimum (long intervals spanning several
windows pay positive "middles" that exactly cancel).

Proof method: for `s > 0` we use the explicit smooth global primitive
`φ_s(t) = arctan(s·sin t/(1 - s·cos t))` (= the continuous argument of
`1 - s·e^{-it}`).  One checks `w_s(t) = -(1/s)·dφ_s/dt` for every `t`, so

    ∫_u^v w_s = (φ_s(u) - φ_s(v))/s.

Since `1 - s·e^{-it}` stays in the half-plane `Re ≥ 1 - s > 0`, the argument
`φ_s` ranges in `(-π/2, π/2)`; its extrema are reached at the tangent points
of the circle `{1 - s·e^{-it}}` from the origin, i.e. `|φ_s(x)| ≤ π/2 - a`
(where `a = arccos s`).  This last bound is purely trigonometric:
`tan φ_s(x) ≤ tan(π/2 - a)` reduces to `cos(x - a) ≤ 1` (and, by oddness,
`φ_s(x) ≥ -(π/2 - a)` follows from `cos(x + a) ≤ 1`), both trivial.  The
case `s = 0` is the elementary `w_0 = -cos`, `∫_u^v w_0 = sin u - sin v ≥ -2`.

Prove the theorem below; you may add helper lemmas.  Do NOT change its
statement.  No sorries may remain in this file.
-/

noncomputable section

open scoped Real
open MeasureTheory
open Interval

namespace Submission.Core

/-- The integrand `w_s(t) = (s - cos t)/(1 - 2s cos t + s²)`. -/
private noncomputable def wInt (s t : ℝ) : ℝ :=
  (s - Real.cos t) / (1 - 2 * s * Real.cos t + s ^ 2)

/-- The explicit primitive of `-s·w_s`: the argument of `1 - s·e^{-it}`,
i.e. `φ_s(t) = arctan(s·sin t/(1 - s·cos t))`. -/
private noncomputable def phiInt (s t : ℝ) : ℝ :=
  Real.arctan (s * Real.sin t / (1 - s * Real.cos t))

/-- The denominator `1 - 2s cos t + s²` is positive for `0 ≤ s < 1`. -/
private lemma den_pos {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (t : ℝ) :
    0 < 1 - 2 * s * Real.cos t + s ^ 2 := by
  have hterm : 0 ≤ 2 * s * (1 - Real.cos t) := by
    exact mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hs0)
      (sub_nonneg.mpr (Real.cos_le_one t))
  have hrel : (1 - s) ^ 2 + 2 * s * (1 - Real.cos t) = 1 - 2 * s * Real.cos t + s ^ 2 := by ring
  have hsq : 0 < (1 - s) ^ 2 := by
    refine sq_pos_of_ne_zero ?_
    intro hzero
    have hpos : 0 < 1 - s := sub_pos.mpr hs1
    linarith
  nlinarith

/-- `1 - s cos t` is positive for `0 ≤ s < 1`. -/
private lemma one_sub_s_mul_cos_pos {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (t : ℝ) :
    0 < 1 - s * Real.cos t := by
  have hsc : s * Real.cos t ≤ s := by
    simpa using (mul_le_mul_of_nonneg_left (Real.cos_le_one t) hs0)
  exact sub_pos.mpr (lt_of_le_of_lt hsc hs1)

/-- `wInt s` is continuous on ℝ for `0 ≤ s < 1`. -/
private lemma continuous_wInt {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Continuous (fun t : ℝ => wInt s t) := by
  unfold wInt
  have hden : ∀ t : ℝ, 1 - 2 * s * Real.cos t + s ^ 2 ≠ 0 := fun t => (den_pos hs0 hs1 t).ne'
  apply Continuous.div (continuous_const.sub Real.continuous_cos) _ hden
  fun_prop

/-- `dφ/dt = s(cos t - s)/den` where `den = 1 - 2s cos t + s²`. -/
private lemma hasDerivAt_phiInt {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (t : ℝ) :
    HasDerivAt (fun x : ℝ => phiInt s x)
      (s * (Real.cos t - s) / (1 - 2 * s * Real.cos t + s ^ 2)) t := by
  unfold phiInt
  have hDne : 1 - s * Real.cos t ≠ 0 := ne_of_gt (one_sub_s_mul_cos_pos hs0 hs1 t)
  have hden : 1 - 2 * s * Real.cos t + s ^ 2 ≠ 0 := (den_pos hs0 hs1 t).ne'
  have hden2 : (1 - s * Real.cos t) ^ 2 + (s * Real.sin t) ^ 2 = 1 - 2 * s * Real.cos t + s ^ 2 := by
    have hsc2 : Real.sin t ^ 2 + Real.cos t ^ 2 = 1 := Real.sin_sq_add_cos_sq t
    nlinarith [hsc2]
  have hnz : (1 - s * Real.cos t) ^ 2 + (s * Real.sin t) ^ 2 ≠ 0 := by
    rw [hden2]
    exact hden
  refine ((Real.hasDerivAt_arctan (s * Real.sin t / (1 - s * Real.cos t))).comp t
      (((Real.hasDerivAt_sin t).const_mul s).div
        ((Real.hasDerivAt_cos t).const_mul s |>.const_sub (1 : ℝ)) hDne)).congr_deriv ?_
  rw [← hden2]
  field_simp [hDne, hnz]
  have hsc2 : Real.sin t ^ 2 + Real.cos t ^ 2 = 1 := Real.sin_sq_add_cos_sq t
  nlinarith [hsc2]

/-- For `0 < s < 1`, `wInt s = -(1/s)·dφ/dt` everywhere. -/
private lemma hasDerivAt_wInt {s : ℝ} (hs_pos : 0 < s) (hs1 : s < 1) (t : ℝ) :
    HasDerivAt (fun x : ℝ => -(1 / s) * phiInt s x) (wInt s t) t := by
  have hd := hasDerivAt_phiInt hs_pos.le hs1 t
  have hd' : HasDerivAt (fun x : ℝ => -(1 / s) * phiInt s x)
      (-(1 / s) * (s * (Real.cos t - s) / (1 - 2 * s * Real.cos t + s ^ 2))) t := by
    simpa using hd.const_mul (-(1 / s))
  convert hd' using 1
  unfold wInt
  field_simp [hs_pos.ne']
  ring

/-- The fundamental theorem for `wInt`: `∫_u^v wInt = (φ(u) - φ(v))/s`. -/
private lemma integral_wInt (s : ℝ) (hs_pos : 0 < s) (hs1 : s < 1) (u v : ℝ) :
    (∫ t in u..v, wInt s t) = (phiInt s u - phiInt s v) / s := by
  have hderiv : ∀ x ∈ Set.uIcc u v,
      HasDerivAt (fun y : ℝ => -(1 / s) * phiInt s y) (wInt s x) x := by
    intro x hx
    exact hasDerivAt_wInt hs_pos hs1 x
  have hint : IntervalIntegrable (wInt s) volume u v :=
    (continuous_wInt hs_pos.le hs1).intervalIntegrable u v
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  calc
    (∫ t in u..v, wInt s t) = -(1 / s) * phiInt s v - (-(1 / s) * phiInt s u) := hftc
    _ = (phiInt s u - phiInt s v) / s := by
      field_simp [hs_pos.ne']
      ring

/-- `φ` is odd in `t`. -/
private lemma phiInt_neg (s x : ℝ) : phiInt s (-x) = -phiInt s x := by
  unfold phiInt
  rw [Real.sin_neg, Real.cos_neg]
  rw [mul_neg, neg_div]
  rw [Real.arctan_neg]

/-- If `0 ≤ a` and `cos a = s < 1` then `0 < a`. -/
private lemma pos_of_cos_eq_lt_one {a s : ℝ} (ha0 : 0 ≤ a) (hs1 : s < 1)
    (hcos : Real.cos a = s) : 0 < a := by
  refine lt_of_le_of_ne ha0 ?_
  intro hEq
  have hcosval : Real.cos a = 1 := by
    have hEq' : a = 0 := by linarith
    rw [hEq']
    exact Real.cos_zero
  linarith

/-- If `a ≤ π/2` and `0 < cos a = s` then `a < π/2`. -/
private lemma lt_pi_div_two_of_cos_pos {a s : ℝ} (ha_le : a ≤ Real.pi / 2)
    (hs_pos : 0 < s) (hcos : Real.cos a = s) : a < Real.pi / 2 := by
  refine lt_of_le_of_ne ha_le ?_
  intro hEq
  have hcosval : Real.cos a = 0 := by
    have hEq' : a = Real.pi / 2 := by linarith
    rw [hEq']
    exact Real.cos_pi_div_two
  linarith

/-- Upper bound for the primitive's range: `φ_s(x) ≤ π/2 - a` for
`0 < s < 1`, `a = arccos s`.  (Geometric meaning: the circle
`1 - s e^{-it}` is seen from the origin under half-angle `≤ π/2 - a`.) -/
private lemma phiInt_le {s : ℝ} (hs_pos : 0 < s) (hs1 : s < 1) {a : ℝ} (ha0 : 0 ≤ a)
    (ha_pi : a < Real.pi / 2) (hcos : Real.cos a = s) (x : ℝ) :
    phiInt s x ≤ Real.pi / 2 - a := by
  have ha_pos : 0 < a := pos_of_cos_eq_lt_one ha0 hs1 hcos
  have ha_lt_pi : a < Real.pi := by nlinarith [ha_pi, Real.pi_pos]
  have hsa_pos : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha_pos ha_lt_pi
  have hden : 0 < 1 - s * Real.cos x := one_sub_s_mul_cos_pos hs_pos.le hs1 x
  have hc1 : Real.cos x * Real.cos a + Real.sin x * Real.sin a ≤ 1 := by
    rw [← Real.cos_sub]
    exact Real.cos_le_one (x - a)
  have hcore : Real.sin x * Real.sin a ≤ 1 - s * Real.cos x := by
    nlinarith [hc1, hcos]
  have hcross : (s * Real.sin x) * Real.sin a ≤ s * (1 - s * Real.cos x) := by
    have hm := mul_le_mul_of_nonneg_left hcore hs_pos.le
    simpa [mul_assoc] using hm
  have hy : s * Real.sin x / (1 - s * Real.cos x) ≤ s / Real.sin a := by
    exact (div_le_div_iff₀ hden hsa_pos).mpr hcross
  have hT : s / Real.sin a = Real.tan (Real.pi / 2 - a) := by
    rw [← hcos, Real.tan_pi_div_two_sub, Real.tan_eq_sin_div_cos, inv_div]
  have hlo : -(Real.pi / 2) < Real.pi / 2 - a := by nlinarith [ha_lt_pi]
  have hhi : Real.pi / 2 - a < Real.pi / 2 := by linarith [ha_pos]
  calc
    phiInt s x = Real.arctan (s * Real.sin x / (1 - s * Real.cos x)) := rfl
    _ ≤ Real.arctan (s / Real.sin a) := (Real.arctan_le_arctan_iff).2 hy
    _ = Real.arctan (Real.tan (Real.pi / 2 - a)) := by rw [hT]
    _ = Real.pi / 2 - a := Real.arctan_tan hlo hhi

/-- Lower bound for the primitive's range: `-(π/2 - a) ≤ φ_s(x)`. -/
private lemma phiInt_lower {s : ℝ} (hs_pos : 0 < s) (hs1 : s < 1) {a : ℝ} (ha0 : 0 ≤ a)
    (ha_pi : a < Real.pi / 2) (hcos : Real.cos a = s) (x : ℝ) :
    -(Real.pi / 2 - a) ≤ phiInt s x := by
  have hu := phiInt_le hs_pos hs1 ha0 ha_pi hcos (-x)
  have hneg : phiInt s (-x) = -phiInt s x := phiInt_neg s x
  linarith

/-- The range is exactly attained at `x = a`: `φ_s(a) = π/2 - a`. -/
private lemma phiInt_at_a {s : ℝ} (_hs_pos : 0 < s) (hs1 : s < 1) {a : ℝ} (ha0 : 0 ≤ a)
    (ha_pi : a < Real.pi / 2) (hcos : Real.cos a = s) :
    phiInt s a = Real.pi / 2 - a := by
  have ha_pos : 0 < a := pos_of_cos_eq_lt_one ha0 hs1 hcos
  have ha_lt_pi : a < Real.pi := by nlinarith [ha_pi, Real.pi_pos]
  have hsa_pos : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha_pos ha_lt_pi
  have hT : s * Real.sin a / (1 - s * Real.cos a) = Real.tan (Real.pi / 2 - a) := by
    rw [Real.tan_pi_div_two_sub, Real.tan_eq_sin_div_cos, inv_div]
    rw [← hcos]
    have hsq : 1 - (Real.cos a) ^ 2 = (Real.sin a) ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq a]
    rw [show Real.cos a * Real.cos a = (Real.cos a) ^ 2 by ring, hsq]
    field_simp [pow_ne_zero 2 hsa_pos.ne']
  have hlo : -(Real.pi / 2) < Real.pi / 2 - a := by nlinarith [ha_lt_pi]
  have hhi : Real.pi / 2 - a < Real.pi / 2 := by linarith [ha_pos]
  calc
    phiInt s a = Real.arctan (s * Real.sin a / (1 - s * Real.cos a)) := rfl
    _ = Real.arctan (Real.tan (Real.pi / 2 - a)) := by rw [hT]
    _ = Real.pi / 2 - a := Real.arctan_tan hlo hhi

/-- `sin a = 1` when `cos a = 0` and `0 ≤ a ≤ π/2` (so `a = π/2`). -/
private lemma sin_eq_one_of_cos_eq_zero_of_mem_Icc {a : ℝ} (ha0 : 0 ≤ a)
    (ha_le : a ≤ Real.pi / 2) (hcos : Real.cos a = 0) : Real.sin a = 1 := by
  have hsq : Real.sin a ^ 2 = 1 := by
    have := Real.sin_sq_add_cos_sq a
    nlinarith [hcos]
  have hnonneg : 0 ≤ Real.sin a := by
    exact Real.sin_nonneg_of_mem_Icc ⟨ha0, by nlinarith [ha_le, Real.pi_pos]⟩
  have hcases := sq_eq_one_iff.mp hsq
  rcases hcases with h1 | h2
  · exact h1
  · exfalso
    nlinarith [hnonneg]


/-- **Per-level minimum.**  For `0 ≤ s < 1` with `a = arccos s` (i.e.
`cos a = s`), every interval `[u,v]` satisfies
`∫_u^v w_s ≥ ∫_{-a}^{a} w_s`. -/
theorem w_interval_lower (s a : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (ha0 : 0 ≤ a) (hcos : Real.cos a = s) (ha_le : a ≤ Real.pi / 2) :
    ∀ ⦃u v : ℝ⦄, u ≤ v →
      (∫ t in u..v, (s - Real.cos t) / (1 - 2 * s * Real.cos t + s ^ 2)) ≥
        (∫ t in (-a)..a, (s - Real.cos t) / (1 - 2 * s * Real.cos t + s ^ 2)) := by
  intro u v huv
  rcases lt_or_eq_of_le hs0 with hs_pos | hs_eq
  · -- main case 0 < s
    have ha_pos : 0 < a := pos_of_cos_eq_lt_one ha0 hs1 hcos
    have ha_pi : a < Real.pi / 2 := lt_pi_div_two_of_cos_pos ha_le hs_pos hcos
    have hup : ∀ x : ℝ, phiInt s x ≤ Real.pi / 2 - a := phiInt_le hs_pos hs1 ha0 ha_pi hcos
    have hlo : ∀ x : ℝ, -(Real.pi / 2 - a) ≤ phiInt s x := phiInt_lower hs_pos hs1 ha0 ha_pi hcos
    have hA : phiInt s a = Real.pi / 2 - a := phiInt_at_a hs_pos hs1 ha0 ha_pi hcos
    have hAm : phiInt s (-a) = -(Real.pi / 2 - a) := by
      rw [phiInt_neg, hA]
    have hmain : (∫ t in u..v, wInt s t) ≥ (∫ t in (-a)..a, wInt s t) := by
      calc
        (∫ t in u..v, wInt s t) = (phiInt s u - phiInt s v) / s := integral_wInt s hs_pos hs1 u v
        _ ≥ (phiInt s (-a) - phiInt s a) / s := by
          apply div_le_div_of_nonneg_right ?_ hs_pos.le
          linarith [hlo u, hup v, hAm, hA]
        _ = (∫ t in (-a)..a, wInt s t) := (integral_wInt s hs_pos hs1 (-a) a).symm
    simpa [wInt] using hmain
  · -- case s = 0
    have hs0eq : s = 0 := hs_eq.symm
    have hsin1 : Real.sin a = 1 := by
      have hcos0 : Real.cos a = 0 := by simpa [hs0eq] using hcos
      exact sin_eq_one_of_cos_eq_zero_of_mem_Icc ha0 ha_le hcos0
    have hL : (∫ t in u..v, (s - Real.cos t) / (1 - 2 * s * Real.cos t + s ^ 2)) =
        Real.sin u - Real.sin v := by
      rw [hs0eq]
      simp
    have hR : (∫ t in (-a)..a, (s - Real.cos t) / (1 - 2 * s * Real.cos t + s ^ 2)) = -2 := by
      rw [hs0eq]
      simp [hsin1]
      ring
    rw [hL, hR]
    have h1 : -1 ≤ Real.sin u := Real.neg_one_le_sin u
    have h2 : -1 ≤ -Real.sin v := by linarith [Real.sin_le_one v]
    linarith

end Submission.Core

end
