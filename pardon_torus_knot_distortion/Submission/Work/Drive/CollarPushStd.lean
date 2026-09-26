import Submission.Work.Drive.CollarPushDefs

/-!
# The standard collar push: continuity and level properties

This file proves, for the explicit push `Work.Drive.pushStd` of the standard torus of revolution:

* `continuous_uncurry_pushStd` — joint continuity in `(x, δ)`;
* `meridVec_pushStd` — the exact effect of the push on the meridian vector: on the region
  `1/4 < ‖meridVec x‖ < 3/2` and for `|δ| ≤ 1/4`, the meridian vector is scaled by
  `(‖meridVec x‖ + δ · stdCut ‖meridVec x‖)/‖meridVec x‖` (so the longitude is unchanged and the
  meridian radius becomes `‖meridVec x‖ + δ · stdCut ‖meridVec x‖`);
* `pushStd_collar`, `pushStd_outer`, `pushStd_inner`, `pushStd_eq_self_of_ge` — the four level
  properties of the collar push of the standard torus.
-/

open LeanEval.KnotTheory.PardonDistortion
open Work.CoreTopology
open Set

namespace Work.Drive

noncomputable section

/-! ## Elementary bounds for the cutoff -/

/-- The displacement `δ · stdCut s` is at most `1/4` in absolute value when `|δ| ≤ 1/4`. -/
theorem abs_mul_stdCut_le {δ s : ℝ} (hδ : |δ| ≤ 1 / 4) : |δ * stdCut s| ≤ 1 / 4 := by
  rw [abs_mul, abs_of_nonneg (stdCut_nonneg s)]
  calc |δ| * stdCut s ≤ (1 / 4) * 1 :=
        mul_le_mul hδ (stdCut_le_one s) (stdCut_nonneg s) (by norm_num)
    _ = 1 / 4 := by norm_num

/-! ## The effect of the push on the meridian vector -/

/-- **The push is the exact flow of the meridian coordinate** on the region
`1/4 < ‖meridVec x‖ < 3/2`: for `|δ| ≤ 1/4` the meridian vector of `pushStd x δ` is `t/s` times
the meridian vector of `x`, where `s = ‖meridVec x‖` is the meridian radius and
`t = s + δ · stdCut s` the new one. -/
theorem meridVec_pushStd {x : R3} {δ : ℝ} (hδ : |δ| ≤ 1 / 4)
    (h1 : 1 / 4 < ‖meridVec x‖) (h2 : ‖meridVec x‖ < 3 / 2) :
    meridVec (pushStd x δ) =
      (((‖meridVec x‖ + δ * stdCut ‖meridVec x‖) / ‖meridVec x‖ : ℝ) : ℂ) * meridVec x := by
  have hs_pos : 0 < ‖meridVec x‖ := by linarith
  have hsq : (horizRadius x - 2) ^ 2 ≤ ‖meridVec x‖ ^ 2 := by
    have h := norm_meridVec_sq x
    rw [torusHeight_apply] at h
    nlinarith [sq_nonneg (x 2)]
  have hr_abs : |horizRadius x - 2| ≤ ‖meridVec x‖ := by
    have h := (sq_le_sq).mp hsq
    rwa [abs_of_nonneg (norm_nonneg (meridVec x))] at h
  have hr_lo : 1 / 2 ≤ horizRadius x := by
    have := (abs_le.mp hr_abs).1; linarith
  have hr_hi : horizRadius x ≤ 9 / 2 := by
    have := (abs_le.mp hr_abs).2; linarith
  have hr_pos : 0 < horizRadius x := by linarith
  have hcap : capDamp (horizRadius x) = 1 / horizRadius x := capDamp_eq_inv hr_lo hr_hi
  have hnu : cutDamp ‖meridVec x‖ = stdCut ‖meridVec x‖ / ‖meridVec x‖ :=
    cutDamp_eq_div hs_pos
  have hlamr : (1 + δ * cutDamp ‖meridVec x‖ * (1 - 2 * capDamp (horizRadius x))) * horizRadius x
      = 2 + (‖meridVec x‖ + δ * stdCut ‖meridVec x‖) * (horizRadius x - 2) / ‖meridVec x‖ := by
    rw [hcap, hnu]
    field_simp
    ring
  have ht_lo : 0 < ‖meridVec x‖ + δ * stdCut ‖meridVec x‖ := by
    have h := abs_mul_stdCut_le (s := ‖meridVec x‖) hδ
    have := neg_abs_le (δ * stdCut ‖meridVec x‖)
    linarith
  have ht_hi : ‖meridVec x‖ + δ * stdCut ‖meridVec x‖ < 2 := by
    have h := abs_mul_stdCut_le (s := ‖meridVec x‖) hδ
    have := le_abs_self (δ * stdCut ‖meridVec x‖)
    linarith
  have hr2 : -1 ≤ (horizRadius x - 2) / ‖meridVec x‖ := by
    rw [le_div_iff₀ hs_pos]
    linarith [(abs_le.mp hr_abs).1]
  have hlam_pos : 0 < 1 + δ * cutDamp ‖meridVec x‖ * (1 - 2 * capDamp (horizRadius x)) := by
    have hprod : (1 + δ * cutDamp ‖meridVec x‖ * (1 - 2 * capDamp (horizRadius x))) *
        horizRadius x > 0 := by
      rw [hlamr]
      have hrew : 2 + (‖meridVec x‖ + δ * stdCut ‖meridVec x‖) * (horizRadius x - 2) /
          ‖meridVec x‖ = 2 + (‖meridVec x‖ + δ * stdCut ‖meridVec x‖) *
            ((horizRadius x - 2) / ‖meridVec x‖) := by ring
      rw [hrew]
      nlinarith
    by_contra hle
    push Not at hle
    have := mul_nonpos_of_nonpos_of_nonneg hle (le_of_lt hr_pos)
    linarith
  have hhr : horizRadius (pushStd x δ) =
      |1 + δ * cutDamp ‖meridVec x‖ * (1 - 2 * capDamp (horizRadius x))| * horizRadius x := by
    have hsq' : horizRadiusSq (pushStd x δ) =
        (1 + δ * cutDamp ‖meridVec x‖ * (1 - 2 * capDamp (horizRadius x))) ^ 2 *
          horizRadiusSq x := by
      simp only [horizRadiusSq, pushStd_apply_zero, pushStd_apply_one]
      ring
    rw [horizRadius, hsq', Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, horizRadius]
  have hcoord0 : horizRadius (pushStd x δ) - 2 =
      (‖meridVec x‖ + δ * stdCut ‖meridVec x‖) / ‖meridVec x‖ * (horizRadius x - 2) := by
    rw [hhr, abs_of_pos hlam_pos, hlamr]
    ring
  have hcoord2 : pushStd x δ 2 =
      (‖meridVec x‖ + δ * stdCut ‖meridVec x‖) / ‖meridVec x‖ * x 2 := by
    rw [pushStd_apply_two, hnu]
    field_simp
  apply Complex.ext
  · simp only [meridVec_re, hcoord0, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  · simp only [meridVec_im, hcoord2, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero]

/-! ## The level properties -/

/-- On the collar `1/2 ≤ ‖meridVec x‖ ≤ 5/4` the push changes the meridian radius by exactly the
prescribed amount `δ`, for `|δ| ≤ 1/4`. -/
theorem pushStd_collar {x : R3} {δ : ℝ} (hx : ‖meridVec x‖ ∈ Set.Icc (1 / 2) (5 / 4))
    (hδ : |δ| ≤ 1 / 4) :
    ‖meridVec (pushStd x δ)‖ = ‖meridVec x‖ + δ := by
  obtain ⟨hx1, hx2⟩ := hx
  have h1 : 1 / 4 < ‖meridVec x‖ := by linarith
  have h2 : ‖meridVec x‖ < 3 / 2 := by linarith
  have hcut : stdCut ‖meridVec x‖ = 1 := stdCut_eq_one hx1 hx2
  rw [meridVec_pushStd hδ h1 h2, hcut, mul_one,
    Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hs : 0 < ‖meridVec x‖ := by linarith
  have hsδ : 0 < ‖meridVec x‖ + δ := by
    have := abs_le.mp hδ; linarith
  rw [abs_of_pos (div_pos hsδ hs), div_mul_cancel₀ _ (ne_of_gt hs)]

/-- Above the level `5/4` a forward push (`0 ≤ δ ≤ 1/4`) keeps the meridian radius at least `5/4`. -/
theorem pushStd_outer {x : R3} {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1 / 4)
    (h5 : 5 / 4 ≤ ‖meridVec x‖) : 5 / 4 ≤ ‖meridVec (pushStd x δ)‖ := by
  by_cases hge : (3 / 2 : ℝ) ≤ ‖meridVec x‖
  · rw [pushStd_eq_self_of_ge hge]; exact h5
  · have hlt : ‖meridVec x‖ < 3 / 2 := not_le.mp hge
    have h1' : 1 / 4 < ‖meridVec x‖ := by linarith
    have hδ : |δ| ≤ 1 / 4 := abs_le.mpr ⟨by linarith, h1⟩
    rw [meridVec_pushStd hδ h1' hlt, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hs : 0 < ‖meridVec x‖ := by linarith
    have hsc0 : 0 ≤ stdCut ‖meridVec x‖ := stdCut_nonneg _
    have ht : 0 < ‖meridVec x‖ + δ * stdCut ‖meridVec x‖ := by
      have := mul_nonneg h0 hsc0; linarith
    rw [abs_of_pos (div_pos ht hs), div_mul_cancel₀ _ (ne_of_gt hs)]
    have := mul_nonneg h0 hsc0
    linarith

/-- Below the level `1` a backward push (`-1/4 ≤ δ ≤ 0`) does not increase the meridian radius. -/
theorem pushStd_inner {x : R3} {δ : ℝ} (h0 : -1 / 4 ≤ δ) (h1 : δ ≤ 0)
    (hle : ‖meridVec x‖ ≤ 1) : ‖meridVec (pushStd x δ)‖ ≤ ‖meridVec x‖ := by
  by_cases hsmall : ‖meridVec x‖ ≤ 1 / 4
  · rw [pushStd_eq_self_of_le hsmall]
  · have h1' : 1 / 4 < ‖meridVec x‖ := not_le.mp hsmall
    have h2 : ‖meridVec x‖ < 3 / 2 := by linarith
    have hδ : |δ| ≤ 1 / 4 := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [meridVec_pushStd hδ h1' h2, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hs : 0 < ‖meridVec x‖ := by linarith
    have ht : 0 < ‖meridVec x‖ + δ * stdCut ‖meridVec x‖ := by
      have := abs_mul_stdCut_le (s := ‖meridVec x‖) hδ
      have := neg_abs_le (δ * stdCut ‖meridVec x‖)
      linarith
    rw [abs_of_pos (div_pos ht hs), div_mul_cancel₀ _ (ne_of_gt hs)]
    have hsc0 : 0 ≤ stdCut ‖meridVec x‖ := stdCut_nonneg _
    have := mul_nonpos_of_nonpos_of_nonneg h1 hsc0
    linarith

/-! ## Continuity -/

/-- The standard push is jointly continuous on `ℝ³ × ℝ`. -/
theorem continuous_uncurry_pushStd : Continuous (Function.uncurry pushStd) := by
  have h : Continuous (fun p : R3 × ℝ => fun i : Fin 3 =>
      (if i.val = 0 then
        (1 + p.2 * cutDamp ‖meridVec p.1‖ * (1 - 2 * capDamp (horizRadius p.1))) * p.1 0
       else if i.val = 1 then
        (1 + p.2 * cutDamp ‖meridVec p.1‖ * (1 - 2 * capDamp (horizRadius p.1))) * p.1 1
       else (1 + p.2 * cutDamp ‖meridVec p.1‖) * p.1 2 : ℝ)) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp h

end

end Work.Drive
