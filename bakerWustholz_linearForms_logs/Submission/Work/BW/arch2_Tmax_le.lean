import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Tangent-line form of the key growth estimate: if `C > 0` and `C e^{-h} ≤ log C`, then
`log (1 + t) ≤ (h - 1) + (C e^{-h}) t` for every `t ≥ 0`.

Proof: the tangent-line inequality `log x ≤ log u + x/u - 1` at `u = 1/(C e^{-h})` gives
`log (1 + t) ≤ log (1/λ) + λ + λ t - 1` with `λ = C e^{-h}`, and `log (1/λ) = h - log C`, so
the hypothesis `λ ≤ log C` turns this into the claim. -/
lemma log_one_add_le_linear {C h : ℝ} (hCpos : 0 < C)
    (hlam : C * Real.exp (-h) ≤ Real.log C) {t : ℝ} (ht : 0 ≤ t) :
    Real.log (1 + t) ≤ (h - 1) + (C * Real.exp (-h)) * t := by
  set lam : ℝ := C * Real.exp (-h) with hlamdef
  have hlamp : 0 < lam := by rw [hlamdef]; positivity
  have hkey : Real.log (1/lam) + lam ≤ h := by
    have hinv_eq : 1/lam = Real.exp h / C := by
      rw [hlamdef, one_div, mul_inv_rev, Real.exp_neg, inv_inv, div_eq_mul_inv]
    have hloginv : Real.log (1/lam) = h - Real.log C := by
      rw [hinv_eq, Real.log_div (Real.exp_ne_zero h) (ne_of_gt hCpos), Real.log_exp]
    rw [hloginv]
    have : lam ≤ Real.log C := by rw [hlamdef]; exact hlam
    linarith
  have h1t : 0 < 1 + t := by linarith
  have hu : 0 < 1/lam := by positivity
  have htan := Real.log_le_sub_one_of_pos (div_pos h1t hu)
  rw [Real.log_div (ne_of_gt h1t) (ne_of_gt hu)] at htan
  have hdiv : (1 + t) / (1/lam) = (1 + t) * lam := by
    rw [div_eq_mul_inv, one_div, inv_inv]
  rw [hdiv] at htan
  have h2 : (1 + t) * lam - 1 = lam - 1 + lam * t := by ring
  rw [h2] at htan
  have hfin : Real.log (1 + t) ≤ h - 1 + lam * t := by linarith
  rwa [hlamdef] at hfin

/-- Sup bound for the `Π`-part of BW (15) at level `J`: for `h ≥ 19` and `Λ ≥ 0`,
`T * (1 + log (1 + Λ/T)) - h * T ≤ (5.44/(2e)) · Λ · e^{-h}` for every `T ≥ 0`.
Substituting `t = Λ/T` (for `Λ > 0`) the left side is `Λ · (log (1+t) - (h-1))/t`, whose maximum
over `t > 0` is `Λ/(1+t*)` with `t*` the solution of `log (1+t*) - t*/(1+t*) = h-1`; since
`1 + t* = e^{h - 1/(1+t*)}` this is `Λ e^{-h+1/(1+t*)}` with `1/(1+t*) ≤ 2e^{-18}` for `h ≥ 19`,
and `e^{1/(1+t*)} ≤ 5.44/(2e) = 1.00063`.
Proof route: put `λ = 5.44/(2 e^h e)`; from `log (1/λ) + λ ≤ h` (i.e. `h - 0.00063 + λ ≤ h`) and
the tangent-line inequality `log x ≤ log u + x/u - 1` at `u = 1/λ` one gets
`log (1+t) ≤ (h-1) + λ t` for all `t ≥ 0`; multiply by `Λ/t`. -/
theorem arch2_Tmax_le {h Λ T : ℝ} (hh : 19 ≤ h) (hΛ : 0 ≤ Λ) (hT : 0 ≤ T) :
    T * (1 + Real.log (1 + Λ / T)) - h * T
      ≤ (5.44 / (2 * Real.exp 1)) * (Λ * Real.exp (-h)) := by
  have hCpos : 0 < 5.44 / (2 * Real.exp 1) := by positivity
  have hC_ge : (2000:ℝ)/1999 ≤ 5.44 / (2 * Real.exp 1) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * Real.exp 1)]
    nlinarith [Real.exp_one_lt_d9]
  have hlogC : (1:ℝ)/2000 ≤ Real.log (5.44 / (2 * Real.exp 1)) := by
    have hinv : (5.44 / (2 * Real.exp 1))⁻¹ ≤ (1999:ℝ)/2000 := by
      have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < (2000:ℝ)/1999) hC_ge
      rw [one_div, one_div] at h
      have h2 : ((2000:ℝ)/1999)⁻¹ = 1999/2000 := by norm_num
      rwa [h2] at h
    have h1 := Real.one_sub_inv_le_log_of_pos hCpos
    linarith
  have hlam_le : 5.44 / (2 * Real.exp 1) * Real.exp (-h) ≤ (1:ℝ)/2000 := by
    have hC_le : 5.44 / (2 * Real.exp 1) ≤ 3 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.exp 1)]
      nlinarith [Real.exp_one_gt_two]
    have hexp_le : Real.exp (-h) ≤ Real.exp (-19) := Real.exp_le_exp.mpr (by linarith)
    have hexp19 : Real.exp (-19) ≤ (1:ℝ)/6000 := by
      rw [Real.exp_neg, one_div]
      rw [inv_le_inv₀ (Real.exp_pos 19) (by norm_num : (0:ℝ) < 6000)]
      have h1 : Real.exp 19 = (Real.exp 1)^19 := by
        rw [show (19:ℝ) = (19:ℕ) * 1 by norm_num, Real.exp_nat_mul]
      rw [h1]
      have h2 : (2:ℝ)^19 ≤ (Real.exp 1)^19 :=
        pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_two) 19
      have h3 : (6000:ℝ) ≤ (2:ℝ)^19 := by norm_num
      linarith
    calc 5.44 / (2 * Real.exp 1) * Real.exp (-h) ≤ 3 * ((1:ℝ)/6000) :=
          mul_le_mul hC_le (le_trans hexp_le hexp19) (Real.exp_nonneg _) (by norm_num)
      _ ≤ 1/2000 := by norm_num
  have hlam_log : 5.44 / (2 * Real.exp 1) * Real.exp (-h) ≤ Real.log (5.44 / (2 * Real.exp 1)) :=
    le_trans hlam_le hlogC
  rcases eq_or_lt_of_le hT with hT0 | hTpos
  · subst hT0
    simp only [div_zero, add_zero, Real.log_one, mul_zero, sub_zero, zero_mul]
    exact mul_nonneg (le_of_lt hCpos) (mul_nonneg hΛ (Real.exp_nonneg _))
  · have hG : 0 ≤ Λ / T := div_nonneg hΛ (le_of_lt hTpos)
    have hkey := log_one_add_le_linear hCpos hlam_log (t := Λ / T) hG
    have hmul := mul_le_mul_of_nonneg_left hkey (le_of_lt hTpos)
    have hcancel : T * ((5.44 / (2 * Real.exp 1) * Real.exp (-h)) * (Λ / T))
        = 5.44 / (2 * Real.exp 1) * (Λ * Real.exp (-h)) := by
      field_simp
    nlinarith [hmul, hcancel]

end Work.BW
