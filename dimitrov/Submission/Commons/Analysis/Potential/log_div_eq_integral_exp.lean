import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory Set Filter
open scoped Topology

namespace Commons.Analysis.Potential

/-- For `u, v ≥ 0`, the decreasing exponential is `1`-Lipschitz:
`|exp (-u) - exp (-v)| ≤ |u - v|`. -/
lemma abs_exp_neg_sub_exp_neg_le {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |Real.exp (-u) - Real.exp (-v)| ≤ |u - v| := by
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) (Set.Ici (0 : ℝ)) x := by
    intro x _
    simpa using ((hasDerivAt_neg' x).exp).hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ici (0 : ℝ), ‖-Real.exp (-x)‖ ≤ (1 : ℝ) := by
    intro x hx
    have hx' : (0 : ℝ) ≤ x := hx
    rw [norm_neg, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.Ici (0 : ℝ)) (f := fun y : ℝ => Real.exp (-y))
    (f' := fun x : ℝ => -Real.exp (-x)) hderiv hbound (convex_Ici 0) hv hu
  simpa [Real.norm_eq_abs, one_mul] using h

/-- The Frullani integrand `t ↦ t⁻¹ * (exp (-(a t)) - exp (-(b t)))` is integrable on
`(0, ∞)` for positive `a`, `b`. -/
lemma integrableOn_inv_mul_exp_neg_sub_exp_neg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t⁻¹ * (Real.exp (-(a * t)) - Real.exp (-(b * t))))
      (Ioi 0) := by
  set c : ℝ := min a b with hc_def
  have hc : 0 < c := lt_min ha hb
  have hca : c ≤ a := min_le_left _ _
  have hcb : c ≤ b := min_le_right _ _
  -- The decaying majorant on `(1, ∞)`.
  have hdecay : IntegrableOn (fun t : ℝ => Real.exp (-(c * t))) (Ioi 1) := by
    have h := integrableOn_exp_mul_Ioi (a := -c) (by linarith) (1 : ℝ)
    simpa [neg_mul] using h
  change Integrable (fun t : ℝ => Real.exp (-(c * t))) (volume.restrict (Ioi 1)) at hdecay
  have hmajor : Integrable (fun t : ℝ => 2 * Real.exp (-(c * t))) (volume.restrict (Ioi 1)) :=
    hdecay.const_mul 2
  -- Bound on the tail.
  have htail_bound : ∀ t ∈ Ioi (1 : ℝ),
      ‖t⁻¹ * (Real.exp (-(a * t)) - Real.exp (-(b * t)))‖ ≤ 2 * Real.exp (-(c * t)) := by
    intro t ht
    have htpos : 0 < t := lt_trans zero_lt_one ht
    have hD : |Real.exp (-(a * t)) - Real.exp (-(b * t))| ≤ 2 * Real.exp (-(c * t)) := by
      have h1 : Real.exp (-(a * t)) ≤ Real.exp (-(c * t)) :=
        Real.exp_le_exp.mpr (by nlinarith [hca, htpos])
      have h2 : Real.exp (-(b * t)) ≤ Real.exp (-(c * t)) :=
        Real.exp_le_exp.mpr (by nlinarith [hcb, htpos])
      calc |Real.exp (-(a * t)) - Real.exp (-(b * t))|
          ≤ |Real.exp (-(a * t))| + |Real.exp (-(b * t))| := abs_sub _ _
        _ = Real.exp (-(a * t)) + Real.exp (-(b * t)) := by
              rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
        _ ≤ Real.exp (-(c * t)) + Real.exp (-(c * t)) := add_le_add h1 h2
        _ = 2 * Real.exp (-(c * t)) := by ring
    have htinv : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht.le
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr htpos)]
    calc t⁻¹ * |Real.exp (-(a * t)) - Real.exp (-(b * t))|
        ≤ t⁻¹ * (2 * Real.exp (-(c * t))) :=
          mul_le_mul_of_nonneg_left hD (inv_nonneg.mpr htpos.le)
      _ ≤ 1 * (2 * Real.exp (-(c * t))) :=
          mul_le_mul_of_nonneg_right htinv (by positivity)
      _ = 2 * Real.exp (-(c * t)) := one_mul _
  have htail : IntegrableOn
      (fun t : ℝ => t⁻¹ * (Real.exp (-(a * t)) - Real.exp (-(b * t)))) (Ioi 1) :=
    Integrable.mono' hmajor (by fun_prop)
      (ae_restrict_of_forall_mem measurableSet_Ioi htail_bound)
  -- Bound near `0`.
  have hnear_bound : ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖t⁻¹ * (Real.exp (-(a * t)) - Real.exp (-(b * t)))‖ ≤ |a - b| := by
    intro t ht
    have htpos : 0 < t := ht.1
    have hD : |Real.exp (-(a * t)) - Real.exp (-(b * t))| ≤ |a - b| * t := by
      have h := abs_exp_neg_sub_exp_neg_le (u := a * t) (v := b * t) (by positivity) (by positivity)
      have hsub : a * t - b * t = (a - b) * t := by ring
      rw [hsub, abs_mul, abs_of_pos htpos] at h
      exact h
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr htpos)]
    calc t⁻¹ * |Real.exp (-(a * t)) - Real.exp (-(b * t))|
        ≤ t⁻¹ * (|a - b| * t) := mul_le_mul_of_nonneg_left hD (inv_nonneg.mpr htpos.le)
      _ = |a - b| := by
          rw [mul_comm (|a - b|) t, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt htpos), one_mul]
  have hnear : IntegrableOn
      (fun t : ℝ => t⁻¹ * (Real.exp (-(a * t)) - Real.exp (-(b * t)))) (Ioc 0 1) :=
    IntegrableOn.of_bound measure_Ioc_lt_top (by fun_prop) |a - b|
      (ae_restrict_of_forall_mem measurableSet_Ioc hnear_bound)
  -- Glue the two pieces.
  refine (hnear.union htail).mono_set ?_
  intro t ht
  rcases le_or_gt t 1 with h | h
  · exact Or.inl ⟨ht, h⟩
  · exact Or.inr h

/-- **Frullani's integral** for the decreasing exponential:
`∫_0^∞ (e^{-a t} - e^{-b t}) / t dt = log (b / a)` for `a, b > 0`. -/
lemma integral_inv_smul_exp_neg_sub_exp_neg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ t in Ioi 0, t⁻¹ • (Real.exp (-(a * t)) - Real.exp (-(b * t))) = Real.log (b / a) := by
  have hf : LocallyIntegrableOn (fun y : ℝ => Real.exp (-y)) (Ioi 0) :=
    (Real.continuous_exp.comp continuous_neg).continuousOn.locallyIntegrableOn measurableSet_Ioi
  have hL : Tendsto (fun y : ℝ => Real.exp (-y)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hcont : Continuous (fun y : ℝ => Real.exp (-y)) := by fun_prop
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hR : Tendsto (fun y : ℝ => Real.exp (-y)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hint : IntegrableOn
      (fun x : ℝ => x⁻¹ • (Real.exp (-(a * x)) - Real.exp (-(b * x)))) (Ioi 0) := by
    simpa [smul_eq_mul] using integrableOn_inv_mul_exp_neg_sub_exp_neg ha hb
  have h := Frullani.integral_Ioi_eq (f := fun y : ℝ => Real.exp (-y))
    (a := a) (b := b) hf ha hb hL hR hint
  simpa using h

theorem log_div_eq_integral_exp (R : ℝ) (hR : 0 < R) {x : ℂ} (hx : x ≠ 0) :
    2 * Real.log (R / ‖x‖) =
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi 0))
        (fun t : ℝ => t⁻¹ * (Real.exp (-(t * ‖x‖ ^ 2 / R ^ 2)) - Real.exp (-t))) := by
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set A : ℝ := ‖x‖ ^ 2 / R ^ 2 with hA
  have hApos : 0 < A := by rw [hA]; positivity
  have hint := integral_inv_smul_exp_neg_sub_exp_neg (a := A) (b := 1) hApos one_pos
  have hcongr : (fun t : ℝ => t⁻¹ * (Real.exp (-(t * ‖x‖ ^ 2 / R ^ 2)) - Real.exp (-t)))
      = fun t : ℝ => t⁻¹ • (Real.exp (-(A * t)) - Real.exp (-(1 * t))) := by
    funext t
    have hkey : t * ‖x‖ ^ 2 / R ^ 2 = A * t := by rw [hA]; ring
    simp only [smul_eq_mul, one_mul, hkey]
  have hlog : Real.log (1 / A) = 2 * Real.log (R / ‖x‖) := by
    have hAeq : A = (‖x‖ / R) ^ 2 := by rw [hA, div_pow]
    calc Real.log (1 / A) = -Real.log A := by rw [one_div, Real.log_inv]
      _ = -Real.log ((‖x‖ / R) ^ 2) := by rw [hAeq]
      _ = -(2 * Real.log (‖x‖ / R)) := by rw [Real.log_pow]; norm_num
      _ = 2 * Real.log ((‖x‖ / R)⁻¹) := by rw [Real.log_inv]; ring
      _ = 2 * Real.log (R / ‖x‖) := by rw [inv_div]
  rw [hcongr, hint, hlog]

end Commons.Analysis.Potential