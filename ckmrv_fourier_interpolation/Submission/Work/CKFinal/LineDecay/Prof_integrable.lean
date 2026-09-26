import Mathlib

namespace Work.CKFinal.LineDecay

open MeasureTheory Filter Real Asymptotics

lemma Prof_integrable (α : ℝ) (hα : 0 ≤ α) :
    MeasureTheory.Integrable (fun u : ℝ => (1 + |u|) ^ α * Real.exp (-(Real.pi * |u|))) := by
  -- Step 1: continuity of the model function `x ↦ (1 + x)^α * exp(-(π x))` on `[0, ∞)`.
  have hcont : ContinuousOn (fun x : ℝ => (1 + x) ^ α * Real.exp (-(Real.pi * x))) (Set.Ici 0) := by
    refine ContinuousOn.mul ?_ ?_
    · refine ContinuousOn.rpow_const ?_ ?_
      · exact (continuous_const.add continuous_id).continuousOn
      · intro x hx
        left
        simp only [Set.mem_Ici] at hx
        linarith
    · exact ContinuousOn.rexp (((continuous_const.mul continuous_id).neg).continuousOn)
  -- Step 2: exponential decay of the model function at `+∞`.
  have hO : (fun x : ℝ => (1 + x) ^ α * Real.exp (-(Real.pi * x))) =O[atTop]
      (fun x : ℝ => Real.exp (-(Real.pi / 2) * x)) := by
    have h1 : (fun x : ℝ => (1 + x) ^ α) =O[atTop] (fun x : ℝ => x ^ α) := by
      refine Asymptotics.IsBigO.of_bound (2 ^ α) ?_
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) α),
        abs_of_nonneg (Real.rpow_nonneg (by linarith) α)]
      calc (1 + x) ^ α ≤ (2 * x) ^ α := Real.rpow_le_rpow (by linarith) (by linarith) hα
        _ = 2 ^ α * x ^ α := by rw [Real.mul_rpow (by norm_num) (by linarith)]
    have h2 : (fun x : ℝ => (1 + x) ^ α) =O[atTop] (fun x : ℝ => Real.exp ((Real.pi / 2) * x)) :=
      h1.trans (isLittleO_rpow_exp_pos_mul_atTop α (by positivity)).isBigO
    have h3 := h2.mul (Asymptotics.isBigO_refl (fun x : ℝ => Real.exp (-(Real.pi * x))) atTop)
    refine h3.congr (fun x => rfl) (fun x => ?_)
    rw [← Real.exp_add, Real.exp_eq_exp]
    ring
  -- Step 3: integrability of the model function on `(0, ∞)`.
  have hkey : IntegrableOn (fun x : ℝ => (1 + x) ^ α * Real.exp (-(Real.pi * x))) (Set.Ioi 0) :=
    integrable_of_isBigO_exp_neg (show (0 : ℝ) < Real.pi / 2 by positivity) hcont hO
  -- Step 4: transfer to the even function `u ↦ (1 + |u|)^α * exp(-(π |u|))` on `(0, ∞)`.
  have hpos : IntegrableOn (fun u : ℝ => (1 + |u|) ^ α * Real.exp (-(Real.pi * |u|))) (Set.Ioi 0) :=
    hkey.congr_fun (fun x hx => by rw [abs_of_pos hx]) measurableSet_Ioi
  -- Step 5: the same function on `(-∞, 0)`, by the substitution `x ↦ -x`.
  have hneg0 : IntegrableOn (fun x : ℝ => (1 + -x) ^ α * Real.exp (-(Real.pi * -x))) (Set.Iio 0) := by
    simpa using hkey.comp_neg
  have hneg : IntegrableOn (fun u : ℝ => (1 + |u|) ^ α * Real.exp (-(Real.pi * |u|))) (Set.Iio 0) :=
    hneg0.congr_fun (fun x hx => by rw [abs_of_neg hx]) measurableSet_Iio
  -- Step 6: glue the two half-lines.
  have hIic : IntegrableOn (fun u : ℝ => (1 + |u|) ^ α * Real.exp (-(Real.pi * |u|))) (Set.Iic 0) :=
    (integrableOn_Iic_iff_integrableOn_Iio).mpr hneg
  refine (integrableOn_univ (f := fun u : ℝ => (1 + |u|) ^ α * Real.exp (-(Real.pi * |u|)))
    (μ := volume)).mp ?_
  rw [← Set.Iic_union_Ioi (a := (0 : ℝ))]
  exact (integrableOn_union).mpr ⟨hIic, hpos⟩

end Work.CKFinal.LineDecay
