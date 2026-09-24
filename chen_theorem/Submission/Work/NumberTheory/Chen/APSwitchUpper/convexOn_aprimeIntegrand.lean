import Mathlib

/-!
# Convexity of the switched-integrand `v ↦ log (3/(v-1)) / v` on `[2,4]`

The switched (AP) upper bound of Chen's argument averages the function
`aPrime v = log (3 / (v - 1)) / v` against a window profile, and the
sharp main-term comparison needs `aPrime` to be **convex** on its range
`v ∈ [2,4]` (a Hermite–Hadamard / Jensen input).

Convexity is proved from the sign of the second derivative.  Writing
`t = v - 1 ∈ [1,3]` one computes

`aPrime''(v) = (v^2/(v-1)^2 + 2v/(v-1) + 2·log (3/(v-1))) / v^3`,

and this is `≥ 0` on `[2,4]`: the first two summands are manifestly
non-negative, while `log (3/(v-1)) ≥ 0` because `v - 1 ≤ 3`.
-/

namespace Work.NumberTheory.Chen.APSwitchUpper

/-- The (negated) logarithmic part of the integrand's derivative. -/
private noncomputable def aPrimeF1 (v : ℝ) : ℝ :=
  (-((v - 1)⁻¹ * v) - Real.log (3 / (v - 1))) / (v * v)

/-- The second derivative of the integrand, in a manifestly non-negative form. -/
private noncomputable def aPrimeF2 (v : ℝ) : ℝ :=
  ((v * v) / ((v - 1) * (v - 1)) + 2 * v / (v - 1) + 2 * Real.log (3 / (v - 1)))
    / (v * v * v)

/-- Derivative of `v ↦ log (3/(v-1))` on `(2,4)`. -/
private lemma hasDerivAt_log_three (x : ℝ) (hx : x ∈ Set.Ioo (2:ℝ) 4) :
    HasDerivAt (fun v : ℝ => Real.log (3 / (v - 1))) (-((x - 1)⁻¹)) x := by
  have hx1 : (x - 1) ≠ 0 := by linarith [hx.1]
  have hsub : HasDerivAt (fun v : ℝ => v - 1) (1:ℝ) x := by
    simpa using (hasDerivAt_id x).sub_const 1
  have hinv := hsub.inv hx1
  have h3 : HasDerivAt (fun v : ℝ => 3 / (v - 1)) (-(3 / (x - 1) ^ 2)) x :=
    (hinv.const_mul (3:ℝ)).congr_deriv (by ring)
  have hpos : (0:ℝ) < 3 / (x - 1) := div_pos (by norm_num) (by linarith [hx.1])
  exact (h3.log hpos.ne').congr_deriv (by field_simp)

/-- First derivative of the integrand on `(2,4)`. -/
private lemma hasDerivAt_aPrimeF1 (x : ℝ) (hx : x ∈ Set.Ioo (2:ℝ) 4) :
    HasDerivAt (fun v : ℝ => Real.log (3 / (v - 1)) / v) (aPrimeF1 x) x := by
  have hx0 : x ≠ 0 := by linarith [hx.1]
  have h := (hasDerivAt_log_three x hx).div (hasDerivAt_id x) hx0
  exact h.congr_deriv (by simp only [aPrimeF1, id_eq]; ring)

/-- Second derivative of the integrand on `(2,4)`, with the derivative written
in the manifestly non-negative form `aPrimeF2`. -/
private lemma hasDerivAt_aPrimeF2 (x : ℝ) (hx : x ∈ Set.Ioo (2:ℝ) 4) :
    HasDerivAt aPrimeF1 (aPrimeF2 x) x := by
  have hx1 : (x - 1) ≠ 0 := by linarith [hx.1]
  have hx0 : x ≠ 0 := by linarith [hx.1]
  have hsub : HasDerivAt (fun v : ℝ => v - 1) (1:ℝ) x := by
    simpa using (hasDerivAt_id x).sub_const 1
  have hinv := hsub.inv hx1
  have hlog := hasDerivAt_log_three x hx
  have hnum : HasDerivAt (fun v : ℝ => -((v - 1)⁻¹ * v) - Real.log (3 / (v - 1)))
      (x * ((x - 1) ^ 2)⁻¹) x := by
    have hmul := (hinv.mul (hasDerivAt_id x)).neg
    have h := hmul.sub hlog
    exact h.congr_deriv (by simp only [id_eq, Pi.inv_apply]; ring)
  have hden : HasDerivAt (fun v : ℝ => v * v) (2 * x) x := by
    have h := (hasDerivAt_id x).mul (hasDerivAt_id x)
    exact h.congr_deriv (by simp only [id_eq]; ring)
  have h := hnum.div hden (mul_ne_zero hx0 hx0)
  exact h.congr_deriv (by simp only [aPrimeF2]; field_simp; ring)

/-- The second derivative of the integrand is non-negative on `(2,4)`. -/
private lemma aPrimeF2_nonneg (x : ℝ) (hx : x ∈ Set.Ioo (2:ℝ) 4) : 0 ≤ aPrimeF2 x := by
  have hx1 : (0:ℝ) < x - 1 := by linarith [hx.1]
  have hx0 : (0:ℝ) < x := by linarith [hx.1]
  have hlog : 0 ≤ Real.log (3 / (x - 1)) := by
    apply Real.log_nonneg
    rw [one_le_div hx1]
    linarith [hx.2]
  rw [aPrimeF2]
  apply div_nonneg
  · refine add_nonneg (add_nonneg ?_ ?_) ?_
    · exact div_nonneg (mul_self_nonneg x) (le_of_lt (mul_pos hx1 hx1))
    · exact div_nonneg (mul_nonneg (by norm_num) (le_of_lt hx0)) (le_of_lt hx1)
    · exact mul_nonneg (by norm_num) hlog
  · exact le_of_lt (mul_pos (mul_pos hx0 hx0) hx0)

theorem convexOn_aprimeIntegrand :
    ConvexOn ℝ (Set.Icc 2 4) (fun v : ℝ => Real.log (3 / (v - 1)) / v) := by
  have hcont : ContinuousOn (fun v : ℝ => Real.log (3 / (v - 1)) / v)
      (Set.Icc (2:ℝ) 4) := by
    apply ContinuousOn.div
    · apply ContinuousOn.log
      · exact ContinuousOn.div continuousOn_const
          (continuousOn_id.sub continuousOn_const) (fun v hv => by linarith [hv.1])
      · intro v hv
        exact ne_of_gt (div_pos (by norm_num) (by linarith [hv.1]))
    · exact continuousOn_id
    · intro v hv; linarith [hv.1]
  refine convexOn_of_hasDerivWithinAt2_nonneg (D := Set.Icc (2:ℝ) 4)
    (f := fun v : ℝ => Real.log (3 / (v - 1)) / v)
    (f' := aPrimeF1) (f'' := aPrimeF2) (convex_Icc 2 4) hcont ?_ ?_ ?_
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_aPrimeF1 x hx).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_aPrimeF2 x hx).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact aPrimeF2_nonneg x hx

end Work.NumberTheory.Chen.APSwitchUpper
