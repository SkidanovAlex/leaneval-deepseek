import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.Rb5Lin

open MeasureTheory Set Real

/-- Substitution `r = √(u² + s²)` in the integral over `u ∈ (0, ∞)`, valid for an arbitrary
(not necessarily measurable) integrand.  This is the general one-dimensional change-of-variables
formula `MeasureTheory.integral_image_eq_integral_abs_deriv_smul` applied to
`φ u = √(u² + s²)`, whose image is `Ioi |s|` and whose derivative is `u / √(u² + s²)`. -/
theorem integral_Ioi_sqrt_subst (Ψ : ℝ → ℝ) (s : ℝ) :
    (∫ u in Set.Ioi (0 : ℝ), u * Ψ (Real.sqrt (u ^ 2 + s ^ 2)))
      = ∫ r in Set.Ioi |s|, r * Ψ r := by
  have himg : (fun u : ℝ => Real.sqrt (u ^ 2 + s ^ 2)) '' Set.Ioi 0 = Set.Ioi |s| := by
    ext r
    constructor
    · rintro ⟨u, hu, rfl⟩
      change |s| < Real.sqrt (u ^ 2 + s ^ 2)
      rw [Real.lt_sqrt (abs_nonneg s), sq_abs]
      nlinarith [sq_pos_of_pos (show (0:ℝ) < u from hu)]
    · intro hr
      have hr0 : 0 < r := lt_of_le_of_lt (abs_nonneg s) hr
      have hsq : s ^ 2 < r ^ 2 := by
        have h : |s| ^ 2 < r ^ 2 := by
          have := mul_self_lt_mul_self (show (0:ℝ) ≤ |s| from abs_nonneg s) hr
          simpa [pow_two] using this
        rwa [sq_abs] at h
      have hpos : 0 < r ^ 2 - s ^ 2 := by linarith
      refine ⟨Real.sqrt (r ^ 2 - s ^ 2), Real.sqrt_pos_of_pos hpos, ?_⟩
      change Real.sqrt (Real.sqrt (r ^ 2 - s ^ 2) ^ 2 + s ^ 2) = r
      rw [Real.sq_sqrt (le_of_lt hpos), sub_add_cancel, Real.sqrt_sq (le_of_lt hr0)]
  have hinj : InjOn (fun u : ℝ => Real.sqrt (u ^ 2 + s ^ 2)) (Set.Ioi 0) := by
    intro u hu v hv huv
    have h1 : u ^ 2 + s ^ 2 = v ^ 2 + s ^ 2 := by
      have hh := Real.sqrt_inj (x := u^2+s^2) (y := v^2+s^2) (by positivity) (by positivity)
      exact hh.mp huv
    have h2 : u ^ 2 = v ^ 2 := by linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h | h
    · exact h
    · exfalso; nlinarith [show (0:ℝ) < u from hu, show (0:ℝ) < v from hv, h]
  have hderiv : ∀ x ∈ Set.Ioi (0:ℝ),
      HasDerivWithinAt (fun u : ℝ => Real.sqrt (u ^ 2 + s ^ 2))
        (x / Real.sqrt (x ^ 2 + s ^ 2)) (Set.Ioi 0) x := by
    intro x hx
    have hx0 : (0:ℝ) < x := hx
    have hy : (0:ℝ) < x ^ 2 + s ^ 2 := by nlinarith [sq_pos_of_pos hx0, sq_nonneg s]
    have h2 : HasDerivAt (fun u : ℝ => u ^ 2 + s ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).add_const (s ^ 2)
    have h3 : HasDerivAt (fun u : ℝ => Real.sqrt (u ^ 2 + s ^ 2))
        (1 / (2 * Real.sqrt (x ^ 2 + s ^ 2)) * (2 * x)) x :=
      (Real.hasDerivAt_sqrt hy.ne').comp x h2
    have hv : 1 / (2 * Real.sqrt (x ^ 2 + s ^ 2)) * (2 * x)
        = x / Real.sqrt (x ^ 2 + s ^ 2) := by
      field_simp
    rw [hv] at h3
    exact h3.hasDerivWithinAt
  have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (f := fun u : ℝ => Real.sqrt (u ^ 2 + s ^ 2))
    (f' := fun u : ℝ => u / Real.sqrt (u ^ 2 + s ^ 2))
    measurableSet_Ioi hderiv hinj (fun r => r * Ψ r)
  rw [himg] at h
  rw [h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx0 : 0 < x := hx
  have hpos : 0 < Real.sqrt (x ^ 2 + s ^ 2) :=
    Real.sqrt_pos_of_pos (by nlinarith [sq_pos_of_pos hx0, sq_nonneg s])
  simp only [smul_eq_mul]
  rw [abs_of_pos (div_pos hx0 hpos)]
  field_simp

end Work.BoseFixR.Rb5Lin
