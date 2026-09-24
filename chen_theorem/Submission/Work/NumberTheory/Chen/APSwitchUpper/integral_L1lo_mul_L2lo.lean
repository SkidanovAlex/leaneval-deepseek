import Mathlib

namespace Work.NumberTheory.Chen.APSwitchUpper

/-!
# The integral `∫_2^4 L1lo(u) * L2lo(u) / u du`

Here `L1lo(u) = 2*((4-u)/(u+2)) + (2/3)*((4-u)/(u+2))^3` and
`L2lo(u) = 2*((u-2)/(u+4)) + (2/3)*((u-2)/(u+4))^3` are the two lower bound
"linear sieve" weight profiles appearing in the switched (AP) upper bound
computation of Chen's theorem.  We evaluate the integral by exhibiting an
explicit antiderivative.  The integrand is a rational function with poles only
at `u = 0`, `u = -2`, `u = -4`, all outside `[2,4]`; its partial fraction
decomposition is

`-(91/9)/u + 1300/(u+2) - 1297/(u+4) - 1080/(u+2)^2 + 672/(u+2)^3
   - 1380/(u+4)^2 - 1824/(u+4)^3`

(when written over the common denominator `u (u+2)^3 (u+4)^3`), so that

`-(91/9) log u + 1300 log(u+2) - 1297 log(u+4) + 1080/(u+2) - 336/(u+2)^2
   + 1380/(u+4) + 912/(u+4)^2`

is an antiderivative.  Evaluating at `4` and `2` and using
`log 4 = 2 log 2`, `log 6 = log 2 + log 3`, `log 8 = 3 log 2` gives the stated
closed form.
-/

/-- The first (lower) linear-sieve weight factor. -/
noncomputable abbrev intL1loL2lo_Lofactor (u : ℝ) : ℝ :=
  2 * ((4 - u) / (u + 2)) + (2 / 3 : ℝ) * ((4 - u) / (u + 2)) ^ 3

/-- The second (lower) linear-sieve weight factor. -/
noncomputable abbrev intL1loL2lo_Hifactor (u : ℝ) : ℝ :=
  2 * ((u - 2) / (u + 4)) + (2 / 3 : ℝ) * ((u - 2) / (u + 4)) ^ 3

/-- The integrand of the present computation. -/
noncomputable abbrev intL1loL2lo_integrand (u : ℝ) : ℝ :=
  intL1loL2lo_Lofactor u * intL1loL2lo_Hifactor u / u

/-- An explicit antiderivative of `intL1loL2lo_integrand` on `(0, ∞)`. -/
noncomputable abbrev intL1loL2lo_prim (u : ℝ) : ℝ :=
  -(91 / 9 : ℝ) * Real.log u + 1300 * Real.log (u + 2) - 1297 * Real.log (u + 4)
    + 1080 * (u + 2)⁻¹ - 336 * (u + 2)⁻¹ ^ 2 + 1380 * (u + 4)⁻¹ + 912 * (u + 4)⁻¹ ^ 2

/-- `intL1loL2lo_prim` is an antiderivative of `intL1loL2lo_integrand` on `[2,4]`.

The derivative is the partial fraction expansion of the integrand:
`-(91/9)/u + 1300/(u+2) - 1297/(u+4) - 1080/(u+2)^2 + 672/(u+2)^3
  - 1380/(u+4)^2 - 1824/(u+4)^3`. -/
lemma intL1loL2lo_hasDerivAt {u : ℝ} (hu1 : 2 ≤ u) (_hu2 : u ≤ 4) :
    HasDerivAt intL1loL2lo_prim (intL1loL2lo_integrand u) u := by
  have hu0 : u ≠ 0 := by linarith
  have h2 : u + 2 ≠ 0 := by linarith
  have h4 : u + 4 ≠ 0 := by linarith
  have hlog1 : HasDerivAt (fun x : ℝ => -(91 / 9 : ℝ) * Real.log x)
      (-(91 / 9 : ℝ) * u⁻¹) u :=
    (Real.hasDerivAt_log hu0).const_mul _
  have hlog2 : HasDerivAt (fun x : ℝ => (1300 : ℝ) * Real.log (x + 2))
      (1300 * (u + 2)⁻¹) u := by
    have h := ((Real.hasDerivAt_log h2).comp u ((hasDerivAt_id u).add_const (2 : ℝ))).const_mul
      (1300 : ℝ)
    simpa using h
  have hlog4 : HasDerivAt (fun x : ℝ => (1297 : ℝ) * Real.log (x + 4))
      (1297 * (u + 4)⁻¹) u := by
    have h := ((Real.hasDerivAt_log h4).comp u ((hasDerivAt_id u).add_const (4 : ℝ))).const_mul
      (1297 : ℝ)
    simpa using h
  have hinv2 : HasDerivAt (fun x : ℝ => (x + 2)⁻¹) (-(1 : ℝ) / (u + 2) ^ 2) u :=
    ((hasDerivAt_id (𝕜 := ℝ) u).add_const (2 : ℝ)).inv h2
  have hinv4 : HasDerivAt (fun x : ℝ => (x + 4)⁻¹) (-(1 : ℝ) / (u + 4) ^ 2) u :=
    ((hasDerivAt_id (𝕜 := ℝ) u).add_const (4 : ℝ)).inv h4
  have hp2 := hinv2.pow 2
  have hp4 := hinv4.pow 2
  have hA : HasDerivAt (fun x : ℝ => (1080 : ℝ) * (x + 2)⁻¹)
      (1080 * (-(1 : ℝ) / (u + 2) ^ 2)) u :=
    hinv2.const_mul 1080
  have hB : HasDerivAt (fun x : ℝ => (336 : ℝ) * (x + 2)⁻¹ ^ 2)
      (336 * (2 * (u + 2)⁻¹ ^ (2 - 1) * (-(1 : ℝ) / (u + 2) ^ 2))) u :=
    hp2.const_mul 336
  have hC : HasDerivAt (fun x : ℝ => (1380 : ℝ) * (x + 4)⁻¹)
      (1380 * (-(1 : ℝ) / (u + 4) ^ 2)) u :=
    hinv4.const_mul 1380
  have hD : HasDerivAt (fun x : ℝ => (912 : ℝ) * (x + 4)⁻¹ ^ 2)
      (912 * (2 * (u + 4)⁻¹ ^ (2 - 1) * (-(1 : ℝ) / (u + 4) ^ 2))) u :=
    hp4.const_mul 912
  have hcomb := ((((hlog1.add hlog2).sub hlog4).add hA).sub hB).add hC |>.add hD
  unfold intL1loL2lo_prim intL1loL2lo_integrand intL1loL2lo_Lofactor intL1loL2lo_Hifactor
  refine ((hcomb.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun x => ?_))).congr_deriv ?_)
  · simp only [Pi.add_apply, Pi.sub_apply]
  · push_cast
    field_simp
    ring

/-- The integrand is continuous on `[2,4]` (the only poles are `0`, `-2`, `-4`). -/
lemma intL1loL2lo_continuousOn :
    ContinuousOn intL1loL2lo_integrand (Set.uIcc (2 : ℝ) 4) := by
  have hge : ∀ x ∈ Set.uIcc (2 : ℝ) 4, (2 : ℝ) ≤ x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)] at hx
    exact hx.1
  have h1 : ∀ x ∈ Set.uIcc (2 : ℝ) 4, x + 2 ≠ 0 := fun x hx => by linarith [hge x hx]
  have h2 : ∀ x ∈ Set.uIcc (2 : ℝ) 4, x + 4 ≠ 0 := fun x hx => by linarith [hge x hx]
  have h3 : ∀ x ∈ Set.uIcc (2 : ℝ) 4, x ≠ 0 := fun x hx => by linarith [hge x hx]
  unfold intL1loL2lo_integrand intL1loL2lo_Lofactor intL1loL2lo_Hifactor
  fun_prop (disch := assumption)

/-- Evaluation of the antiderivative at the endpoints. -/
lemma intL1loL2lo_prim_eval :
    intL1loL2lo_prim 4 - intL1loL2lo_prim 2
      = -1763 / 12 - (35137 / 9 : ℝ) * Real.log 2 + 2597 * Real.log 3 := by
  have l4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have l6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have l8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  unfold intL1loL2lo_prim
  norm_num
  rw [l4, l6, l8]
  ring

theorem integral_L1lo_mul_L2lo :
    ∫ u in (2 : ℝ)..4,
        (2 * ((4 - u) / (u + 2)) + (2 / 3 : ℝ) * ((4 - u) / (u + 2)) ^ 3) *
          (2 * ((u - 2) / (u + 4)) + (2 / 3 : ℝ) * ((u - 2) / (u + 4)) ^ 3) / u
      = -1763 / 12 - (35137 / 9 : ℝ) * Real.log 2 + 2597 * Real.log 3 := by
  have hderiv : ∀ u ∈ Set.uIcc (2 : ℝ) 4, HasDerivAt intL1loL2lo_prim (intL1loL2lo_integrand u) u := by
    intro u hu
    rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)] at hu
    exact intL1loL2lo_hasDerivAt hu.1 hu.2
  have hint : IntervalIntegrable intL1loL2lo_integrand MeasureTheory.volume 2 4 :=
    intL1loL2lo_continuousOn.intervalIntegrable
  have hftc : ∫ u in (2 : ℝ)..4, intL1loL2lo_integrand u
      = intL1loL2lo_prim 4 - intL1loL2lo_prim 2 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hgoal : (∫ u in (2 : ℝ)..4,
        (2 * ((4 - u) / (u + 2)) + (2 / 3 : ℝ) * ((4 - u) / (u + 2)) ^ 3) *
          (2 * ((u - 2) / (u + 4)) + (2 / 3 : ℝ) * ((u - 2) / (u + 4)) ^ 3) / u)
      = ∫ u in (2 : ℝ)..4, intL1loL2lo_integrand u := rfl
  rw [hgoal, hftc, intL1loL2lo_prim_eval]

end Work.NumberTheory.Chen.APSwitchUpper
