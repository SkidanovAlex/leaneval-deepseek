import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.LocData

/-- The angular integral `∫_{[0,π/2]} √(sin θ cos²θ) dθ = 2/3`.

On `Iθ` the integrand is `√(sin θ) · cos θ` (with `cos θ ≥ 0`), so the substitution
`u = sin θ` gives `∫_0^1 √u du = 2/3`.  Together with `∫_{Iθ} sin θ cos²θ = 1/3`
(Mathlib's `integral_sin_mul_cos_sq`) this is what the proof of
`3/5 ≤ Work.Spaces.c α` needs. -/
theorem integral_sqrt_sin_mul_cos_sq :
    ∫ θ in Work.Spaces.Iθ, Real.sqrt (Real.sin θ * Real.cos θ ^ 2) = 2 / 3 := by
  -- Step 1: on `Iθ = [0, π/2]` both `sin θ` and `cos θ` are nonnegative, so
  -- `√(sin θ · cos²θ) = √(sin θ) · |cos θ| = √(sin θ) · cos θ`.
  have hpt : ∀ θ ∈ Work.Spaces.Iθ, Real.sqrt (Real.sin θ * Real.cos θ ^ 2)
      = Real.sqrt (Real.sin θ) * Real.cos θ := by
    intro θ hθ
    have h0 : 0 ≤ θ := hθ.1
    have h2 : θ ≤ Real.pi / 2 := hθ.2
    have hsin : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨h0, by linarith [h2, Real.pi_pos]⟩
    have hcos : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [h0, Real.pi_pos]) h2
    rw [Real.sqrt_mul hsin (Real.cos θ ^ 2), Real.sqrt_sq_eq_abs, abs_of_nonneg hcos]
  rw [MeasureTheory.setIntegral_congr_fun (s := Work.Spaces.Iθ) measurableSet_Icc hpt]
  -- Step 2: the set integral over `Iθ = Icc 0 (π/2)` is the interval integral over `[0, π/2]`.
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
  -- Step 3: the substitution `u = sin θ` turns it into `∫_0^1 √u du`.
  have hcv : ∫ θ in (0 : ℝ)..Real.pi / 2, Real.sqrt (Real.sin θ) * Real.cos θ
      = ∫ x in (0 : ℝ)..1, Real.sqrt x := by
    simpa using intervalIntegral.integral_comp_mul_deriv (a := (0 : ℝ)) (b := Real.pi / 2)
      (f := Real.sin) (f' := Real.cos) (g := Real.sqrt)
      (fun x _ => Real.hasDerivAt_sin x) Real.continuous_cos.continuousOn Real.continuous_sqrt
  -- Step 4: `∫_0^1 √u du = ∫_0^1 u^(1/2) du = (1^(3/2) - 0^(3/2))/(3/2) = 2/3`.
  have hroot : ∫ x in (0 : ℝ)..1, Real.sqrt x = 2 / 3 := by
    rw [show ∫ x in (0 : ℝ)..1, Real.sqrt x = ∫ x in (0 : ℝ)..1, x ^ (1 / 2 : ℝ) from
      intervalIntegral.integral_congr (fun x _ => Real.sqrt_eq_rpow x)]
    rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < 1 / 2))]
    norm_num
  rw [hcv, hroot]

end Work.FTS.LocData

namespace Work.FTS.LocData.Work.FTS.LocData

/-- The same statement, recorded also under the doubly nested name that results from the
requested statement text (which itself carried a `namespace Work.FTS.LocData` line).
Both names are provided so that the lemma can be cited either way. -/
theorem integral_sqrt_sin_mul_cos_sq :
    ∫ θ in Work.Spaces.Iθ, Real.sqrt (Real.sin θ * Real.cos θ ^ 2) = 2 / 3 :=
  _root_.Work.FTS.LocData.integral_sqrt_sin_mul_cos_sq

end Work.FTS.LocData.Work.FTS.LocData
