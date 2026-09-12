import Mathlib

/-!
Real-analysis lemma: `T * exp (-a * T) → 0`, in the form needed to make the
Gaussian-walk "stays inside the polytope" failure probability small by taking
many tiny steps (child task).

TASK: prove `exists_nat_small_exp`.  You may add helpers above it.
-/

open scoped BigOperators Topology
open Filter

noncomputable section

namespace Submission.Discrepancy

set_option linter.unusedVariables false in

/-- For any `M ≥ 0`, `a > 0`, `B > 0` there is a natural `T` with
`M * T * exp (-a * T) < B`. -/
lemma exists_nat_small_exp (M a B : ℝ) (hM : 0 ≤ M) (ha : 0 < a) (hB : 0 < B) :
    ∃ T : ℕ, M * (T : ℝ) * Real.exp (-a * (T : ℝ)) < B := by
  -- `x ↦ x * exp (-x)` tends to `0` at `+∞`
  have hbase : Tendsto (fun x : ℝ => x * Real.exp (-x)) atTop (𝓝 0) := by
    simpa [pow_one] using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1)
  -- the argument rescaling `x ↦ a * x` (with `a > 0`) stays at `+∞`
  have harg : Tendsto (fun x : ℝ => a * x) atTop atTop :=
    tendsto_id.const_mul_atTop ha
  -- hence `(a*x) * exp (-(a*x)) → 0`
  have hcomp : Tendsto (fun x : ℝ => (a * x) * Real.exp (-(a * x))) atTop (𝓝 0) :=
    hbase.comp harg
  -- multiplying by the constant `M / a` preserves the limit
  have hsc : Tendsto (fun x : ℝ => (M / a) * ((a * x) * Real.exp (-(a * x)))) atTop (𝓝 0) := by
    simpa using (Filter.Tendsto.const_mul (M / a) hcomp)
  -- and this function equals `M * x * exp (-a * x)` pointwise (since `a ≠ 0`)
  have hF : Tendsto (fun x : ℝ => M * x * Real.exp (-(a * x))) atTop (𝓝 0) := by
    refine hsc.congr' ?_
    filter_upwards with x
    field_simp [ha.ne']
  -- along the naturals the same sequence tends to `0`
  have hFn : Tendsto (fun T : ℕ => M * (T : ℝ) * Real.exp (-(a * (T : ℝ)))) atTop (𝓝 0) :=
    hF.comp tendsto_natCast_atTop_atTop
  -- so eventually it is `< B`
  have hB' : ∀ᶠ T : ℕ in atTop, M * (T : ℝ) * Real.exp (-(a * (T : ℝ))) < B :=
    (tendsto_order.1 hFn).2 B hB
  rcases (eventually_atTop.1 hB') with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  simpa [neg_mul] using hN N le_rfl

end Discrepancy

end Submission
