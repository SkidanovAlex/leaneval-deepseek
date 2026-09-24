import Mathlib
import Submission.ChenPlan.Interfaces
import Submission.Work.NumberTheory.Chen.mertens_lower_tenth
import Submission.Work.NumberTheory.Chen.sqMass_bound_sharp

/-! Guidance from the project lead (the requester):

Small assembly. Work under Submission/Work/ChenPlan/Assembly/. Apply
`Submission.chen_rate_estimate_of_inputs_gen` (Submission/Chen/Switch.lean) with M = chenSiftLimitTenth,
ε = 1/100, A = 39/25, B = 27/10, D = 34/5, E = 1/32, δ = 1/1000. hfin ≈ +0.061; check the arithmetic exactly.
Inputs:
- hV: `Work.NumberTheory.Chen.mertens_lower_tenth`.
- hsq: from `Work.NumberTheory.Chen.sqMass_bound_sharp` (it is at chenSiftLimit ≈ x^{0.0749} with log²x).
  sqMassAll x M is antitone in M (fewer rough p, fewer q ≥ M) and chenSiftLimit ≤ chenSiftLimitTenth for large x;
  also sqMass·log x ≤ sqMass·log²x/log x.
- hM: `eventually_chenSiftLimitTenth_ge` (in Switch.lean). hY: `window_cube`.
- hlog: log(x+2) ≤ (1+δ) log x eventually.
- h1, h2, h3: the hypotheses.
-/

open Filter Finset
open scoped BigOperators

namespace Work.ChenPlan.Assembly

/-- `sqMassAll` is a sum of `log p` over primes `p ≥ 2`, hence nonnegative. -/
lemma sqMassAll_nonneg (x M : ℕ) : 0 ≤ Submission.sqMassAll x M := by
  classical
  rw [Submission.sqMassAll]
  refine Finset.sum_nonneg fun p hp => ?_
  have hp' : p ∈ Submission.s0Set x M := (Finset.mem_filter.mp hp).1
  exact Submission.log_nonneg_of_mem_s0Set hp'

/-- The `q²`-exceptional mass at the sift limit `x^{1/10}` satisfies the input `hsq` of the
assembly with `E = 1/32`: since `sqMassAll` is antitone in the sift limit and its value at
`chenSiftLimit x` obeys the sharp bound with `(log x)²`. -/
lemma eventually_sqMassAll_tenth_log_le :
    ∀ᶠ x : ℕ in Filter.atTop,
      Submission.sqMassAll x (Submission.chenSiftLimitTenth x) * Real.log (x : ℝ)
        ≤ (1 / 32 : ℝ) * (x : ℝ) := by
  have hlog1 : ∀ᶠ x : ℕ in Filter.atTop, 1 ≤ Real.log (x : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop 1)
  filter_upwards [Work.NumberTheory.Chen.sqMass_bound_sharp, hlog1,
    Filter.eventually_ge_atTop 1] with x hsharp hlog1x hx1
  have hmono : Submission.sqMassAll x (Submission.chenSiftLimitTenth x)
      ≤ Submission.sqMassAll x (Submission.chenSiftLimit x) :=
    Submission.sqMassAll_antitone x _ _ (Submission.chenSiftLimit_le_tenth hx1)
  have hnn : 0 ≤ Submission.sqMassAll x (Submission.chenSiftLimit x) := sqMassAll_nonneg x _
  have hlog0 : 0 ≤ Real.log (x : ℝ) := by linarith
  calc Submission.sqMassAll x (Submission.chenSiftLimitTenth x) * Real.log (x : ℝ)
      ≤ Submission.sqMassAll x (Submission.chenSiftLimit x) * Real.log (x : ℝ) :=
        mul_le_mul_of_nonneg_right hmono hlog0
    _ ≤ Submission.sqMassAll x (Submission.chenSiftLimit x) * (Real.log (x : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left (by nlinarith [hlog1x]) hnn
    _ ≤ (1 / 32 : ℝ) * (x : ℝ) := hsharp

/-- The rate estimate from the three inputs at `M = x^{1/10}`, via `chen_rate_estimate_of_inputs_gen`. -/
theorem chen_rate_of_inputs (h1 : Submission.ChenPlan.H1Statement) (h2 : Submission.ChenPlan.H2Statement)
    (h3 : Submission.ChenPlan.H3Statement) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in Filter.atTop,
      c * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 ≤ (Submission.chenCount x : ℝ) := by
  refine Submission.chen_rate_estimate_of_inputs_gen
    (M := fun x => Submission.chenSiftLimitTenth x)
    (ε := 1 / 100) (A := 39 / 25) (B := 27 / 10) (D := 34 / 5) (E := 1 / 32) (δ := 1 / 1000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [Submission.eventually_log_add_two_le (1 / 1000) (by norm_num),
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (Filter.eventually_ge_atTop 1)] with x hlogx h1x
    exact ⟨h1x, hlogx⟩
  · exact Submission.eventually_chenSiftLimitTenth_ge
  · exact Submission.eventually_window_cube
  · exact Work.NumberTheory.Chen.mertens_lower_tenth
  · exact eventually_sqMassAll_tenth_log_le
  · simpa only [Submission.ChenPlan.H1Statement] using h1
  · simpa only [Submission.ChenPlan.H2Statement] using h2
  · simpa only [Submission.ChenPlan.H3Statement] using h3

end Work.ChenPlan.Assembly
