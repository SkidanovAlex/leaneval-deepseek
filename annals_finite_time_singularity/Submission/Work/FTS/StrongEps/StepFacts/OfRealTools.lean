/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/StepFacts/OfRealTools.lean`

Small `ℝ≥0∞`-bookkeeping lemmas used by the one-order smoothing estimate for the log-coordinate
mollifier `J_ε`:

* `ofReal_integral_le_lintegral_ofReal` — `ofReal (∫ f) ≤ ∫⁻ ofReal ∘ f` for a nonnegative `f`
  (no integrability hypothesis: for a non-integrable `f` the Bochner integral is `0` by
  `integral_undef`, and the inequality is trivial);
* `ofReal_mul_ofReal` / `ofReal_sum_of_nonneg` in the shapes used below;
* the `nsmul`-bookkeeping for the finite sum over the top-order slots.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.StepFacts

set_option autoImplicit false

/-- **`ofReal` of a Bochner integral of a nonnegative function is bounded by the `lintegral`.**
No integrability hypothesis is needed: if `f` is not integrable then `∫ f = 0` by
`integral_undef` and the inequality is trivial. -/
theorem ofReal_integral_le_lintegral_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases h : Integrable f μ
  · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal h (Eventually.of_forall hf)]
  · rw [MeasureTheory.integral_undef h]
    simp

/-- `ofReal (a * b) = ofReal a * ofReal b` in the nonnegative case, in the direction used below. -/
theorem ofReal_mul_eq (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal (a * b) = ENNReal.ofReal a * ENNReal.ofReal b :=
  ENNReal.ofReal_mul ha

/-- `ofReal` of a finite sum of nonnegative reals is the sum of the `ofReal`s. -/
theorem ofReal_sum_of_nonneg {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    ENNReal.ofReal (∑ i ∈ s, f i) = ∑ i ∈ s, ENNReal.ofReal (f i) :=
  ENNReal.ofReal_sum_of_nonneg hf

/-- A finite sum of `ℝ≥0∞`-numbers each bounded by `C` is bounded by `card • C`. -/
theorem sum_le_card_nsmul {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) (C : ℝ≥0∞)
    (h : ∀ i ∈ s, f i ≤ C) : ∑ i ∈ s, f i ≤ s.card • C :=
  Finset.sum_le_card_nsmul s f C h

/-- `n • C ≤ (n : ℝ≥0∞) * C`: the `nsmul` of `ℝ≥0∞` is multiplication by the natural number. -/
theorem nsmul_le_natCast_mul (n : ℕ) (C : ℝ≥0∞) : n • C ≤ (n : ℝ≥0∞) * C :=
  le_of_eq (nsmul_eq_mul n C)

/-- Numerical bookkeeping: `1 + n * x ≤ (n + 2) * x` for `1 ≤ x` and `0 ≤ x`. -/
theorem one_add_mul_le (n : ℕ) (x : ℝ) (hx : 1 ≤ x) : 1 + (n : ℝ) * x ≤ (n + 2) * x := by
  have h0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx
  have hm : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith

end Work.FTS.StrongEps.StepFacts
