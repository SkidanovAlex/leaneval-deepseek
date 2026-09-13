/-
The **Hessian measure input**: Chaudhuri--Trudinger's theorem `[CT]` Theorem 2.4, in the form in
which it is used in Shankar--Yuan.

`[CT]` states that the second distributional derivatives of a continuous `2`-convex function are
(matrix valued) Radon measures: `D²u = D²u \, dx + [D²u]_s`.  We package this as: for a continuous
`2`-convex `u` on a bounded open `s`, and for every open `t` with `closure t ⊆ s`, there are
`M : Fin 4 → Fin 4 → ℝ⁴ → ℝ` (the density of the absolutely continuous part, locally integrable)
and signed measures `σ i j` with `(σ i j).totalVariation ⟂ volume` (the singular part) such that
`M dx + σ` is the weak Hessian of `u` on `t` in the sense of `Submission.HasWeakHessian`.

Two restrictions on the statement are *essential*, and both are satisfied in the application
(where `s = ball 0 3` and `t = ball 0 (1/2)`):

* `t` is required to have compact closure inside `s`.  The reason is that the Hessian of a
  `2`-convex function is in general only a *Radon* measure on `s` (finite on compact subsets of
  `s`), so its singular part can have infinite total mass on `s` -- for instance
  `u(x) = g(x₁)` with `g` convex and `g'' = ∑_n δ_{1/n}` on `(0,1)` is `2`-convex and continuous,
  and its Hessian measure has infinite mass on `(0,1)⁴`.  A Mathlib `SignedMeasure` always has
  finite variation, so the decomposition can only be asserted after restricting to the compact set
  `closure t ⊆ s` (which makes the measures finite).
* `s` is required to be bounded: the Riesz representation of the functionals `φ ↦ ∫ u Δφ` is
  applied to test functions with `tsupport ⊆ s`, and these only have compact support when `s` is
  bounded.

Note that, in contrast to `Submission.WeakHessianMeasureInput`, **no weak gradient is required**:
in the paper the weak gradient is obtained from Trudinger--Wang's gradient estimate, not from
`[CT]` (see `Submission.GradFromGradient`).
-/
import Mathlib
import Submission.AlexandrovInputs

open HessianEstimates
open MeasureTheory Metric Set Filter Function
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace

set_option autoImplicit false

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-- **Chaudhuri--Trudinger `[CT]` Theorem 2.4** (Hessian measure part). -/
def HessianMeasureInput : Prop :=
  ∀ (u : ℝ⁴ → ℝ) (s : Set ℝ⁴), IsOpen s → Bornology.IsBounded s → ContinuousOn u s →
    IsTwoConvexOn u s →
    ∀ (t : Set ℝ⁴), IsOpen t → closure t ⊆ s →
      ∃ (M : Fin 4 → Fin 4 → ℝ⁴ → ℝ) (σ : Fin 4 → Fin 4 → SignedMeasure ℝ⁴),
        (∀ i j, LocallyIntegrable (M i j) volume) ∧
        (∀ i j, (σ i j).totalVariation ⟂ₘ volume) ∧
        HasWeakHessian u t M σ

end Submission
