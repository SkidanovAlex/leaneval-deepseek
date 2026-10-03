import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.sampling_principle_variation_kernel_lp
import Submission.Work.BourgainPlan.IonescuWainger.OpArcLinear
import Submission.Work.BourgainPlan.IonescuWainger.msw_torsion_kernel

/-!
# The decimated (periodised) sampling principle in kernel form, and on all of `ℓᵖ(ℤ)`

`Work.BourgainPlan.IonescuWainger.sampling_principle_variation_decimated` (KMSZ Definition 5.1(3),
the Magyar–Stein–Wainger sampling principle in the form used by §6.3, i.e. MST Theorem 3.1) states
the `ℓᵖ(ℤ)`-variation bound for the **decimated kernel** `j ↦ Q·[Q ∣ j]·∫ m ξ e^{2πi j ξ} dξ`,
for **finitely supported** inputs.

Two packaging steps are needed before it can be *composed* with the Ionescu–Wainger input for the
weight factor of the major-arc model (KMSZ (6.22)):

* `decimatedKernel` names that kernel, and
  **`sampling_principle_variation_decimated_kernel`** restates the sampling principle in the
  kernel form `∫⁻_k (V²(Σ_{j ∈ a.support} K n (k-j) a j))^p ≤ ofReal ((C A)^p) · lpPow p a` which is
  the hypothesis consumed by the extension lemma
  `Work.BourgainPlan.IonescuWainger.sampling_principle_variation_kernel_lp`;
* **`sampling_principle_variation_decimated_lp`** is the resulting *operator-norm* form (the input
  an arbitrary `h ∈ ℓᵖ(ℤ)`, the family defined by the absolutely convergent kernel sum), which is
  the shape in which KMSZ use the sampling principle — as a bound `ℓᵖ → S` on the *whole* space, so
  that it composes with the Theorem 1.9 bound for the weight factor.

Together with `Work.BourgainPlan.Thm52.largeScaleBoundF_comp`-type bookkeeping this produces the
`LargeScaleBound` input of KMSZ Theorem 5.2 for the §6.3 model family; see `Thm52/STATUS.md`.
-/

open MeasureTheory
open scoped ENNReal BigOperators Interval

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.BourgainPlan.Thm52

noncomputable section

/-- **The decimated (periodised) kernel** of a symbol supported in the ball of radius `1/(2Q)`:
`j ↦ Q · [Q ∣ j] · ∫_{-1/2}^{1/2} m ξ e^{2πi j ξ} dξ`.  It is the kernel of the periodisation
`ξ ↦ Σ_{a < Q} m (ξ - a/Q)` of `m` (equivalently: of the `ℤ`-side multiplier
`T_ℤ[J_1 | m K_{Q}]` of KMSZ (5.5)). -/
def decimatedKernel (Q : ℕ) (m : ℝ → ℂ) (j : ℤ) : ℂ :=
  (Q : ℂ) * (if (Q : ℤ) ∣ j then
    (∫ ξ in (-(1/2):ℝ)..(1/2), m ξ *
      Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (ξ : ℂ)))) else 0)

end

end Work.BourgainPlan.Thm52
