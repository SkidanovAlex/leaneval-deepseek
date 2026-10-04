/-
# Auxiliary calculus lemmas for the `d = 2` phase function

The two computations that every derivative of the phase function
`phaseShape A B Ξ ϑ Θ τ F G` uses:

* the chain rule for a real function of a real-valued function on a manifold,
  `mvfderiv I (fun y => φ (f y)) x v = deriv φ (f x) * mvfderiv I f x v`;
* the product rule `mvfderiv I (fun y => F y * G y) x v = F x * mvfderiv I G x v +
  G x * mvfderiv I F x v`.

Both are proved by reducing `mvfderiv` to `mfderiv` (`mvfderiv_eq_fderiv`) after applying
Mathlib's composition lemmas.
-/
import Mathlib
import Submission.Work.Diff.Dim2.PhaseDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.Dim2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Chain rule for `mvfderiv` and a real function of one real variable.** -/
theorem mvfderiv_comp_scalar {φ : ℝ → ℝ} {f : M → ℝ} {x : M} {v : TangentSpace I x}
    (hφ : DifferentiableAt ℝ φ (f x)) (hf : MDifferentiableAt I 𝓘(ℝ,ℝ) f x) :
    mvfderiv I (fun y => φ (f y)) x v = deriv φ (f x) * mvfderiv I f x v := by
  have h := mvfderiv_comp_apply (I := 𝓘(ℝ,ℝ)) (I' := I) (f := f) (g := φ) x
    hφ.mdifferentiableAt hf v
  change (mvfderiv I (φ ∘ f) x) v = deriv φ (f x) * mvfderiv I f x v
  rw [h]
  have h1 : (mvfderiv (I := 𝓘(ℝ,ℝ)) φ (f x)) ((mfderiv% f x) v)
      = (fderiv ℝ φ (f x)) ((mfderiv% f x) v) :=
    congrArg (fun L : ℝ →L[ℝ] ℝ => L ((mfderiv% f x) v)) mvfderiv_eq_fderiv
  rw [h1, show (mfderiv% f x) v = mvfderiv I f x v from rfl,
    hφ.hasDerivAt.hasFDerivAt.fderiv, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  ring

/-- **Product rule for `mvfderiv` of two real-valued functions.** -/
theorem mvfderiv_mul_apply {F G : M → ℝ} {x : M} {v : TangentSpace I x}
    (hF : MDifferentiableAt I 𝓘(ℝ,ℝ) F x) (hG : MDifferentiableAt I 𝓘(ℝ,ℝ) G x) :
    mvfderiv I (fun y => F y * G y) x v = F x * mvfderiv I G x v + G x * mvfderiv I F x v := by
  rw [show mvfderiv I (fun y : M => F y * G y) x = mvfderiv I (F * G) x from rfl]
  rw [mvfderiv_mul hF hG]
  simp [smul_eq_mul]

/-- **Additivity of `mvfderiv` for real-valued functions.** -/
theorem mvfderiv_add_apply {F G : M → ℝ} {x : M} {v : TangentSpace I x}
    (hF : MDifferentiableAt I 𝓘(ℝ,ℝ) F x) (hG : MDifferentiableAt I 𝓘(ℝ,ℝ) G x) :
    mvfderiv I (fun y => F y + G y) x v = mvfderiv I F x v + mvfderiv I G x v := by
  rw [show mvfderiv I (fun y : M => F y + G y) x = mvfderiv I (F + G) x from rfl]
  rw [mvfderiv_add hF hG]
  rfl

/-- **`mvfderiv` of a constant function.** -/
theorem mvfderiv_const_apply {c : ℝ} {x : M} {v : TangentSpace I x} :
    mvfderiv I (fun _ : M => c) x v = 0 := by
  rw [mvfderiv_const (I := I) c]
  exact zero_apply v

/-- **Subtraction rule for `mvfderiv` of real-valued functions.** -/
theorem mvfderiv_sub_apply {F G : M → ℝ} {x : M} {v : TangentSpace I x}
    (hF : MDifferentiableAt I 𝓘(ℝ,ℝ) F x) (hG : MDifferentiableAt I 𝓘(ℝ,ℝ) G x) :
    mvfderiv I (fun y => F y - G y) x v = mvfderiv I F x v - mvfderiv I G x v := by
  rw [show mvfderiv I (fun y : M => F y - G y) x = mvfderiv I (F - G) x from rfl]
  rw [mvfderiv_sub hF hG]
  rfl

/-- **`mvfderiv` of a constant minus a function.** -/
theorem mvfderiv_const_sub_apply {c : ℝ} {F : M → ℝ} {x : M} {v : TangentSpace I x}
    (hF : MDifferentiableAt I 𝓘(ℝ,ℝ) F x) :
    mvfderiv I (fun y => c - F y) x v = -mvfderiv I F x v := by
  rw [show mvfderiv I (fun y : M => c - F y) x
      = mvfderiv I ((fun _ : M => c) - F) x from rfl]
  rw [mvfderiv_sub (mdifferentiableAt_const (c := c)) hF]
  simp only [sub_apply, mvfderiv_const_apply, zero_sub]

/-- **`mvfderiv` of a function minus a constant.** -/
theorem mvfderiv_sub_const_apply {c : ℝ} {F : M → ℝ} {x : M} {v : TangentSpace I x}
    (hF : MDifferentiableAt I 𝓘(ℝ,ℝ) F x) :
    mvfderiv I (fun y => F y - c) x v = mvfderiv I F x v := by
  rw [show mvfderiv I (fun y : M => F y - c) x
      = mvfderiv I (F - (fun _ : M => c)) x from rfl]
  rw [mvfderiv_sub hF (mdifferentiableAt_const (c := c))]
  simp only [sub_apply, mvfderiv_const_apply, sub_zero]

/-- **`mvfderiv` of a constant plus a function.** -/
theorem mvfderiv_const_add_apply {c : ℝ} {F : M → ℝ} {x : M} {v : TangentSpace I x}
    (hF : MDifferentiableAt I 𝓘(ℝ,ℝ) F x) :
    mvfderiv I (fun y => c + F y) x v = mvfderiv I F x v := by
  rw [show mvfderiv I (fun y : M => c + F y) x
      = mvfderiv I ((fun _ : M => c) + F) x from rfl]
  rw [mvfderiv_add (mdifferentiableAt_const (c := c)) hF]
  simp only [add_apply, mvfderiv_const_apply, zero_add]

/-- **`mvfderiv` is invariant under eventual equality.** -/
theorem mvfderiv_congr_of_eventuallyEq {f₁ f : M → ℝ} {x : M} {v : TangentSpace I x}
    (h : f₁ =ᶠ[𝓝 x] f) : mvfderiv I f₁ x v = mvfderiv I f x v := by
  rw [mvfderiv, mvfderiv, h.mfderiv_eq]
  simp only [ContinuousLinearMap.comp_apply]
  rw [h.eq_of_nhds]
  rfl

end Work.Diff.Dim2
