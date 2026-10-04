import Mathlib
import Submission.Work.Diff.GE.smp_defs
import Submission.Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve
import Submission.Commons.Analysis.Calculus.deriv_deriv_nonneg_of_isLocalMin

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The two analytic facts behind the scalar maximum principle

* `Work.Diff.GE.Smp.deriv_deriv_nonpos_of_isLocalMax`: a twice differentiable function on `ℝ` with
  a local maximum at `0`, `deriv f 0 = 0` and continuous at `0` has `deriv (deriv f) 0 ≤ 0`.
* `Work.Diff.GE.Smp.mvfderiv_eq_zero_of_isMax`: Fermat's rule on a manifold (at a global maximum
  the differential vanishes).
* `Work.Diff.GE.Smp.hessAt_self_nonpos_of_isCriticalMax`: at a global maximum which is also a
  critical point every diagonal value of `hessAt` is `≤ 0`.

The manifold statements are proved by walking along the integral curve of a smooth extension of
`v` and using the chain rule along curves (`Commons...mvfderiv_comp_curve`).
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set Filter VectorField CovariantDerivative Metric

namespace Work.Diff.GE.Smp

/-- The second derivative at a local maximum is `≤ 0`. -/
theorem deriv_deriv_nonpos_of_isLocalMax {f : ℝ → ℝ} (hf0 : deriv f 0 = 0)
    (hcont : ContinuousAt f 0) (hmax : IsLocalMax f 0) : deriv (deriv f) 0 ≤ 0 := by
  by_contra hle
  rw [not_le] at hle
  -- if the second derivative were positive, `0` would be a local minimum as well
  have hmin : IsLocalMin f 0 := isLocalMin_of_deriv_deriv_pos hle hf0 hcont
  have heq : f =ᶠ[𝓝 0] (fun _ => f 0) := by
    filter_upwards [hmax, hmin] with x hx1 hx2
    exact le_antisymm hx1 hx2
  -- hence `f` is locally constant and its second derivative vanishes
  have hderiv : deriv f =ᶠ[𝓝 0] (fun _ => (0 : ℝ)) := by
    filter_upwards [heq.deriv] with x hx
    rw [hx, deriv_const]
  have h0 : deriv (deriv f) 0 = 0 := by rw [hderiv.deriv_eq, deriv_const]
  linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]

/-- The velocity of a curve whose derivative is the field `X` is `X` itself. -/
theorem mfderiv_eq_of_hasMFDerivAt {γ : ℝ → M} {X : Π x : M, TangentSpace I x} {t : ℝ}
    (h : HasMFDerivAt% γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (X (γ t)))) :
    mfderiv 𝓘(ℝ) I γ t (1 : ℝ) = X (γ t) := by
  rw [h.mfderiv]
  show (1 : ℝ) • X (γ t) = X (γ t)
  rw [one_smul]

/-- The velocity of an integral curve is the field itself. -/
theorem mfderiv_eq_of_isMIntegralCurveAt {γ : ℝ → M} {X : Π x : M, TangentSpace I x} {t : ℝ}
    (h : IsMIntegralCurveAt γ X t) : mfderiv 𝓘(ℝ) I γ t (1 : ℝ) = X (γ t) :=
  mfderiv_eq_of_hasMFDerivAt h.hasMFDerivAt

/-- **Fermat on a manifold**: a smooth function attaining its global maximum at `x₀` has vanishing
differential there. -/
theorem mvfderiv_eq_zero_of_isMax (u : M → ℝ) (hu : CMDiff ∞ u) (x₀ : M)
    (hmax : ∀ y, u y ≤ u x₀) : mvfderiv I u x₀ = 0 := by
  ext v
  obtain ⟨hEs, hEx⟩ := smoothExt_spec (I := I) x₀ v
  have hsec : CMDiffAt 1 (T% (smoothExt x₀ v)) x₀ := hEs.contMDiffAt.of_le (by simp)
  obtain ⟨γ, hγ0, hγ⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless (t₀ := (0 : ℝ)) hsec
  have hγmd : MDifferentiableAt 𝓘(ℝ) I γ 0 := hγ.hasMFDerivAt.mdifferentiableAt
  have humd : MDifferentiableAt I 𝓘(ℝ, ℝ) u (γ 0) := hu.mdifferentiableAt (by simp)
  -- the velocity of `γ` at `0` is `v`
  have hvm : mfderiv 𝓘(ℝ) I γ 0 (1 : ℝ) = v := by
    rw [mfderiv_eq_of_isMIntegralCurveAt hγ, hγ0, hEx]
  have hchain := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I) (g := u) (γ := γ) (t := 0) humd hγmd
  rw [hvm, hγ0] at hchain
  -- the composite has a maximum at `0`
  have hmaxcomp : IsLocalMax (u ∘ γ) 0 := by
    refine Filter.Eventually.of_forall fun s => ?_
    simp only [Function.comp_apply]
    rw [hγ0]
    exact hmax (γ s)
  rw [hchain, IsLocalMax.deriv_eq_zero hmaxcomp]
  simp

/-- At a global maximum which is also a critical point, every diagonal value of the Hessian is
`≤ 0`. -/
theorem hessAt_self_nonpos_of_isCriticalMax (g : SMet I M) (u : M → ℝ) (hu : CMDiff ∞ u)
    (x₀ : M) (hcrit : mvfderiv I u x₀ = 0) (hmax : ∀ y, u y ≤ u x₀)
    (v : TangentSpace I x₀) : hessAt g u x₀ v v ≤ 0 := by
  obtain ⟨hEs, hEx⟩ := smoothExt_spec (I := I) x₀ v
  have hsec : CMDiffAt 1 (T% (smoothExt x₀ v)) x₀ := hEs.contMDiffAt.of_le (by simp)
  obtain ⟨γ, hγ0, hγ⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless (t₀ := (0 : ℝ)) hsec
  have hγmd : MDifferentiableAt 𝓘(ℝ) I γ 0 := hγ.hasMFDerivAt.mdifferentiableAt
  have hvm : mfderiv 𝓘(ℝ) I γ 0 (1 : ℝ) = v := by
    rw [mfderiv_eq_of_isMIntegralCurveAt hγ, hγ0, hEx]
  -- the connection term in `hessAt` vanishes at the critical point
  have hhess : hessAt g u x₀ v v
      = mvfderiv I (fun y : M => mvfderiv I u y (smoothExt x₀ v y)) x₀ v := by
    rw [hessAt, hcrit, zero_apply, sub_zero]
  rw [hhess]
  -- chain rule along `γ` for the smooth function `y ↦ du_y (X_y)`
  have hFmd : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => mvfderiv I u y (smoothExt x₀ v y)) (γ 0) :=
    (contMDiff_mvfderiv_smoothExt hu x₀ v).contMDiffAt.mdifferentiableAt (by simp)
  have hchain := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I)
    (g := fun y : M => mvfderiv I u y (smoothExt x₀ v y)) (γ := γ) (t := 0) hFmd hγmd
  rw [hvm, hγ0] at hchain
  rw [hchain]
  -- `deriv (u ∘ γ)` agrees near `0` with `s ↦ du_{γ s}(X_{γ s})`
  have hEq : (fun s : ℝ => mvfderiv I u (γ s) (smoothExt x₀ v (γ s))) =ᶠ[𝓝 0] deriv (u ∘ γ) := by
    filter_upwards [hγ] with s hs
    have hsmd : MDifferentiableAt 𝓘(ℝ) I γ s := hs.mdifferentiableAt
    have humd : MDifferentiableAt I 𝓘(ℝ, ℝ) u (γ s) := hu.mdifferentiableAt (by simp)
    have h1 := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I) (g := u) (γ := γ) (t := s) humd hsmd
    rw [mfderiv_eq_of_hasMFDerivAt hs] at h1
    exact h1
  have hkey : deriv ((fun y : M => mvfderiv I u y (smoothExt x₀ v y)) ∘ γ) 0
      = deriv (deriv (u ∘ γ)) 0 := hEq.deriv_eq
  rw [hkey]
  -- the second derivative test for `u ∘ γ`, which has a maximum at `0`
  have hmaxcomp : IsLocalMax (u ∘ γ) 0 := by
    refine Filter.Eventually.of_forall fun s => ?_
    simp only [Function.comp_apply]
    rw [hγ0]
    exact hmax (γ s)
  have hf0 : deriv (u ∘ γ) 0 = 0 := by
    have h1 := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I) (g := u) (γ := γ) (t := 0)
      (hu.mdifferentiableAt (by simp)) hγmd
    rw [hvm, hγ0] at h1
    rw [← h1, hcrit]
    simp
  have hcont : ContinuousAt (u ∘ γ) 0 := hu.continuous.continuousAt.comp hγ.continuousAt
  exact deriv_deriv_nonpos_of_isLocalMax hf0 hcont hmaxcomp

end Work.Diff.GE.Smp
