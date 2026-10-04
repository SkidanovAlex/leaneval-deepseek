import Mathlib
import Submission.Work.Diff.GE.smp_defs
import Submission.Work.Diff.GE.smp_crux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.MP

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- **Fermat on a manifold, local form.** A smooth function with a local maximum at `x₀` has
vanishing differential there.

The proof walks along a local integral curve `γ` of a smooth extension of the direction `v`
(`exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless`); the composite `u ∘ γ` has a local maximum
at `0`, so its derivative vanishes (`IsLocalMax.deriv_eq_zero`), and the chain rule along curves
(`Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve`) transfers this to `mvfderiv I u x₀ v`. -/
theorem mvfderiv_eq_zero_of_isLocalMax
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M]
    (u : M → ℝ) (hu : CMDiff ∞ u) (x₀ : M) (hmax : ∀ᶠ y in 𝓝 x₀, u y ≤ u x₀) :
    mvfderiv I u x₀ = 0 := by
  ext v
  obtain ⟨hEs, hEx⟩ := Work.Diff.GE.smoothExt_spec (I := I) x₀ v
  have hsec : CMDiffAt 1 (T% (smoothExt x₀ v)) x₀ := hEs.contMDiffAt.of_le (by simp)
  obtain ⟨γ, hγ0, hγ⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless (t₀ := (0 : ℝ)) hsec
  have hγmd : MDifferentiableAt 𝓘(ℝ) I γ 0 := hγ.hasMFDerivAt.mdifferentiableAt
  have humd : MDifferentiableAt I 𝓘(ℝ, ℝ) u (γ 0) := hu.mdifferentiableAt (by simp)
  -- the velocity of `γ` at `0` is `v`
  have hvm : mfderiv 𝓘(ℝ) I γ 0 (1 : ℝ) = v := by
    rw [Work.Diff.GE.Smp.mfderiv_eq_of_isMIntegralCurveAt hγ, hγ0, hEx]
  -- chain rule along `γ`
  have hchain := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I) (g := u) (γ := γ)
    (t := 0) humd hγmd
  rw [hvm, hγ0] at hchain
  -- the composite has a local maximum at `0`
  have hmax' : ∀ᶠ y in 𝓝 (γ 0), u y ≤ u (γ 0) := by
    rw [hγ0]
    exact hmax
  have hmaxcomp : IsLocalMax (u ∘ γ) 0 := by
    filter_upwards [hγ.continuousAt.eventually hmax'] with s hs
    simpa only [Function.comp_apply] using hs
  rw [hchain, IsLocalMax.deriv_eq_zero hmaxcomp]
  simp

/-- **The second derivative test for `hessAt` at a local maximum.** If a smooth function `u` has a
local maximum at `x₀`, then every diagonal value of its Hessian at `x₀` is `≤ 0`.

At a local maximum the differential vanishes (`mvfderiv_eq_zero_of_isLocalMax`), so the connection
term in `hessAt` drops out and `hessAt g u x₀ v v` is the second derivative of `u` along the
integral curve of the smooth extension `smoothExt x₀ v`; that curve has a local maximum at `0`, and
the second derivative at a local maximum is `≤ 0`
(`Work.Diff.GE.Smp.deriv_deriv_nonpos_of_isLocalMax`). -/
theorem hessAt_nonpos_of_isLocalMax
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M]
    (g : SMet I M) (u : M → ℝ) (hu : CMDiff ∞ u) (x₀ : M)
    (hmax : ∀ᶠ y in 𝓝 x₀, u y ≤ u x₀) (v : TangentSpace I x₀) :
    hessAt g u x₀ v v ≤ 0 := by
  -- Fermat: the differential of `u` vanishes at the local maximum
  have hcrit : mvfderiv I u x₀ = 0 := mvfderiv_eq_zero_of_isLocalMax u hu x₀ hmax
  obtain ⟨hEs, hEx⟩ := Work.Diff.GE.smoothExt_spec (I := I) x₀ v
  have hsec : CMDiffAt 1 (T% (smoothExt x₀ v)) x₀ := hEs.contMDiffAt.of_le (by simp)
  obtain ⟨γ, hγ0, hγ⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless (t₀ := (0 : ℝ)) hsec
  have hγmd : MDifferentiableAt 𝓘(ℝ) I γ 0 := hγ.hasMFDerivAt.mdifferentiableAt
  -- the velocity of `γ` at `0` is `v`
  have hvm : mfderiv 𝓘(ℝ) I γ 0 (1 : ℝ) = v := by
    rw [Work.Diff.GE.Smp.mfderiv_eq_of_isMIntegralCurveAt hγ, hγ0, hEx]
  -- the connection term in `hessAt` vanishes at the critical point
  have hhess : hessAt g u x₀ v v
      = mvfderiv I (fun y : M => mvfderiv I u y (smoothExt x₀ v y)) x₀ v := by
    rw [hessAt, hcrit, zero_apply, sub_zero]
  rw [hhess]
  -- chain rule along `γ` for the smooth function `y ↦ du_y (X_y)`
  have hFmd : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => mvfderiv I u y (smoothExt x₀ v y)) (γ 0) :=
    (Work.Diff.GE.contMDiff_mvfderiv_smoothExt hu x₀ v).contMDiffAt.mdifferentiableAt (by simp)
  have hchain := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I)
    (g := fun y : M => mvfderiv I u y (smoothExt x₀ v y)) (γ := γ) (t := 0) hFmd hγmd
  rw [hvm, hγ0] at hchain
  rw [hchain]
  -- `deriv (u ∘ γ)` agrees near `0` with `s ↦ du_{γ s}(X_{γ s})`
  have hEq : (fun s : ℝ => mvfderiv I u (γ s) (smoothExt x₀ v (γ s)))
      =ᶠ[𝓝 0] deriv (u ∘ γ) := by
    filter_upwards [hγ] with s hs
    have hsmd : MDifferentiableAt 𝓘(ℝ) I γ s := hs.mdifferentiableAt
    have humd : MDifferentiableAt I 𝓘(ℝ, ℝ) u (γ s) := hu.mdifferentiableAt (by simp)
    have h1 := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I) (g := u) (γ := γ)
      (t := s) humd hsmd
    rw [Work.Diff.GE.Smp.mfderiv_eq_of_hasMFDerivAt hs] at h1
    exact h1
  have hkey : deriv ((fun y : M => mvfderiv I u y (smoothExt x₀ v y)) ∘ γ) 0
      = deriv (deriv (u ∘ γ)) 0 := hEq.deriv_eq
  rw [hkey]
  -- the second derivative test for `u ∘ γ`, which has a local maximum at `0`
  have hmax' : ∀ᶠ y in 𝓝 (γ 0), u y ≤ u (γ 0) := by
    rw [hγ0]
    exact hmax
  have hmaxcomp : IsLocalMax (u ∘ γ) 0 := by
    filter_upwards [hγ.continuousAt.eventually hmax'] with s hs
    simpa only [Function.comp_apply] using hs
  have hf0 : deriv (u ∘ γ) 0 = 0 := by
    have h1 := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I) (g := u) (γ := γ)
      (t := 0) (hu.mdifferentiableAt (by simp)) hγmd
    rw [hvm, hγ0] at h1
    rw [← h1, hcrit]
    simp
  have hcont : ContinuousAt (u ∘ γ) 0 := hu.continuous.continuousAt.comp hγ.continuousAt
  exact Work.Diff.GE.Smp.deriv_deriv_nonpos_of_isLocalMax hf0 hcont hmaxcomp

end Work.Diff.MP
