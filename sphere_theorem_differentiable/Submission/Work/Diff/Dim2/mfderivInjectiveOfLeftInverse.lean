import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set Filter

theorem mfderivInjectiveOfLeftInverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : M → F} {Ψ : F → M} {x : M}
    (hΦ : MDifferentiableAt I 𝓘(ℝ, F) Φ x)
    (hΨ : MDifferentiableAt 𝓘(ℝ, F) I Ψ (Φ x))
    (h : ∀ᶠ y in 𝓝 x, Ψ (Φ y) = y) :
    Function.Injective (mfderiv I 𝓘(ℝ, F) Φ x) := by
  -- `Ψ ∘ Φ =ᶠ[𝓝 x] id`: the derivative of the identity gives the derivative of `Ψ ∘ Φ`,
  -- while the chain rule gives the composition of the two differentials.
  have hid : HasMFDerivAt I I (fun y => Ψ (Φ y)) x
      (((tangentSpaceCast I x (Ψ (Φ x))) :
        TangentSpace I x →L[ℝ] TangentSpace I (Ψ (Φ x))) ∘SL
        ContinuousLinearMap.id ℝ (TangentSpace I x)) :=
    (hasMFDerivAt_id (I := I) x).congr_of_eventuallyEq h
  have hcomp : HasMFDerivAt I I (fun y => Ψ (Φ y)) x
      ((mfderiv 𝓘(ℝ, F) I Ψ (Φ x)).comp (mfderiv I 𝓘(ℝ, F) Φ x)) :=
    (hΨ.hasMFDerivAt).comp x (hΦ.hasMFDerivAt)
  have hkey := hasMFDerivAt_unique hid hcomp
  -- Consequently `(DΨ) ∘SL (DΦ)` vanishes on the kernel of `DΦ`, and the left factor
  -- `tangentSpaceCast I x (Ψ (Φ x))` is a linear equivalence (its underlying map is the identity).
  intro v w hvw
  have hu : mfderiv I 𝓘(ℝ, F) Φ x (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  have h2 := congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I (Ψ (Φ x)) => L (v - w)) hkey
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hu, map_zero] at h2
  have h3 : v - w = 0 := h2
  exact sub_eq_zero.mp h3

end Work.Diff.Dim2
