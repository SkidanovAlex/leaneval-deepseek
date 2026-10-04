import Mathlib
import Submission.Work.Diff.Dim2.AmbientD

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set Filter

/-- **Injectivity of the differential is preserved by reindexing the target.**

Precomposing `G` with the linear isometry `(reindexLI hdim3).symm : ℝ³ → ℝ^{finrank ℝ E + 1}` does
not destroy injectivity of the differential: by the chain rule the differential of
`(reindexLI hdim3).symm ∘ G` at `x` is the composite of the (injective) linear isometry with
`mfderiv G x`, hence injective as well. -/
theorem ambDIso
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (hdim3 : Module.finrank ℝ E + 1 = 3)
    {G : M → EuclideanSpace ℝ (Fin 3)} {x : M}
    (hG : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) G x)
    (hinj : Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) G x)) :
    Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)))
      (fun y : M => (Work.Diff.Dim2.reindexLI hdim3).symm (G y)) x) := by
  -- The reindexing, as a continuous linear equivalence.
  set L := (Work.Diff.Dim2.reindexLI hdim3).symm.toContinuousLinearEquiv with hL
  -- It is mdifferentiable at every point (it is linear).
  have hLmd : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)))
      (fun z => (Work.Diff.Dim2.reindexLI hdim3).symm z) (G x) :=
    ContinuousLinearEquiv.mdifferentiableAt (𝕜 := ℝ) (x := G x) L
  -- Chain rule: the differential of the composite is `L` applied to the differential of `G`.
  have key : ∀ v : TangentSpace I x,
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)))
        (fun y : M => (Work.Diff.Dim2.reindexLI hdim3).symm (G y)) x v
      = (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)))
          ((mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) G x) v) := by
    intro v
    show (mfderiv% ((fun z => (Work.Diff.Dim2.reindexLI hdim3).symm z) ∘ G) x) v
      = (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)))
          ((mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) G x) v)
    rw [mfderiv_comp_apply _ hLmd hG]
    exact congr($(ContinuousLinearEquiv.mfderiv_eq (𝕜 := ℝ) (x := G x) L)
      ((mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) G x) v))
  -- Injectivity: a vector in the kernel of the composite differential dies in two steps.
  intro a b hab
  have hzero : (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)))
        (fun y : M => (Work.Diff.Dim2.reindexLI hdim3).symm (G y)) x) (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have h3 : (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)))
      ((mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) G x) (a - b)) = 0 :=
    (key (a - b)).symm.trans hzero
  have h4 : (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)))
      ((mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) G x) (a - b))
      = (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) 0 := by
    rw [h3, map_zero]
  have h2 : (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) G x) (a - b) = 0 := L.injective h4
  exact sub_eq_zero.mp (hinj (by rw [h2, map_zero]))

end Work.Diff.Dim2
