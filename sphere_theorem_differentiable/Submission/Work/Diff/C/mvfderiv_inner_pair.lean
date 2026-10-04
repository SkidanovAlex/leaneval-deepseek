import Mathlib
import Submission.Work.Diff.C.Setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- `mvfderiv` (the derivative of a vector-valued map, valued in the model space) and `mfderiv`
(the derivative, valued in the tangent space of the target) agree, since the tangent space of a
normed space at a point is identified with the normed space itself. -/
lemma mvfderiv_eq_mfderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : M → F) (x : M) :
    mvfderiv I g x = mfderiv I 𝓘(ℝ, F) g x := by
  ext v
  rfl

/-- Product rule for the manifold directional derivative of an inner product of two maps into a
normed space: `d ⟪Φ, Ψ⟫_x v = ⟪dΦ_x v, Ψ x⟫ + ⟪Φ x, dΨ_x v⟫`.  (Route: `mvfderiv_comp_apply` with
the smooth pairing `(u,w) ↦ ⟪u,w⟫` on `V × V`, or Mathlib's `HasFDerivAt.inner` in the chart.) -/
theorem mvfderiv_inner_pair
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {Φ Ψ : M → V} {x : M}
    (hΦ : MDifferentiableAt I (𝓘(ℝ, V)) Φ x) (hΨ : MDifferentiableAt I (𝓘(ℝ, V)) Ψ x)
    (v : TangentSpace I x) :
    mvfderiv I (fun y : M => Inner.inner ℝ (Φ y) (Ψ y)) x v
      = Inner.inner ℝ (mvfderiv I Φ x v) (Ψ x)
        + Inner.inner ℝ (Φ x) (mvfderiv I Ψ x v) := by
  -- The pairing `g` on `V × V`, the pair map `P`, and their derivatives.
  have hP : MDifferentiableAt I (𝓘(ℝ, V × V)) (fun y : M => (Φ y, Ψ y)) x := hΦ.prodMk_space hΨ
  have hgd : MDifferentiableAt (𝓘(ℝ, V × V)) (𝓘(ℝ, ℝ))
      (fun p : V × V => Inner.inner ℝ p.1 p.2) (Φ x, Ψ x) := by
    rw [mdifferentiableAt_iff_differentiableAt]
    exact DifferentiableAt.inner ℝ differentiableAt_fst differentiableAt_snd
  -- The Fréchet derivative of the pairing on `V × V`.
  have hLg_eq : fderiv ℝ (fun p : V × V => Inner.inner ℝ p.1 p.2) (Φ x, Ψ x)
      = (innerSL ℝ (Ψ x)) ∘L (ContinuousLinearMap.fst ℝ V V)
        + (innerSL ℝ (Φ x)) ∘L (ContinuousLinearMap.snd ℝ V V) := by
    apply ContinuousLinearMap.ext
    intro y
    rw [fderiv_inner_apply ℝ differentiableAt_fst differentiableAt_snd, fderiv_fst, fderiv_snd]
    show Inner.inner ℝ (Φ x) y.2 + Inner.inner ℝ y.1 (Ψ x)
        = Inner.inner ℝ (Ψ x) y.1 + Inner.inner ℝ (Φ x) y.2
    rw [real_inner_comm y.1 (Ψ x)]
    ring
  have hLgF : HasFDerivAt (fun p : V × V => Inner.inner ℝ p.1 p.2)
      ((innerSL ℝ (Ψ x)) ∘L (ContinuousLinearMap.fst ℝ V V)
        + (innerSL ℝ (Φ x)) ∘L (ContinuousLinearMap.snd ℝ V V)) (Φ x, Ψ x) := by
    rw [← hLg_eq]
    exact (mdifferentiableAt_iff_differentiableAt.mp hgd).hasFDerivAt
  have hLg : HasMFDerivAt 𝓘(ℝ, V × V) 𝓘(ℝ, ℝ)
      (fun p : V × V => Inner.inner ℝ p.1 p.2) (Φ x, Ψ x)
      ((innerSL ℝ (Ψ x)) ∘L (ContinuousLinearMap.fst ℝ V V)
        + (innerSL ℝ (Φ x)) ∘L (ContinuousLinearMap.snd ℝ V V)) :=
    hasMFDerivAt_iff_hasFDerivAt.mpr hLgF
  -- The derivative of the pair map.
  have hmf : mfderiv I 𝓘(ℝ, V × V) (fun y : M => (Φ y, Ψ y)) x
      = (mfderiv I 𝓘(ℝ, V) Φ x).prod (mfderiv I 𝓘(ℝ, V) Ψ x) := by
    rw [modelWithCornersSelf_prod (𝕜 := ℝ) (E := V) (F := V), ← chartedSpaceSelf_prod]
    exact mfderiv_prodMk (𝕜 := ℝ) (I := I) hΦ hΨ
  have hmfdf : mfderiv I 𝓘(ℝ, V × V) (fun y : M => (Φ y, Ψ y)) x
      = (mvfderiv I Φ x).prod (mvfderiv I Ψ x) := by
    rw [hmf, ← mvfderiv_eq_mfderiv (g := Φ) (x := x),
      ← mvfderiv_eq_mfderiv (g := Ψ) (x := x)]
    try rfl
  have hdf : HasMFDerivAt I 𝓘(ℝ, V × V) (fun y : M => (Φ y, Ψ y)) x
      ((mvfderiv I Φ x).prod (mvfderiv I Ψ x)) := by
    rw [← hmfdf]
    exact hP.hasMFDerivAt
  -- Chain rule for the composition `⟪Φ ·, Ψ ·⟫ = g ∘ P`.
  have hcomp := hLg.comp x hdf
  have hmv : mvfderiv I ((fun p : V × V => Inner.inner ℝ p.1 p.2) ∘ fun y : M => (Φ y, Ψ y)) x v
      = ((innerSL ℝ (Ψ x)) ∘L (ContinuousLinearMap.fst ℝ V V)
          + (innerSL ℝ (Φ x)) ∘L (ContinuousLinearMap.snd ℝ V V))
          (((mvfderiv I Φ x).prod (mvfderiv I Ψ x)) v) := by
    rw [mvfderiv_eq_mfderiv]
    rw [hcomp.mfderiv]
    rfl
  show (mvfderiv I ((fun p : V × V => Inner.inner ℝ p.1 p.2) ∘ fun y : M => (Φ y, Ψ y)) x) v = _
  rw [hmv, ContinuousLinearMap.prod_apply]
  show Inner.inner ℝ (Ψ x) (mvfderiv I Φ x v) + Inner.inner ℝ (Φ x) (mvfderiv I Ψ x v)
      = Inner.inner ℝ (mvfderiv I Φ x v) (Ψ x) + Inner.inner ℝ (Φ x) (mvfderiv I Ψ x v)
  rw [real_inner_comm (mvfderiv I Φ x v) (Ψ x)]

end Work.Diff.C
