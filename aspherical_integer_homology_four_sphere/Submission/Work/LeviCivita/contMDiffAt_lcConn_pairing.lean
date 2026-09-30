import Mathlib
import Submission.Work.LeviCivita.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Smoothness of the pairing of the Levi-Civita covariant derivative with a vector field

The main result of this file is

    `Work.LeviCivita.contMDiffAt_lcConn_pairing`

stating that for globally `C^∞` vector fields `σ`, `X`, `Z` on a Riemannian manifold `(M, g)` whose
metric is `C^∞` (`IsContMDiffRiemannianBundle I ∞ E _`), the function

    `x ↦ ⟪∇_X σ (x), Z x⟫`

is `C^∞` at every point, where `∇` is the Levi-Civita connection `Work.LeviCivita.lcConn`.

## Proof outline

The Levi-Civita connection satisfies the **Koszul formula** `lcConn_apply_inner`
(`Submission.Work.LeviCivita.Defs`): for vector fields differentiable at `x`,

`⟪∇_X Y, Z⟫ x = ½ ( X⟪Y,Z⟫ + Y⟪Z,X⟫ − Z⟪X,Y⟫ − ⟪Y,[X,Z]⟫ − ⟪Z,[Y,X]⟫ + ⟪X,[Z,Y]⟫ )`.

All six summands on the right-hand side are `C^∞` functions of `x`:

* the directional derivatives `x ↦ d% f x (Y x)` of a smooth scalar function `f` along a smooth
  vector field `Y` are smooth: this is `contMDiffAt_mvfderiv_of_contMDiff` below.  We prove it by
  observing that `d% f x (Y x)` is the fibre component of `tangentMap% f (T% Y x)`, that the
  tangent map of a `C^∞` map is `C^∞` (`ContMDiff.contMDiff_tangentMap`), and that for the
  tangent bundle of the model space `ℝ` the tangent-bundle trivialization is the identity
  (`contMDiffAt_totalSpace` reduces the fibre component to the trivialised fibre component);

* the inner products `x ↦ ⟪U x, V x⟫` of two smooth sections of the Riemannian bundle are smooth
  (`ContMDiffAt.inner_bundle`);

* the Lie brackets of smooth vector fields are smooth (`mlieBracket_vectorField`).

Combining these gives smoothness of the right-hand side of the Koszul formula, which hence agrees
with `x ↦ ⟪∇_X σ (x), Z x⟫`.
-/

set_option linter.unusedSectionVars false
set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.LeviCivita

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

/-! ## The directional derivative of a smooth function along a smooth vector field -/

/-- **Smoothness of the manifold derivative of a smooth function along a smooth vector field.**

If `f : M → ℝ` is `C^∞` and `Y` is a `C^∞` vector field, then
`x ↦ mvfderiv I f x (Y x)` is `C^∞` at every point.

The point is that `mvfderiv I f x (Y x)` is, by definition (up to the canonical identification of
`TangentSpace 𝓘(ℝ,ℝ) (f x)` with `ℝ`), the fibre component of `tangentMap% f (T% Y x)`; the tangent
map of a smooth map is smooth (`ContMDiff.contMDiff_tangentMap`) and the fibre component of a smooth
map into the tangent bundle of the model space `ℝ` is smooth, because for the model space the
tangent-bundle trivialisation is the identity. -/
theorem contMDiffAt_mvfderiv_of_contMDiff
    [I.Boundaryless]
    {f : M → ℝ} {Y : Π x : M, TangentSpace I x} {x₀ : M}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hY : ContMDiff I I.tangent ∞ (T% Y)) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x : M ↦ mvfderiv I f x (Y x)) x₀ := by
  -- the tangent map of `f` is smooth, hence so is its composite with the section `T% Y`
  have hT : ContMDiff I.tangent (𝓘(ℝ, ℝ)).tangent ∞ (tangentMap% f) :=
    hf.contMDiff_tangentMap (by simp)
  have hcomp : ContMDiffAt I ((𝓘(ℝ, ℝ)).tangent) ∞
      (fun x : M ↦ tangentMap% f (T% Y x)) x₀ :=
    (hT (T% Y x₀)).comp x₀ (hY x₀)
  -- its fibre component is smooth
  have hfib := (contMDiffAt_totalSpace.mp hcomp).2
  -- and for the model space the tangent-bundle trivialisation is the identity, so the fibre
  -- component is exactly `x ↦ mvfderiv I f x (Y x)`
  refine hfib.congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  intro x
  simp only [mvfderiv, ContinuousLinearMap.comp_apply]
  rw [TangentBundle.trivializationAt_apply]
  simp only [chartAt_self_eq]
  simp
  rfl

/-! ## The pairing with the Levi-Civita connection -/

open scoped Manifold ContDiff Bundle Topology in
theorem contMDiffAt_lcConn_pairing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless]
    {σ X Z : Π x : M, TangentSpace I x}
    (hσ : ContMDiff I I.tangent ∞ (T% σ)) (hX : ContMDiff I I.tangent ∞ (T% X))
    (hZ : ContMDiff I I.tangent ∞ (T% Z)) (x₀ : M) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M ↦ inner ℝ (Work.LeviCivita.lcConn (I := I) (M := M) σ x (X x)) (Z x)) x₀ := by
  -- the smoothness instances needed for the Lie bracket of smooth vector fields
  have h2M : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  have hsucc : IsManifold I (∞ + 1) M := IsManifold.of_le (n := ∞) (by simp)
  -- the three directional-derivative terms of the Koszul formula
  have h1 : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M ↦ mvfderiv I (fun y : M ↦ inner ℝ (σ y) (Z y)) x (X x)) x₀ :=
    contMDiffAt_mvfderiv_of_contMDiff
      (fun y ↦ ContMDiffAt.inner_bundle (hσ y) (hZ y)) hX
  have h2 : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M ↦ mvfderiv I (fun y : M ↦ inner ℝ (Z y) (X y)) x (σ x)) x₀ :=
    contMDiffAt_mvfderiv_of_contMDiff
      (fun y ↦ ContMDiffAt.inner_bundle (hZ y) (hX y)) hσ
  have h3 : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M ↦ mvfderiv I (fun y : M ↦ inner ℝ (X y) (σ y)) x (Z x)) x₀ :=
    contMDiffAt_mvfderiv_of_contMDiff
      (fun y ↦ ContMDiffAt.inner_bundle (hX y) (hσ y)) hZ
  -- the three Lie bracket terms: the brackets of smooth vector fields are smooth
  have hbr1 : ContMDiff I I.tangent ∞ (T% (mlieBracket I X Z)) :=
    mlieBracket_vectorField hX hZ (by simp)
  have hbr2 : ContMDiff I I.tangent ∞ (T% (mlieBracket I σ X)) :=
    mlieBracket_vectorField hσ hX (by simp)
  have hbr3 : ContMDiff I I.tangent ∞ (T% (mlieBracket I Z σ)) :=
    mlieBracket_vectorField hZ hσ (by simp)
  have h4 : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M ↦ inner ℝ (σ x) (mlieBracket I X Z x)) x₀ :=
    ContMDiffAt.inner_bundle (hσ x₀) (hbr1 x₀)
  have h5 : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M ↦ inner ℝ (Z x) (mlieBracket I σ X x)) x₀ :=
    ContMDiffAt.inner_bundle (hZ x₀) (hbr2 x₀)
  have h6 : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M ↦ inner ℝ (X x) (mlieBracket I Z σ x)) x₀ :=
    ContMDiffAt.inner_bundle (hX x₀) (hbr3 x₀)
  -- the right-hand side of the Koszul formula is smooth
  have hsum := ((((h1.add h2).sub h3).sub h4).sub h5).add h6
  have hdiv := hsum.div_const 2
  -- and it agrees with the function we are interested in, by the Koszul formula
  have hk : ∀ x : M,
      inner ℝ (Work.LeviCivita.lcConn (I := I) (M := M) σ x (X x)) (Z x) =
      (mvfderiv I (fun y : M ↦ inner ℝ (σ y) (Z y)) x (X x)
        + mvfderiv I (fun y : M ↦ inner ℝ (Z y) (X y)) x (σ x)
        - mvfderiv I (fun y : M ↦ inner ℝ (X y) (σ y)) x (Z x)
        - inner ℝ (σ x) (mlieBracket I X Z x)
        - inner ℝ (Z x) (mlieBracket I σ X x)
        + inner ℝ (X x) (mlieBracket I Z σ x)) / 2 := by
    intro x
    exact lcConn_apply_inner (I := I) (M := M) (X := X) (Y := σ) (Z := Z)
      ((hX x).mdifferentiableAt (by simp)) ((hσ x).mdifferentiableAt (by simp))
      ((hZ x).mdifferentiableAt (by simp))
  exact hdiv.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun x ↦ hk x))

end

end Work.LeviCivita
