/-
# Layer C2 (DeTurck pull-back): metric compatibility of the pulled-back connection

This file proves

`Work.Diff.STE.C2.pullCov_metric_compat`,

namely that the pull-back `pullCov φ (lcOf g)` of the Levi-Civita connection of a smooth metric `g`
along a diffeomorphism `φ` is compatible with the pull-back metric `pullMetBilin φ g` — and, unlike
the sibling file `pullCov_leibniz.lean` (which proves the same Leibniz rule for *globally smooth*
fields), it does so for fields that are only required to be differentiable *at the point* `x`.

The mathematical content is the classical naturality of the metric compatibility of a connection
under a diffeomorphism.  Writing `W = pushField φ σ`, `V = pushField φ Z` for the push-forwards,

* `pullMetBilin φ g y (σ y) (Z y) = g(φ y)(W (φ y), V (φ y))`, so the left-hand side is the
  derivative of the pairing of `W` and `V` at `φ x` along `dφ_x v` (chain rule, plus the fact that
  the push-forward of a field differentiable at `x` is differentiable at `φ x`),
* the right-hand side is, by the definition of `pullCovFun` and the cancellation of `dφ ∘ dφ⁻¹`,
  `g(φ x)(∇_{dφ_x v} W, V (φ x)) + g(φ x)(W (φ x), ∇_{dφ_x v} V)`,
* and these two agree by metric compatibility of `lcOf g` at the single point `φ x`.

The pointwise form of metric compatibility (`lcOf_leibniz_at` below) is proved here from Mathlib's
`CovariantDerivative.isMetricCompatible_leviCivitaConnection` and
`IsMetricCompatible.mvfderiv_inner_eq`: it does not need `[I.Boundaryless]`, `[T2Space M]` nor the
contract `LCSmooth I M` (which the workspace's copy `Work.Diff.EXT.mvfderiv_metric_pairing_split`
takes as a hypothesis), which is what makes it applicable to the hypotheses of the target statement.
-/

import Mathlib
import Submission.Work.Diff.STE.C2.Defs
import Submission.Work.Diff.STE.C2.PullCovAux
import Submission.Work.Diff.STE.C2.pullCov_leibniz

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

namespace Work.Diff.STE.C2

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- **Pointwise metric compatibility of the Levi-Civita connection.**

For a smooth metric `g` and sections `W`, `V` that are only assumed differentiable *at the point*
`y`, the directional derivative of the pairing `q ↦ g.inner q (W q) (V q)` at `y` in the direction
`v ∈ T_yM` splits as `g(∇_v W, V) + g(W, ∇_v V)`, where `∇ = lcOf g`.

Note the hypotheses: no `[I.Boundaryless]`, no `[T2Space M]`, and no `LCSmooth I M` — the
compatibility of `lcOf g` is taken directly from Mathlib's
`CovariantDerivative.isMetricCompatible_leviCivitaConnection`, transported along the definitional
identifications `lcOf g = leviCivitaConnection I M` and `g.inner = inner ℝ` that hold once
`RiemannianBundle := ⟨g.toRiemannianMetric⟩` is installed. -/
theorem lcOf_leibniz_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g : Submission.Diff.SMet I M) {W V : Π y : M, TangentSpace I y} {y : M} {v : TangentSpace I y}
    (hW : MDiffAt (T% W) y) (hV : MDiffAt (T% V) y) :
    mvfderiv I (fun z : M ↦ g.inner z (W z) (V z)) y v
      = g.inner y ((Submission.Diff.lcOf g) W y v) (V y)
        + g.inner y (W y) ((Submission.Diff.lcOf g) V y v) := by
  classical
  -- Work with `g` as the instance metric on the fibres, so that `g.inner = inner ℝ` and `lcOf g` is
  -- Mathlib's Levi-Civita connection of that instance metric.
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hmet := CovariantDerivative.isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  -- the Leibniz rule `d ⟪W, V⟫_y v = ⟪∇_v W, V⟫ + ⟪W, ∇_v V⟫` of metric compatibility
  have hmain := hmet.mvfderiv_inner_eq (x := y) (FiberBundle.extend E v) hW hV
  simp only [FiberBundle.extend_apply_self] at hmain
  change mvfderiv I (fun q : M => inner ℝ (W q) (V q)) y v
      = inner ℝ ((CovariantDerivative.leviCivitaConnection I M) W y v) (V y)
        + inner ℝ (W y) ((CovariantDerivative.leviCivitaConnection I M) V y v)
  exact hmain

theorem pullCov_metric_compat
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (φ : Diffeomorph I I M M (⊤ : ℕ∞)) (g : Submission.Diff.SMet I M)
    (σ Z : Π y : M, TangentSpace I y) (x : M)
    (hσ : MDifferentiableAt I I.tangent (fun y : M ↦ (⟨y, σ y⟩ : TangentBundle I M)) x)
    (hZ : MDifferentiableAt I I.tangent (fun y : M ↦ (⟨y, Z y⟩ : TangentBundle I M)) x)
    (v : TangentSpace I x) :
    mvfderiv I (fun y : M ↦ Work.Diff.STE.C2.pullMetBilin φ g y (σ y) (Z y)) x v
      = Work.Diff.STE.C2.pullMetBilin φ g x
          ((Work.Diff.STE.C2.pullCov φ (Submission.Diff.lcOf g)) σ x v) (Z x)
        + Work.Diff.STE.C2.pullMetBilin φ g x (σ x)
          ((Work.Diff.STE.C2.pullCov φ (Submission.Diff.lcOf g)) Z x v) := by
  classical
  -- `g` as the instance metric, so that the inner products of the two sides are comparable.
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) := inferInstance
  -- the bundled pull-back is its raw underlying function
  change mvfderiv I (fun y : M ↦ Work.Diff.STE.C2.pullMetBilin φ g y (σ y) (Z y)) x v
      = Work.Diff.STE.C2.pullMetBilin φ g x
          (Work.Diff.STE.C2.pullCovFun φ (Submission.Diff.lcOf g) σ x v) (Z x)
        + Work.Diff.STE.C2.pullMetBilin φ g x (σ x)
          (Work.Diff.STE.C2.pullCovFun φ (Submission.Diff.lcOf g) Z x v)
  -- the push-forwards of `σ` and `Z` are differentiable at `φ x`
  have hW : MDiffAt (T% (Work.Diff.STE.C2.pushField φ σ)) (φ x) :=
    Work.Diff.STE.C2.pullCov_mdiff_pushField φ hσ
  have hV : MDiffAt (T% (Work.Diff.STE.C2.pushField φ Z)) (φ x) :=
    Work.Diff.STE.C2.pullCov_mdiff_pushField φ hZ
  -- hence so is their metric pairing
  have hpair : MDiffAt (fun z : M ↦ g.inner z (Work.Diff.STE.C2.pushField φ σ z)
      (Work.Diff.STE.C2.pushField φ Z z)) (φ x) :=
    MDifferentiableAt.inner_bundle (F := E) (E := fun z : M ↦ TangentSpace I z) (b := id) hW hV
  -- the pulled-back metric evaluated on `σ`, `Z` is the pairing of the push-forwards, composed
  -- with `φ`
  have hfun : (fun y : M ↦ Work.Diff.STE.C2.pullMetBilin φ g y (σ y) (Z y))
      = (fun z : M ↦ g.inner z (Work.Diff.STE.C2.pushField φ σ z)
          (Work.Diff.STE.C2.pushField φ Z z)) ∘ (φ : M → M) := by
    funext y
    simp only [Function.comp_apply, Work.Diff.STE.C2.pullMetBilin_apply]
    rw [Work.Diff.STE.C2.pushField_apply_self (φ := φ) (Y := σ) y,
        Work.Diff.STE.C2.pushField_apply_self (φ := φ) (Y := Z) y]
  rw [hfun]
  -- chain rule
  rw [mvfderiv_comp_apply x hpair (Work.Diff.STE.C2.mdifferentiableAt_of_diffeomorph φ x) v]
  -- unfold the pull-backs: `dφ ∘ dφ⁻¹` cancels
  rw [Work.Diff.STE.C2.pullMetBilin_pullCovFun_fst (φ := φ) (g := g)
        (cov := Submission.Diff.lcOf g) (Y := σ) (Z := Z) x v,
      Work.Diff.STE.C2.pullMetBilin_pullCovFun_snd (φ := φ) (g := g)
        (cov := Submission.Diff.lcOf g) (Y := σ) (Z := Z) x v]
  -- and the Leibniz rule for the Levi-Civita connection of `g` at the point `φ x`
  exact lcOf_leibniz_at g hW hV

end Work.Diff.STE.C2
