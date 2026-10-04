/-
# Layer C2 (DeTurck pull-back): smoothness of the chart matrix of the pulled-back metric

The pull-back of a smooth metric `g` along a diffeomorphism `φ` is the form

`(pullMetBilin φ g x) u v = g.inner (φ x) (dφ_x u) (dφ_x v)`

(`Work.Diff.STE.C2.Defs0`).  This file proves that its **chart matrix** in the coordinate frame of
the chart at `x₀` is smooth at `x₀`:

`x ↦ frameMat x₀ x (pullMetBilin φ g x)`.

Since `frameMat x₀ x h` is the matrix of `h` in the frame `σ_i(y) = frameVector x₀ y (bB i)`
(`Work.Diff.EXT.frameMat`), the `(i,j)`-entry of the goal is

`g.inner (φ x) (dφ_x (σ_i x)) (dφ_x (σ_j x))`.

## The proof

Write `V i x := dφ_x (σ_i x) ∈ T_{φ x}M`, a section of the tangent bundle *over* `φ`.

* Each `V i` is smooth at `x₀`: the section `σ_i` is the section of the tangent bundle with
  constant coordinates `bB i` in the chart at `x₀`, which is smooth at `x₀`
  (`Submission.Geodesic.contMDiffAt_frameSection`), and the tangent map of the smooth map `φ` is
  smooth (`ContMDiff.contMDiff_tangentMap`); composition (`ContMDiffAt.comp`) gives the smoothness
  of `x ↦ ⟨φ x, V i x⟩` in the tangent bundle.
* The pairing `x ↦ g.inner (φ x) (V i x) (V j x)` is then smooth by
  `ContMDiffAt.inner_bundle` (with base map `φ`), applied with the Riemannian-bundle structure
  induced by `g`.  The scalar product of that structure at `φ x` is `g.inner (φ x)` by definition.
* The matrix is a `Fin _ → Fin _ → ℝ`-valued function, so the two `contMDiffAt_pi_space` reductions
  assemble the components.
-/

import Mathlib
import Submission.Work.Diff.STE.C2.Defs0
import Submission.Work.Diff.EXT.glueDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.STE.C2

theorem pullMetBilin_frameMat_contMDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (φ : Diffeomorph I I M M (⊤ : ℕ∞)) (g : Submission.Diff.SMet I M) (x₀ : M) :
    ContMDiffAt I (modelWithCornersSelf ℝ (Work.Diff.EXT.MatE (E := E))) (⊤ : ℕ∞)
      (fun x : M ↦ Work.Diff.EXT.frameMat (I := I) x₀ x (Work.Diff.STE.C2.pullMetBilin φ g x)) x₀ := by
  classical
  -- the Riemannian-bundle structure induced by `g`, whose scalar product is `g.inner`
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  -- the pushed-forward frame vectors, as a section of the tangent bundle over `φ`
  let V : Fin (Module.finrank ℝ E) → (x : M) → TangentSpace I (φ x) :=
    fun i x ↦ mfderiv I I (φ : M → M) x
      (Submission.Geodesic.frameVector (I := I) x₀ x (Work.Diff.EXT.bB (E := E) i))
  have hφ : CMDiff ∞ (φ : M → M) := φ.contMDiff_toFun
  have htan : ContMDiff I.tangent I.tangent ∞ (tangentMap I I (φ : M → M)) :=
    ContMDiff.contMDiff_tangentMap hφ (by simp)
  -- smoothness of `x ↦ ⟨φ x, V i x⟩`
  have hV (i : Fin (Module.finrank ℝ E)) :
      CMDiffAt ∞ (fun x : M ↦ (⟨φ x, V i x⟩ : TangentBundle I M)) x₀ := by
    have hσ : CMDiffAt ∞ (T% (fun x : M ↦ Submission.Geodesic.frameVector (I := I) x₀ x
          (Work.Diff.EXT.bB (E := E) i))) x₀ :=
      Submission.Geodesic.contMDiffAt_frameSection x₀ _ (mem_chart_source H x₀)
    have h := (htan.contMDiffAt).comp (x₀) (hσ)
    simpa [V, Function.comp_def, tangentMap] using h
  -- smoothness of the matrix entries
  have hinner (i j : Fin (Module.finrank ℝ E)) :
      CMDiffAt ∞ (fun x : M ↦ g.inner (φ x) (V i x) (V j x)) x₀ := by
    have h := ContMDiffAt.inner_bundle (h := ?_) (b := fun x : M ↦ φ x) (v := V i) (w := V j)
      (hV i) (hV j)
    · exact h
    · infer_instance
  -- assemble the two `Fin _ → ·` components
  refine (contMDiffAt_pi_space.mpr fun i ↦ contMDiffAt_pi_space.mpr fun j ↦
    hinner i j).congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
  funext x i j
  simp only [Work.Diff.EXT.frameMat, pullMetBilin_apply, V]

end Work.Diff.STE.C2
