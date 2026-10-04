import Mathlib
import Submission.Work.Diff.T.lc_deps

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Koszul formula for the Levi-Civita connection `lcOf (G t)`

The requested statement is exactly Mathlib's `CovariantDerivative.leviCivitaConnection_apply_inner`
(the Koszul formula for the Levi-Civita connection of a Riemannian metric), transported from the
*instance* inner product `⟪·,·⟫` of `RiemannianBundle := ⟨(G t).toRiemannianMetric⟩` to the
*explicit* inner product `(G t).inner` used throughout this development.

Two observations make the transport definitional:

* `lcOf g` is *by definition* `CovariantDerivative.leviCivitaConnection I M` for the instance
  `⟨g.toRiemannianMetric⟩` (it is a `noncomputable def` whose body is that term, with the instance
  introduced by a `letI`), and
* under that instance, `inner ℝ u v` is *by definition* `g.inner x u v` (the fibre inner product
  space structure is built from `g`'s core `inner` field).

So after introducing the instance locally, the Mathlib lemma's statement is definitionally equal to
the goal, except for the purely algebraic rewriting `(...) / 2 = (1 / 2 : ℝ) * (...)`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.Diff.T

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem lcOf_apply_inner_koszul
    (G : ℝ → SMet I M) (t : ℝ) (X Y Z : Π x : M, TangentSpace I x)
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) (x : M) :
    (G t).inner x (lcOf (G t) Y x (X x)) (Z x) =
      (1 / 2 : ℝ) * (mvfderiv I (fun y : M ↦ (G t).inner y (Y y) (Z y)) x (X x)
        + mvfderiv I (fun y : M ↦ (G t).inner y (Z y) (X y)) x (Y x)
        - mvfderiv I (fun y : M ↦ (G t).inner y (X y) (Y y)) x (Z x)
        - (G t).inner x (Y x) (mlieBracket I X Z x)
        - (G t).inner x (Z x) (mlieBracket I Y X x)
        + (G t).inner x (X x) (mlieBracket I Z Y x)) := by
  -- Endow `M` with the metric `G t`, so that `lcOf (G t)` is defeq to `leviCivitaConnection I M`
  -- and `(G t).inner` is defeq to the instance inner product.
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) := inferInstance
  -- Smooth fields are differentiable at every point.
  have hX' : MDiffAt (T% X) x := hX.contMDiffAt.mdifferentiableAt (by simp)
  have hY' : MDiffAt (T% Y) x := hY.contMDiffAt.mdifferentiableAt (by simp)
  have hZ' : MDiffAt (T% Z) x := hZ.contMDiffAt.mdifferentiableAt (by simp)
  -- Mathlib's Koszul formula, in the instance inner product.
  have hmain := CovariantDerivative.leviCivitaConnection_apply_inner I
    (X := X) (Y := Y) (Z := Z) hX' hY' hZ'
  -- Rewrite the scalar `1 / 2` in front as the division by `2` occurring in `hmain`.
  have hhalf : ∀ s : ℝ, (1 / 2 : ℝ) * s = s / 2 := fun s => by ring
  rw [hhalf]
  exact hmain

end Work.Diff.T
