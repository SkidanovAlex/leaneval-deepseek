import Mathlib
import Submission.Work.OddBound.PolygonChart
import Submission.Work.OddBound.Minimax

/-!
# Definitions for the polygon minimax assembly

The minimax on the based polygon space `Fin (N-1) → M` is run over the **competitor set** of real
numbers below a continuous path of polygons joining the inscribed polygon `a` (the `N`-gon whose
vertices are the points `γ (L i / N)` of a closed geodesic loop `γ` of period `L`) to the constant
polygon `b = p`.  Its infimum is the **minimax value** `Λ`.

* `Work.OddBound.GonMinimaxSet p a b` is the competitor set;
* `Work.OddBound.GonMinimaxValue p a b` is its infimum `Λ`;
* `Work.OddBound.inscribedGon p L N γ` is the inscribed polygon `i ↦ γ (L (i+1) / N)`;
* `Work.OddBound.constantGon p` is the constant polygon `i ↦ p`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length
open Submission.InjRadius Submission.IndexIntrinsic Submission.CurvatureVec

namespace Work.OddBound

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The competitor set of the polygon minimax**: those `m` for which some continuous path of
based polygons joins `a` to `b` staying below `m` in the polygon energy. -/
def GonMinimaxSet (p : M) {N : ℕ} (a b : Fin (N - 1) → M) : Set ℝ :=
  {m : ℝ | ∃ σ : ℝ → Fin (N - 1) → M,
    ContinuousOn σ (Set.Icc (0 : ℝ) 1) ∧ σ 0 = a ∧ σ 1 = b ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1, gonEnergy (I := I) p (σ t) ≤ m}

/-- **The polygon minimax value** `Λ_N`, the infimum of the competitor set. -/
def GonMinimaxValue (p : M) {N : ℕ} (a b : Fin (N - 1) → M) : ℝ :=
  sInf (GonMinimaxSet (I := I) p a b)

/-- **The polygon inscribed in the closed curve `γ` of period `L`**: its `i`-th vertex is
`γ (L (i+1) / N)`.  The side `N-1 → N` closes back to `p = γ 0` when `γ` is `L`-periodic. -/
def inscribedGon {N : ℕ} (L : ℝ) (γ : ℝ → M) : Fin (N - 1) → M :=
  fun i => γ (L * ((i : ℕ) + 1) / N)

/-- The constant polygon at the base point (the endpoint of the competitor paths). -/
def constantGon {N : ℕ} (p : M) : Fin (N - 1) → M := fun _ => p

@[simp] theorem inscribedGon_apply {N : ℕ} (L : ℝ) (γ : ℝ → M) (i : Fin (N - 1)) :
    inscribedGon L γ i = γ (L * ((i : ℕ) + 1) / N) := rfl

@[simp] theorem constantGon_apply {N : ℕ} (p : M) (i : Fin (N - 1)) :
    constantGon p i = p := rfl

end

end Work.OddBound
