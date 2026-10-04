import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.CompSmooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: the elementary order and symmetry properties of the composite pairing

`BPair` is meant to be a positive definite symmetric pairing on the space `Bil` of sections.  This
file records the two facts that follow immediately from the definitions and need no chart transfer:
symmetry, and nonnegativity of the diagonal.
-/

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter MeasureTheory

namespace Work.Diff.STE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}

namespace B3Data

variable (D : B3Data (I := I) (M := M) ι₀ g₀)

/-- The volume density is nonnegative. -/
lemma dens_nonneg (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ) : 0 ≤ D.dens i z :=
  Real.sqrt_nonneg _

/-- The component pairing is symmetric. -/
lemma CPair_comm (i : ι₀)
    (u v : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ) :
    CPair i u v = CPair i v u := by
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  ring

/-- The component pairing is nonnegative on the diagonal. -/
lemma CPair_self_nonneg (i : ι₀)
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ) :
    0 ≤ CPair i u u := by
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
  exact integral_nonneg fun z => mul_self_nonneg _

/-- The composite pairing is symmetric. -/
lemma BPair_comm (h k : Bil (I := I) (M := M)) : D.BPair h k = D.BPair k h := by
  refine Finset.sum_congr rfl fun i _ => ?_
  exact CPair_comm i (D.R i h) (D.R i k)

/-- The composite pairing is nonnegative on the diagonal. -/
lemma BPair_self_nonneg (h : Bil (I := I) (M := M)) : 0 ≤ D.BPair h h :=
  Finset.sum_nonneg fun i _ => CPair_self_nonneg i (D.R i h)

/-- The composite norm is nonnegative. -/
lemma BNorm_nonneg (k : ℕ) (h : Bil (I := I) (M := M)) : 0 ≤ D.BNorm k h :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ =>
    Finset.sum_nonneg fun b _ => tsum_nonneg fun m =>
      mul_nonneg (pow_nonneg (le_of_lt (wt_pos m)) k) (sq_nonneg _)

end B3Data

end Work.Diff.STE
