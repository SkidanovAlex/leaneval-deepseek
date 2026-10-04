import Mathlib
import Submission.Work.OddBound.AssemblyKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Side length bound from the polygon energy bound

If the polygon energy `gonEnergy p w = (N/2) · Σ_{i<N} d(v_i, v_{i+1})²` of the based `N`-gon
with interior vertices `w` is at most `C`, then every side is at most `√(2C/N)`.

Indeed the energy is `(N/2)` times a sum of squares of *nonnegative* side lengths, so a single
side `s` satisfies `(N/2) · s² ≤ C`, i.e. `s² ≤ 2C/N`, i.e. `s ≤ √(2C/N)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.OddBound.assembly

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length
open Submission.InjRadius Submission.IndexIntrinsic Submission.CurvatureVec

theorem gonSideLen_le_of_gonEnergy_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {N : ℕ} (hN : 0 < N) (p : M) {w : Fin (N - 1) → M} {C : ℝ} (hC : 0 ≤ C)
    (hE : Work.OddBound.gonEnergy (I := I) p w ≤ C) (i : Fin N) :
    Work.OddBound.gonSideLen (I := I) p w (i : ℕ) ≤ Real.sqrt (2 * C / (N : ℝ)) := by
  -- The `i`-th side is a distance, hence nonnegative.
  have hs : 0 ≤ Work.OddBound.gonSideLen (I := I) p w (i : ℕ) :=
    Submission.Distance.riemannianDist_nonneg _ _
  -- A single nonnegative term of a sum of nonnegative terms is at most the whole sum.
  have hsum : (Work.OddBound.gonSideLen (I := I) p w (i : ℕ)) ^ 2
      ≤ ∑ j : Fin N, (Work.OddBound.gonSideLen (I := I) p w (j : ℕ)) ^ 2 :=
    Finset.single_le_sum
      (f := fun j : Fin N => (Work.OddBound.gonSideLen (I := I) p w (j : ℕ)) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  -- Scaling by `N/2 ≥ 0` and the energy bound: `(N/2) · s² ≤ C`.
  have hE' : ((N : ℝ) / 2) * (Work.OddBound.gonSideLen (I := I) p w (i : ℕ)) ^ 2 ≤ C := by
    calc ((N : ℝ) / 2) * (Work.OddBound.gonSideLen (I := I) p w (i : ℕ)) ^ 2
        ≤ ((N : ℝ) / 2) * ∑ j : Fin N, (Work.OddBound.gonSideLen (I := I) p w (j : ℕ)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = Work.OddBound.gonEnergy (I := I) p w := rfl
      _ ≤ C := hE
  -- Hence `s² ≤ 2C / N`.
  have hs2 : (Work.OddBound.gonSideLen (I := I) p w (i : ℕ)) ^ 2 ≤ 2 * C / (N : ℝ) := by
    field_simp
    nlinarith [hE']
  -- Take square roots.
  have hrt : Real.sqrt ((Work.OddBound.gonSideLen (I := I) p w (i : ℕ)) ^ 2)
      ≤ Real.sqrt (2 * C / (N : ℝ)) := Real.sqrt_le_sqrt hs2
  rwa [Real.sqrt_sq hs] at hrt

end Work.OddBound.assembly
