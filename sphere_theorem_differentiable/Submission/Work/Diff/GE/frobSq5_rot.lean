import Mathlib
import Submission.Work.Diff.GE.frobSq5_defs
import Submission.Work.Diff.GE.frobSq5_main
import Submission.Work.Diff.GE.N5_eq_QQ2
import Submission.Work.Diff.GE.frobSq5_eq_sum
import Submission.Work.Diff.GE.rot5_eq_rotA

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Finset

theorem frobSq5_rot {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (S : Fin n → Curv4 n) :
    N5 (A * Matrix.transpose A) (rot5 A S) = frobSq5 S := by
  rw [N5_eq_QQ2 (A * Matrix.transpose A) (rot5 A S)]
  rw [rot5_eq_rotA A S]
  rw [main A hA 5 (fun x : Fin 5 → Fin n => S (x 0) (x 1) (x 2) (x 3) (x 4))
        (fun x : Fin 5 → Fin n => S (x 0) (x 1) (x 2) (x 3) (x 4))]
  rw [frobSq5_eq_sum S]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  ring

end Work.Diff.GE
