import Mathlib
import Submission.Work.Diff.GE.frobSq5_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Finset
open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE
noncomputable section
variable {n : ℕ}

/-- The slot-by-slot contraction: `QQ2` of the `k`-fold rotated tensor against `Γ = A * Aᵀ` is the
Euclidean inner product.  Induction on `k`; the step is `QQ2_rotA_succ` followed by the one-slot
contraction `contract_slot`. -/
theorem main {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) :
    ∀ k (X Y : (Fin k → Fin n) → ℝ),
      QQ2 k (A * Matrix.transpose A) (rotA k A X) (rotA k A Y) = ∑ x, X x * Y x := by
  intro k
  induction k with
  | zero =>
    intro X Y
    have e : Fin 0 → Fin n := fun i => i.elim0
    have hr : rotA 0 A X = X := by
      funext x
      simp only [rotA, Fin.prod_univ_zero, one_mul]
      exact Fintype.sum_subsingleton X x
    have hr' : rotA 0 A Y = Y := by
      funext x
      simp only [rotA, Fin.prod_univ_zero, one_mul]
      exact Fintype.sum_subsingleton Y x
    rw [hr, hr']
    rw [show QQ2 0 (A * Matrix.transpose A) X Y
          = ∑ x : Fin 0 → Fin n, ∑ y : Fin 0 → Fin n, X x * Y y from by
        rw [QQ2]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.sum_congr rfl (fun y _ => ?_)]
        rw [show (∏ d : Fin 0, (A * Matrix.transpose A)⁻¹ (x d) (y d)) = 1 from by simp]
        rw [one_mul]]
    rw [show (∑ x : Fin 0 → Fin n, ∑ y : Fin 0 → Fin n, X x * Y y) = X e * Y e from by
          rw [Fintype.sum_subsingleton (fun x => ∑ y, X x * Y y) e]
          rw [Fintype.sum_subsingleton (fun y => X e * Y y) e]]
    rw [Fintype.sum_subsingleton (fun x => X x * Y x) e]
  | succ k ih =>
    intro X Y
    rw [QQ2_rotA_succ A (A * Matrix.transpose A) X Y]
    trans ∑ c : Fin n, ∑ e : Fin n, (if c = e then (1 : ℝ) else 0) *
        QQ2 k (A * Matrix.transpose A) (rotA k A (fun u => X (consFn c u)))
          (rotA k A (fun u => Y (consFn e u)))
    · refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun e _ => ?_))
      rw [contract_slot A hA c e]
    trans ∑ c : Fin n, QQ2 k (A * Matrix.transpose A) (rotA k A (fun u => X (consFn c u)))
        (rotA k A (fun u => Y (consFn c u)))
    · exact sum_ite_diag (fun c e => QQ2 k (A * Matrix.transpose A)
        (rotA k A (fun u => X (consFn c u))) (rotA k A (fun u => Y (consFn e u))))
    trans ∑ c : Fin n, ∑ x' : Fin k → Fin n, X (consFn c x') * Y (consFn c x')
    · refine Finset.sum_congr rfl (fun c _ => ?_)
      exact ih (fun u => X (consFn c u)) (fun u => Y (consFn c u))
    · trans ∑ p : Fin n × (Fin k → Fin n), X (consFn p.1 p.2) * Y (consFn p.1 p.2)
      · exact (Fintype.sum_prod_type' (f := fun c x' => X (consFn c x') * Y (consFn c x'))).symm
      · exact (sum_pi_succ k (fun x => X x * Y x)).symm

end
end Work.Diff.GE
