import Mathlib
import Submission.Work.Diff.GE.NablaRm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- **The frame-leftover sum vanishes.**  For any array `P : (Fin 5 → Fin n) → ℝ` and any antisymmetric
matrix `A` (`A i j = - A j i`), the sum `∑ α, P α * ∑ j, ∑ β, A (α j) β * P (Function.update α j β)`
vanishes.  This is the finite-sum cancellation that makes the second-order frame-correction term
disappear in the computation of the Laplacian of `|∇Rm|²` in an orthonormal frame that is geodesic at
the point.  Proof route: group by `γ := α j`; the inner contraction
`∑_{α : α j = γ} P α * P (Function.update α j β)` is symmetric in `(γ, β)` (swap the two factors and
re-index by `α ↦ Function.update α j β`, which is a bijection), while `A γ β` is antisymmetric, so the
double sum `∑_{γβ} A γ β * (symmetric)` is zero. -/
theorem kato_leftover_sum {n : ℕ} (P : (Fin 5 → Fin n) → ℝ) (A : Fin n → Fin n → ℝ)
    (hA : ∀ i j, A i j = - A j i) :
    ∑ α : Fin 5 → Fin n, P α * (∑ j : Fin 5, ∑ β : Fin n,
      A (α j) β * P (Function.update α j β)) = 0 := by
  classical
  -- The diagonal of an antisymmetric matrix vanishes.
  have hdiag : ∀ i : Fin n, A i i = 0 := by
    intro i
    have h := hA i i
    linarith
  -- For each fixed `j`, the double sum over `(α, β)` vanishes, by pairing each index with the
  -- involution `(α, β) ↦ (Function.update α j β, α j)`.
  have hsingle : ∀ j : Fin 5,
      (∑ α : Fin 5 → Fin n, ∑ β : Fin n,
        P α * A (α j) β * P (Function.update α j β)) = 0 := by
    intro j
    rw [← Fintype.sum_prod_type (fun x : (Fin 5 → Fin n) × Fin n =>
      P x.1 * A (x.1 j) x.2 * P (Function.update x.1 j x.2))]
    refine Finset.sum_ninvolution (s := Finset.univ)
      (f := fun x : (Fin 5 → Fin n) × Fin n =>
        P x.1 * A (x.1 j) x.2 * P (Function.update x.1 j x.2))
      (fun x => (Function.update x.1 j x.2, x.1 j)) ?_ ?_ ?_ ?_
    · -- the two terms of a pair cancel: `A β (α j) = - A (α j) β`
      intro a
      have h1 : Function.update a.1 j a.2 j = a.2 := by simp
      have h2 : Function.update (Function.update a.1 j a.2) j (a.1 j) = a.1 := by
        simp [Function.update_idem, Function.update_eq_self]
      simp only [h1, h2, hA a.2 (a.1 j)]
      ring
    · -- a fixed point would force `A (α j) (α j) = 0`
      intro a hg hga
      apply hg
      have h1 : a.1 j = a.2 := by
        simpa using congrArg (fun p : (Fin 5 → Fin n) × Fin n => p.2) hga
      rw [← h1]
      simp [hdiag]
    · intro a
      exact Finset.mem_univ _
    · -- the map is an involution
      intro a
      simp [Function.update_idem, Function.update_eq_self]
  -- Pull the scalars inside and swap the sums over `α` and `j`.
  have hconv :
      (∑ α : Fin 5 → Fin n, P α * (∑ j : Fin 5, ∑ β : Fin n,
          A (α j) β * P (Function.update α j β)))
        = ∑ j : Fin 5, ∑ α : Fin 5 → Fin n, ∑ β : Fin n,
            P α * A (α j) β * P (Function.update α j β) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun α _ => ?_)
    refine Finset.sum_congr rfl (fun β _ => ?_)
    ring
  rw [hconv]
  simp [hsingle]

end Work.Diff.GE
