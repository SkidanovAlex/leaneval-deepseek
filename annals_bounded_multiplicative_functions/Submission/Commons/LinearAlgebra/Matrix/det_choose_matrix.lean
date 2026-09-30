import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Block

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.LinearAlgebra.Matrix

open Finset

/-- Sum of the first `k` positive integers. -/
lemma sum_range_add_one (k : ℕ) : ∑ i ∈ Finset.range k, (i + 1) = k * (k + 1) / 2 := by
  have h1 : (∑ i ∈ Finset.range (k + 1), i) = ∑ i ∈ Finset.range k, (i + 1) := by
    rw [Finset.sum_range_succ']
    simp
  rw [← h1, Finset.sum_range_id, Nat.add_sub_cancel, Nat.mul_comm]

theorem det_choose_matrix (k : ℕ) (ρ t : ℝ) :
    (Matrix.of (fun (l j : Fin k) => ((l.val + 1).choose (j.val + 1) : ℝ) * ρ ^ (j.val + 1) * t ^ (l.val - j.val))).det = ρ ^ (k * (k + 1) / 2) := by
  have htri : Matrix.IsLowerTriangular
      (Matrix.of (fun (l j : Fin k) =>
        ((l.val + 1).choose (j.val + 1) : ℝ) * ρ ^ (j.val + 1) * t ^ (l.val - j.val))) := by
    intro i j hij
    have hlt : i < j := by simpa using hij
    have hc : (i.val + 1).choose (j.val + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [Matrix.of_apply, hc]
  rw [Matrix.det_of_isLowerTriangular _ htri]
  have hdiag : ∀ i : Fin k,
      (Matrix.of (fun (l j : Fin k) =>
        ((l.val + 1).choose (j.val + 1) : ℝ) * ρ ^ (j.val + 1) * t ^ (l.val - j.val))) i i
        = ρ ^ (i.val + 1) := by
    intro i
    simp [Matrix.of_apply, Nat.choose_self]
  rw [Finset.prod_congr rfl (fun i _ => hdiag i)]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun i => i + 1) k]
  exact sum_range_add_one k

end Commons.LinearAlgebra.Matrix