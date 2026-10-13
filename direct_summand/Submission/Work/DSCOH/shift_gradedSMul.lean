import Mathlib
import Submission.Work.DSCOH.Shift

namespace Work.DSCOH

/-- Multiplication is graded for the shifted grading: if `a` is homogeneous of degree `i` in
`S = A[X₀,…,X_{n-1}]` and `b ∈ S(-d)_j`, then `a * b ∈ S(-d)_{i+j}`.

Indeed, either `j < d`, in which case `S(-d)_j = 0` and `b = 0`, or `d ≤ j`, in which case
`b` is homogeneous of degree `j - d` and `a * b` is homogeneous of degree
`i + (j - d) = (i + j) - d`, which is exactly the `(i+j)`-th piece of `S(-d)`. -/
theorem shift_gradedSMul {A : Type*} [CommRing A] {n : ℕ} (d : ℕ) :
    SetLike.GradedSMul (homSub A n) (shift (A := A) (n := n) d) := by
  refine ⟨fun i j ai bj hai hbj => ?_⟩
  rw [vadd_eq_add]
  by_cases h : d ≤ j
  · rw [shift_of_le h] at hbj
    rw [shift_of_le (le_trans h (Nat.le_add_left j i))]
    rw [homSub, MvPolynomial.mem_homogeneousSubmodule] at hai hbj ⊢
    have h1 : (ai * bj).IsHomogeneous (i + (j - d)) := hai.mul hbj
    have h2 : i + (j - d) = i + j - d := by omega
    rw [smul_eq_mul, ← h2]
    exact h1
  · rw [shift_of_not_le h] at hbj
    rw [Submodule.mem_bot] at hbj
    rw [hbj, smul_zero]
    exact Submodule.zero_mem _

end Work.DSCOH
