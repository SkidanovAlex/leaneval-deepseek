import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.RankAPI.rk_mul_add_le
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.Epic

namespace Work.RankAPI

open Work.ORHughesFree

/-- Multiplication of `1 × 1` matrices is multiplication in the ring. -/
theorem oneByOne_mul_eq {R : Type*} [Ring R] (a b : R) :
    oneByOne a * oneByOne b = oneByOne (a * b) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [oneByOne, Matrix.mul_apply]

/-- The `1 × 1` matrix with entry `1` is the identity matrix. -/
theorem oneByOne_one_eq {R : Type*} [Ring R] : oneByOne (1 : R) = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [oneByOne]

/-- Weak subadditivity of a Sylvester rank function on `1 × 1` matrices:
`rk a + rk b ≤ rk (a * b) + 1`, the `n = m = k = 1` case of the subadditivity inequality. -/
theorem rk_oneByOne_mul_ge {R : Type*} [Ring R] (rk : SylvesterRank R) (a b : R) :
    rk.rk 1 1 (oneByOne a) + rk.rk 1 1 (oneByOne b)
      ≤ rk.rk 1 1 (oneByOne (a * b)) + 1 := by
  have h := Work.ORHughesFree.RankAPI.rk_mul_add_le rk (oneByOne a) (oneByOne b)
  rw [oneByOne_mul_eq] at h
  norm_num at h
  exact h

/-- In a von Neumann regular ring, an element of a faithful Sylvester rank function with
`rk x = 1` is a unit: writing `x * y * x = x` for a weak inverse `y`, the weak subadditivity
inequality applied to `(1 - x * y) * x = 0` forces `1 - x * y` to have rank `0`, hence to
vanish; faithfulness of `rk` then gives `x * y = 1`, so `rk y = 1`, and the same argument with
`(1 - y * x) * y = 0` gives `y * x = 1`. -/
theorem isUnit_of_rk_oneByOne_eq_one {R : Type} [Ring R] [Work.ORHughesFree.VonNeumannRegularRing R]
    (rk : Work.ORHughesFree.SylvesterRank R) (hrk : rk.IsFaithful) {x : R}
    (h : rk.rk 1 1 (Work.ORHughesFree.oneByOne x) = 1) : IsUnit x := by
  obtain ⟨y, hy⟩ := VonNeumannRegularRing.exists_mul_inverse x
  have hxy : x * y = 1 := by
    have h1 := rk_oneByOne_mul_ge rk (1 - x * y) x
    have h2 : (1 - x * y) * x = 0 := by rw [sub_mul, one_mul, hy, sub_self]
    rw [h2, show oneByOne (0 : R) = (0 : Matrix (Fin 1) (Fin 1) R) from rfl,
      rk.rk_zero, h] at h1
    have h0 : rk.rk 1 1 (oneByOne (1 - x * y)) = 0 := by
      have := rk.nonneg (oneByOne (1 - x * y))
      linarith
    exact (sub_eq_zero.mp (hrk _ h0)).symm
  have hy1 : rk.rk 1 1 (oneByOne y) = 1 := by
    have hle : rk.rk 1 1 (oneByOne y) ≤ 1 := by
      have hh := Work.ORHughesFree.RankAPI.rk_le_left rk (oneByOne y)
      norm_num at hh
      exact hh
    have hge : 1 ≤ rk.rk 1 1 (oneByOne y) := by
      have h1 : rk.rk 1 1 (oneByOne (x * y)) ≤ rk.rk 1 1 (oneByOne y) := by
        have hh := rk.rk_mul_le_right (oneByOne x) (oneByOne y)
        rwa [oneByOne_mul_eq] at hh
      have h2 : rk.rk 1 1 (oneByOne (x * y)) = 1 := by
        rw [hxy, oneByOne_one_eq, rk.rk_one]
      linarith
    linarith
  have hyx : y * x = 1 := by
    have h1 := rk_oneByOne_mul_ge rk (1 - y * x) y
    have h2 : (1 - y * x) * y = 0 := by
      rw [sub_mul, one_mul, mul_assoc, hxy, mul_one, sub_self]
    rw [h2, show oneByOne (0 : R) = (0 : Matrix (Fin 1) (Fin 1) R) from rfl,
      rk.rk_zero, hy1] at h1
    have h0 : rk.rk 1 1 (oneByOne (1 - y * x)) = 0 := by
      have := rk.nonneg (oneByOne (1 - y * x))
      linarith
    exact (sub_eq_zero.mp (hrk _ h0)).symm
  exact ⟨⟨x, y, hxy, hyx⟩, rfl⟩

end Work.RankAPI
