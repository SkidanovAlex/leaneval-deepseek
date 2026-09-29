import Submission.Work.Fx.FxLin

/-!
# Elementary rounding / disc estimates for fixed-point complex numbers
-/

set_option autoImplicit false

namespace Work.Fx

open HvdH

/-- Truncating division by `2` has error at most `1/2`. -/
theorem tdiv_two_err (n : ℤ) : |((n.tdiv 2 : ℤ) : ℝ) - (n : ℝ) / 2| ≤ 1 / 2 := by
  have h : n.tmod 2 + n.tdiv 2 * 2 = n := Int.tmod_add_tdiv_mul n 2
  have hkey : ((n.tdiv 2 : ℤ) : ℝ) - (n : ℝ) / 2 = -((n.tmod 2 : ℤ) : ℝ) / 2 := by
    have : (n : ℝ) = (n.tmod 2 : ℝ) + (n.tdiv 2 : ℝ) * 2 := by exact_mod_cast h.symm
    linarith
  rw [hkey, abs_div, abs_neg]
  rcases Int.tmod_two_eq n with h2 | h2 | h2 <;> rw [h2] <;> norm_num

/-- `2 * |n.tdiv 2| ≤ |n|`. -/
theorem two_mul_tdiv_two_natAbs (n : ℤ) : 2 * (n.tdiv 2).natAbs ≤ n.natAbs := by
  have h : (n.tdiv 2).natAbs = n.natAbs / 2 := by
    rw [Int.natAbs_tdiv]
    rfl
  rw [h]
  omega

/-- `4 * (n.tdiv 2)^2 ≤ n^2`. -/
theorem four_mul_tdiv_two_sq_le (n : ℤ) : 4 * (n.tdiv 2) ^ 2 ≤ n ^ 2 := by
  have h2 := two_mul_tdiv_two_natAbs n
  have h3 : (2 * (n.tdiv 2).natAbs) ^ 2 ≤ n.natAbs ^ 2 := Nat.pow_le_pow_left h2 2
  have h4 : ((n.tdiv 2) ^ 2 : ℤ) = (((n.tdiv 2).natAbs : ℤ)) ^ 2 := by
    rw [Int.natAbs_sq]
  have h5 : (n ^ 2 : ℤ) = ((n.natAbs : ℤ)) ^ 2 := by rw [Int.natAbs_sq]
  rw [h4, h5]
  have h6 : (2 * (((n.tdiv 2).natAbs : ℤ))) ^ 2 ≤ ((n.natAbs : ℤ)) ^ 2 := by
    exact_mod_cast h3
  nlinarith [h6]

/-- Lagrange's identity: `(ac+bd)^2 ≤ (a^2+b^2)(c^2+d^2)`. -/
theorem two_sq_mul_le (a b c d : ℤ) : (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a * d - b * c)]

/-- From `inDisc`: each coordinate square is at most `4^p`. -/
theorem inDisc_sq_le (p : ℕ) (z : ℤ × ℤ) (h : inDisc p z) : z.1 ^ 2 ≤ 4 ^ p ∧ z.2 ^ 2 ≤ 4 ^ p := by
  simp only [inDisc] at h
  have h1 : (0 : ℤ) ≤ z.1 ^ 2 := sq_nonneg z.1
  have h2 : (0 : ℤ) ≤ z.2 ^ 2 := sq_nonneg z.2
  constructor <;> linarith

/-- Cauchy–Schwarz bound for two disc points. -/
theorem dot_le_four_pow {p : ℕ} {u v : ℤ × ℤ} (hu : inDisc p u) (hv : inDisc p v) :
    u.1 * v.1 + u.2 * v.2 ≤ 4 ^ p := by
  simp only [inDisc] at hu hv
  have hp4 : (0 : ℤ) ≤ 4 ^ p := by positivity
  have hprod : (u.1 ^ 2 + u.2 ^ 2) * (v.1 ^ 2 + v.2 ^ 2) ≤ 4 ^ p * 4 ^ p :=
    mul_le_mul hu hv (by positivity) hp4
  have hlag := two_sq_mul_le u.1 u.2 v.1 v.2
  have hsq : (u.1 * v.1 + u.2 * v.2) ^ 2 ≤ (4 ^ p) ^ 2 := by nlinarith [hlag, hprod]
  exact le_of_sq_le_sq hsq hp4

/-- The rounded half-sum stays in the disc. -/
theorem inDisc_add_half {p : ℕ} {u v : ℤ × ℤ} (hu : inDisc p u) (hv : inDisc p v) :
    inDisc p ((u.1 + v.1).tdiv 2, (u.2 + v.2).tdiv 2) := by
  simp only [inDisc] at hu hv ⊢
  have hx := four_mul_tdiv_two_sq_le (u.1 + v.1)
  have hy := four_mul_tdiv_two_sq_le (u.2 + v.2)
  have hcs := dot_le_four_pow hu hv
  have hsum : (u.1 + v.1) ^ 2 + (u.2 + v.2) ^ 2 ≤ 4 * 4 ^ p := by
    have h : (u.1 + v.1) ^ 2 + (u.2 + v.2) ^ 2 =
        (u.1 ^ 2 + u.2 ^ 2) + (v.1 ^ 2 + v.2 ^ 2) + 2 * (u.1 * v.1 + u.2 * v.2) := by ring
    nlinarith [hu, hv, hcs, h]
  nlinarith [hx, hy, hsum]

/-- The rounded half-difference stays in the disc. -/
theorem inDisc_sub_half {p : ℕ} {u v : ℤ × ℤ} (hu : inDisc p u) (hv : inDisc p v) :
    inDisc p ((u.1 - v.1).tdiv 2, (u.2 - v.2).tdiv 2) := by
  have hv' : inDisc p (-v.1, -v.2) := by
    simp only [inDisc] at hv ⊢
    have h : (-v.1) ^ 2 + (-v.2) ^ 2 = v.1 ^ 2 + v.2 ^ 2 := by ring
    rw [h]; exact hv
  have h1 : (u.1 + -v.1).tdiv 2 = (u.1 - v.1).tdiv 2 := by congr 1
  have h2 : (u.2 + -v.2).tdiv 2 = (u.2 - v.2).tdiv 2 := by congr 1
  have := inDisc_add_half hu hv'
  rwa [h1, h2] at this

end Work.Fx
