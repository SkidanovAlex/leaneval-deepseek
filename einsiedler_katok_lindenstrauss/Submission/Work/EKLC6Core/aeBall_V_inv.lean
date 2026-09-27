import Mathlib
import Submission.Work.EKLContract.Interfaces

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## Entrywise inverse bound for a matrix near the identity

For `A : Matrix (Fin 3) (Fin 3) ℝ` within (entrywise sup-)distance `s ≤ 1/8` of the identity,
the adjugate `adjugate A` — which is the underlying matrix of `A⁻¹` in `SL₃(ℝ)`, since `det A = 1`
— is within `5 s` of the identity.  The two elementary numerical estimates below drive the nine
entrywise bounds obtained from Mathlib's explicit `3 × 3` adjugate formula
`Matrix.adjugate_fin_three`. -/

/-- A product of two reals of modulus `< s` has modulus `< s ^ 2`. -/
private lemma abs_mul_lt_sq {s x y : ℝ} (hs : 0 < s) (hx : |x| < s) (hy : |y| < s) :
    |x * y| < s ^ 2 := by
  rw [abs_mul]
  nlinarith [abs_nonneg x, abs_nonneg y]

/-- Diagonal entry of a `2 × 2` determinant: if `p`, `q` are within `s` of `1` and `r`, `t` within
`s` of `0`, then `p * q - r * t` is within `5 s` of `1` (`s ≤ 1/8`). -/
private lemma diag_bound {s p q r t : ℝ} (hs : 0 < s) (hs1 : s ≤ 1 / 8)
    (hp : |p - 1| < s) (hq : |q - 1| < s) (hr : |r| < s) (ht : |t| < s) :
    |p * q - r * t - 1| < 5 * s := by
  have hpq : |(p - 1) * (q - 1)| < s ^ 2 := abs_mul_lt_sq hs hp hq
  have hrt : |r * t| < s ^ 2 := abs_mul_lt_sq hs hr ht
  have hE : p * q - r * t - 1 = ((p - 1) + (q - 1) + (p - 1) * (q - 1)) - r * t := by ring
  rw [hE]
  have htri : |((p - 1) + (q - 1) + (p - 1) * (q - 1)) - r * t| ≤
      |p - 1| + |q - 1| + |(p - 1) * (q - 1)| + |r * t| := by
    have h1 : |((p - 1) + (q - 1) + (p - 1) * (q - 1)) - r * t| ≤
        |(p - 1) + (q - 1) + (p - 1) * (q - 1)| + |r * t| := by
      have := abs_add_le ((p - 1) + (q - 1) + (p - 1) * (q - 1)) (-(r * t))
      simpa [sub_eq_add_neg] using this
    have h2 : |(p - 1) + (q - 1) + (p - 1) * (q - 1)| ≤
        |p - 1| + |q - 1| + |(p - 1) * (q - 1)| := by
      have h2a := abs_add_le ((p - 1) + (q - 1)) ((p - 1) * (q - 1))
      have h2b := abs_add_le (p - 1) (q - 1)
      linarith [abs_nonneg ((p - 1) + (q - 1)), abs_nonneg ((p - 1) * (q - 1))]
    linarith [abs_nonneg (r * t)]
  have hsq : 2 * s + 2 * s ^ 2 < 5 * s := by nlinarith
  linarith [abs_nonneg (p - 1), abs_nonneg (q - 1), abs_nonneg ((p - 1) * (q - 1)),
    abs_nonneg (r * t)]

/-- Off-diagonal entry of a `2 × 2` determinant: if `p`, `r`, `t` are within `s` of `0` and `q`
within `s` of `1`, then `q * p + r * t` is within `5 s` of `0` (`s ≤ 1/8`). -/
private lemma off_bound {s p q r t : ℝ} (hs : 0 < s) (hs1 : s ≤ 1 / 8)
    (hp : |p| < s) (hq : |q - 1| < s) (hr : |r| < s) (ht : |t| < s) :
    |q * p + r * t| < 5 * s := by
  have hqp : |(q - 1) * p| < s ^ 2 := abs_mul_lt_sq hs hq hp
  have hrt : |r * t| < s ^ 2 := abs_mul_lt_sq hs hr ht
  have hE : q * p + r * t = (p + (q - 1) * p) + r * t := by ring
  rw [hE]
  have htri : |(p + (q - 1) * p) + r * t| ≤ |p| + |(q - 1) * p| + |r * t| := by
    have h1 := abs_add_le p ((q - 1) * p)
    have h2 := abs_add_le (p + (q - 1) * p) (r * t)
    linarith [abs_nonneg p, abs_nonneg ((q - 1) * p), abs_nonneg (r * t)]
  have hsq : s + 2 * s ^ 2 < 5 * s := by nlinarith
  linarith [abs_nonneg p, abs_nonneg ((q - 1) * p), abs_nonneg (r * t)]

/-- The inverse of a matrix within `s` of the identity (entrywise sup-distance, `s ≤ 1/8`) is
within `5 s` of the identity. -/
theorem aeBall_V_inv {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1 / 8) {v : Work.EKLContract.SL3}
    (hv : v ∈ Work.EKLContract.V s) : v⁻¹ ∈ Work.EKLContract.V (5 * s) := by
  have hv' : ∀ i j, |toMat v i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < s := fun i j => hv i j
  have hd : ∀ k : Fin 3, |toMat v k k - 1| < s := by
    intro k; have := hv' k k; simpa [Matrix.one_apply_eq] using this
  have ho : ∀ k l : Fin 3, k ≠ l → |toMat v k l| < s := by
    intro k l hkl; have := hv' k l; simpa [Matrix.one_apply_ne hkl] using this
  have key : ∀ i j, |toMat v⁻¹ i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < 5 * s := by
    intro i j
    change |Matrix.adjugate (toMat v) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < 5 * s
    fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_three]
    case «0».«0» => exact diag_bound hs hs1 (hd 1) (hd 2) (ho 1 2 (by decide)) (ho 2 1 (by decide))
    case «0».«1» =>
      rw [show -(toMat v 0 1 * toMat v 2 2) + toMat v 0 2 * toMat v 2 1
            = toMat v 2 2 * (-(toMat v 0 1)) + toMat v 0 2 * toMat v 2 1 by ring]
      exact off_bound hs hs1 (by simpa using ho 0 1 (by decide)) (hd 2) (ho 0 2 (by decide))
        (ho 2 1 (by decide))
    case «0».«2» =>
      rw [show toMat v 0 1 * toMat v 1 2 - toMat v 0 2 * toMat v 1 1
            = toMat v 1 1 * (-(toMat v 0 2)) + toMat v 0 1 * toMat v 1 2 by ring]
      exact off_bound hs hs1 (by simpa using ho 0 2 (by decide)) (hd 1) (ho 0 1 (by decide))
        (ho 1 2 (by decide))
    case «1».«0» =>
      rw [show -(toMat v 1 0 * toMat v 2 2) + toMat v 1 2 * toMat v 2 0
            = toMat v 2 2 * (-(toMat v 1 0)) + toMat v 1 2 * toMat v 2 0 by ring]
      exact off_bound hs hs1 (by simpa using ho 1 0 (by decide)) (hd 2) (ho 1 2 (by decide))
        (ho 2 0 (by decide))
    case «1».«1» => exact diag_bound hs hs1 (hd 0) (hd 2) (ho 0 2 (by decide)) (ho 2 0 (by decide))
    case «1».«2» =>
      rw [show -(toMat v 0 0 * toMat v 1 2) + toMat v 0 2 * toMat v 1 0
            = toMat v 0 0 * (-(toMat v 1 2)) + toMat v 0 2 * toMat v 1 0 by ring]
      exact off_bound hs hs1 (by simpa using ho 1 2 (by decide)) (hd 0) (ho 0 2 (by decide))
        (ho 1 0 (by decide))
    case «2».«0» =>
      rw [show toMat v 1 0 * toMat v 2 1 - toMat v 1 1 * toMat v 2 0
            = toMat v 1 1 * (-(toMat v 2 0)) + toMat v 1 0 * toMat v 2 1 by ring]
      exact off_bound hs hs1 (by simpa using ho 2 0 (by decide)) (hd 1) (ho 1 0 (by decide))
        (ho 2 1 (by decide))
    case «2».«1» =>
      rw [show -(toMat v 0 0 * toMat v 2 1) + toMat v 0 1 * toMat v 2 0
            = toMat v 0 0 * (-(toMat v 2 1)) + toMat v 0 1 * toMat v 2 0 by ring]
      exact off_bound hs hs1 (by simpa using ho 2 1 (by decide)) (hd 0) (ho 0 1 (by decide))
        (ho 2 0 (by decide))
    case «2».«2» => exact diag_bound hs hs1 (hd 0) (hd 1) (ho 0 1 (by decide)) (ho 1 0 (by decide))
  exact key

end Work.EKLC6Core
