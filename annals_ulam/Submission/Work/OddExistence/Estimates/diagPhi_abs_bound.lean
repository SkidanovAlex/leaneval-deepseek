import Mathlib
import Submission.Work.OddVolterra.Existence.data_close_of_small

/-!
# Absolute bounds for the diagonal kernels in explicit form

The diagonal kernels `K₁(s,s,t)`, `K₂(s,s,t)` of the odd Volterra system are, by
`K1_diag_eq`, `K2_diag_eq`, the *explicit* functions `diagPhi1 n`, `diagPhi2 n` of the jet
`p = (u, v) = (L h s t, ∂L h s t)`:

* `diagPhi1 n (u,v) = (-1)^(n+1) * (2n+1)!! * (uv)^n * √(uv) / √2`,
* `diagPhi2 n (u,v) = (-1)^n * (2n-1)!! * (uv)^(n-1) * √(uv) * v / √2`.

On the box `|u| ≤ B`, `|v| ≤ B` these are bounded by the values at the corner `(B,B)`:

* `|diagPhi1 n (u,v)| ≤ (2n+1)!! * B^(2n+1) / √2`,
* `|diagPhi2 n (u,v)| ≤ (2n-1)!! * B^(2n) / √2`.

Indeed `uv` enters only through `|P|^n √P ≤ B^(2n+1)` (resp. `|P|^(n-1) √P |v| ≤ B^(2n)`), because
`|uv| ≤ B²` and `√P ≤ √|P| ≤ √(B²) = B` for `B ≥ 0`.
-/

namespace Work.OddExistence.Estimates

open Work.OddVolterra.Existence

/-- Corner bounds of the first diagonal kernel: `|P|^n √P ≤ B^(2n+1)` whenever `|P| ≤ B²`.
(For `P < 0` this is very far from sharp: `√P = 0`.) -/
lemma pow_abs_mul_sqrt_le {P B : ℝ} (n : ℕ) (hB : 0 ≤ B) (hP : |P| ≤ B ^ 2) :
    |P| ^ n * Real.sqrt P ≤ B ^ (2 * n + 1) := by
  have h2 : |P| ^ n ≤ B ^ (2 * n) := by
    have h := pow_le_pow_left₀ (abs_nonneg P) hP n
    rwa [← pow_mul] at h
  have h3 : Real.sqrt P ≤ B := by
    have hle : Real.sqrt P ≤ Real.sqrt |P| := Real.sqrt_le_sqrt (le_abs_self P)
    have h4 : Real.sqrt |P| ≤ Real.sqrt (B ^ 2) := Real.sqrt_le_sqrt hP
    have h5 : Real.sqrt (B ^ 2) = B := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hB]
    linarith
  calc |P| ^ n * Real.sqrt P ≤ B ^ (2 * n) * B :=
        mul_le_mul h2 h3 (Real.sqrt_nonneg P) (pow_nonneg hB (2 * n))
    _ = B ^ (2 * n + 1) := by rw [pow_succ]

/-- Corner bounds of the second diagonal kernel: `|P|^(n-1) √P |v| ≤ B^(2n)` whenever
`|P| ≤ B²`, `|v| ≤ B` and `1 ≤ n`. -/
lemma pow_pred_abs_mul_sqrt_mul_le {P B v : ℝ} (n : ℕ) (hn : 1 ≤ n)
    (hB : 0 ≤ B) (hP : |P| ≤ B ^ 2) (hv : |v| ≤ B) :
    |P| ^ (n - 1) * Real.sqrt P * |v| ≤ B ^ (2 * n) := by
  have h2 : |P| ^ (n - 1) ≤ B ^ (2 * (n - 1)) := by
    have h := pow_le_pow_left₀ (abs_nonneg P) hP (n - 1)
    rwa [← pow_mul] at h
  have h3 : Real.sqrt P ≤ B := by
    have hle : Real.sqrt P ≤ Real.sqrt |P| := Real.sqrt_le_sqrt (le_abs_self P)
    have h4 : Real.sqrt |P| ≤ Real.sqrt (B ^ 2) := Real.sqrt_le_sqrt hP
    have h5 : Real.sqrt (B ^ 2) = B := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hB]
    linarith
  have hstep : |P| ^ (n - 1) * Real.sqrt P ≤ B ^ (2 * (n - 1)) * B :=
    mul_le_mul h2 h3 (Real.sqrt_nonneg P) (pow_nonneg hB (2 * (n - 1)))
  refine (mul_le_mul hstep hv (abs_nonneg v)
    (mul_nonneg (pow_nonneg hB (2 * (n - 1))) hB)).trans (le_of_eq ?_)
  have h2n : 2 * (n - 1) + 2 = 2 * n := by omega
  rw [show B ^ (2 * (n - 1)) * B * B = B ^ (2 * (n - 1)) * B ^ 2 by ring, ← pow_add, h2n]

/-- **Absolute bounds for the explicit diagonal kernels.** -/
theorem diagPhi_abs_bound (n : ℕ) (hn : 1 ≤ n) {B u v : ℝ} (hB : 0 ≤ B) (hu : |u| ≤ B) (hv : |v| ≤ B) :
    |Work.OddVolterra.Existence.diagPhi1 n (u, v)| ≤
        ((Nat.doubleFactorial (2 * n + 1) : ℝ) * B ^ (2 * n + 1)) / Real.sqrt 2 ∧
      |Work.OddVolterra.Existence.diagPhi2 n (u, v)| ≤
        ((Nat.doubleFactorial (2 * n - 1) : ℝ) * B ^ (2 * n)) / Real.sqrt 2 := by
  have hA2 : (0 : ℝ) ≤ (Nat.doubleFactorial (2 * n - 1) : ℝ) := Nat.cast_nonneg _
  have hP : |u * v| ≤ B ^ 2 := by
    rw [abs_mul, sq]
    exact mul_le_mul hu hv (abs_nonneg v) hB
  constructor
  · have hA : (0 : ℝ) ≤ (Nat.doubleFactorial (2 * n + 1) : ℝ) := Nat.cast_nonneg _
    have hkey := pow_abs_mul_sqrt_le n hB hP
    have hdecomp : diagPhi1 n (u, v) =
        (-1 : ℝ) ^ (n + 1) * ((Nat.doubleFactorial (2 * n + 1) : ℝ) *
          (((u * v) ^ n * Real.sqrt (u * v)) / Real.sqrt 2)) := by
      simp only [diagPhi1]; ring
    rw [hdecomp, abs_mul, abs_neg_one_pow, one_mul]
    rw [abs_mul, abs_div, abs_of_nonneg (Real.sqrt_nonneg 2), abs_of_nonneg hA]
    rw [abs_mul, abs_pow, abs_of_nonneg (Real.sqrt_nonneg (u * v))]
    have hmain : (Nat.doubleFactorial (2 * n + 1) : ℝ) *
          (|u * v| ^ n * Real.sqrt (u * v) / Real.sqrt 2) ≤
        (Nat.doubleFactorial (2 * n + 1) : ℝ) * (B ^ (2 * n + 1) / Real.sqrt 2) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hkey (Real.sqrt_nonneg 2)) hA
    convert hmain using 1 <;> ring
  · have hkey := pow_pred_abs_mul_sqrt_mul_le n hn hB hP hv
    have hdecomp : diagPhi2 n (u, v) =
        (-1 : ℝ) ^ n * ((Nat.doubleFactorial (2 * n - 1) : ℝ) *
          (((u * v) ^ (n - 1) * Real.sqrt (u * v) * v) / Real.sqrt 2)) := by
      simp only [diagPhi2]; ring
    rw [hdecomp, abs_mul, abs_neg_one_pow, one_mul]
    rw [abs_mul, abs_div, abs_of_nonneg (Real.sqrt_nonneg 2), abs_of_nonneg hA2]
    rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg (Real.sqrt_nonneg (u * v))]
    have hmain : (Nat.doubleFactorial (2 * n - 1) : ℝ) *
          (|u * v| ^ (n - 1) * Real.sqrt (u * v) * |v| / Real.sqrt 2) ≤
        (Nat.doubleFactorial (2 * n - 1) : ℝ) * (B ^ (2 * n) / Real.sqrt 2) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hkey (Real.sqrt_nonneg 2)) hA2
    convert hmain using 1 <;> ring

end Work.OddExistence.Estimates
