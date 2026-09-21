import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Existence.diag_K1_explicit

/-!
# The second Abel kernel `K₂` on the diagonal for the unperturbed (`h = 0`) case

For the zero parallel-body offset `h = 0` the line is `L(s,t) = s t`, the slope
is `∂_s L(s,t) = t`, and the divided difference vanishes on the diagonal:
`H(s,s) = h'(s) = 0`.  Hence at `σ = s`

* `J₂(s,s,t) = (2n-1)!! (-(s t²))^n t`,
* `Kden(s,s,t) = √(t · 2 s t) = √(2s) |t|`,

and the diagonal value of the second Abel kernel is the explicit

`K₂(s,s,t) = (2n-1)!! (-s)^n t |t|^{2n-1} / √(2s)`,
` s > 0`, `n ≥ 1`.

This is the diagonal datum needed to evaluate the Abel-averaged kernel `G₂`
at `σ = s`; it is the companion of `diag_K1_explicit`.
-/

namespace Work.OddVolterra.Existence

open Work.OddVolterra

/-- The diagonal numerator `J₂` for the zero perturbation: the `if` takes its
`σ = s` branch and the line/slope collapse to `s t` and `t`. -/
lemma diag_J2_zero (n : ℕ) (s t : ℝ) :
    J2 n (fun _ : ℝ => 0) s s t
      = ((Nat.doubleFactorial (2 * n - 1) : ℝ)) * (-(s * t * t)) ^ n * t := by
  unfold J2 line lineSlope
  simp

lemma diag_K2_explicit (n : ℕ) (hn : 1 ≤ n) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    Work.OddVolterra.K2 n (fun _ : ℝ => 0) s s t =
      ((Nat.doubleFactorial (2 * n - 1) : ℝ)) * (-s) ^ n * (t * |t| ^ (2 * n - 1))
        / Real.sqrt (2 * s) := by
  have hpow : (-(s * t ^ 2)) ^ n * t = (-s) ^ n * (t * |t| ^ (2 * n - 1)) * |t| := by
    have h2 : (t ^ 2) ^ n = |t| ^ (2 * n) := by rw [← sq_abs t, ← pow_mul]
    have h3 : |t| ^ (2 * n - 1) * |t| = |t| ^ (2 * n) := by
      rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ 2 * n by omega)]
    rw [show -(s * t ^ 2) = (-s) * t ^ 2 by ring, mul_pow, h2, ← h3]
    ring
  have hnum : ((Nat.doubleFactorial (2 * n - 1) : ℝ)) * (-(s * t ^ 2)) ^ n * t
      = ((Nat.doubleFactorial (2 * n - 1) : ℝ)) *
          ((-s) ^ n * (t * |t| ^ (2 * n - 1))) * |t| := by
    calc ((Nat.doubleFactorial (2 * n - 1) : ℝ)) * (-(s * t ^ 2)) ^ n * t
        = ((Nat.doubleFactorial (2 * n - 1) : ℝ)) * ((-(s * t ^ 2)) ^ n * t) := by ring
      _ = ((Nat.doubleFactorial (2 * n - 1) : ℝ)) *
            ((-s) ^ n * (t * |t| ^ (2 * n - 1)) * |t|) := by rw [hpow]
      _ = ((Nat.doubleFactorial (2 * n - 1) : ℝ)) *
            ((-s) ^ n * (t * |t| ^ (2 * n - 1))) * |t| := by ring
  unfold K2
  rw [diag_J2_zero, diag_Kden_zero, show -(s * t * t) = -(s * t ^ 2) by ring, hnum,
    sqrt_two_mul_sq s t hs]
  rcases eq_or_ne t 0 with ht | ht
  · subst ht
    simp
  · have htab : |t| ≠ 0 := abs_ne_zero.mpr ht
    rw [mul_div_mul_right _ _ htab]
    ring

end Work.OddVolterra.Existence
