import Mathlib
import Submission.Work.OddVolterra.Defs

/-!
# The first Abel kernel `K₁` on the diagonal for the unperturbed (`h = 0`) case

For the zero parallel-body offset `h = 0` the line is `L(s,t) = s t`, the slope
is `∂_s L(s,t) = t`, and the divided difference vanishes on the diagonal:
`H(s,s) = h'(s) = 0`.  Hence at `σ = s`

* `J₁(s,s,t) = (2n+1)!! (-(s t²))^{n+1}`,
* `Kden(s,s,t) = √(t · 2 s t) = √(2s) |t|`,

and the diagonal value of the first Abel kernel is the explicit

`K₁(s,s,t) = (2n+1)!! (-s)^{n+1} |t|^{2n+1} / √(2s)`,
` s > 0`.

This is the diagonal datum needed to evaluate the Abel-averaged kernel `G₂`
at `σ = s`.
-/

namespace Work.OddVolterra.Existence

open Work.OddVolterra

/-- The diagonal numerator `J₁` for the zero perturbation: the `if` takes its
`σ = s` branch and the line/slope collapse to `s t` and `t`. -/
lemma diag_J1_zero (n : ℕ) (s t : ℝ) :
    J1 n (fun _ : ℝ => 0) s s t
      = ((Nat.doubleFactorial (2 * n + 1) : ℝ)) * (-(s * t * t)) ^ (n + 1) := by
  unfold J1 line lineSlope
  simp

/-- The diagonal denominator `Kden` for the zero perturbation:
`√((t + H(s,s)) (L(s,t) + L(s,t))) = √(2 s t²)`. -/
lemma diag_Kden_zero (s t : ℝ) :
    Kden (fun _ : ℝ => 0) s s t = Real.sqrt (2 * s * t ^ 2) := by
  unfold Kden hquot line
  simp
  congr 1
  ring

/-- `√(2 s t²) = √(2s) |t|` for `s > 0`. -/
lemma sqrt_two_mul_sq (s t : ℝ) (hs : 0 < s) :
    Real.sqrt (2 * s * t ^ 2) = Real.sqrt (2 * s) * |t| := by
  rw [show 2 * s * t ^ 2 = (2 * s) * t ^ 2 by ring,
    Real.sqrt_mul (by linarith : (0:ℝ) ≤ 2 * s), Real.sqrt_sq_eq_abs]

lemma diag_K1_explicit (n : ℕ) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    Work.OddVolterra.K1 n (fun _ : ℝ => 0) s s t =
      ((Nat.doubleFactorial (2 * n + 1) : ℝ)) * (-s) ^ (n + 1) * |t| ^ (2 * n + 1)
        / Real.sqrt (2 * s) := by
  have hpow : (-(s * t ^ 2)) ^ (n + 1) = (-s) ^ (n + 1) * |t| ^ (2 * n + 2) := by
    rw [show -(s * t ^ 2) = (-s) * t ^ 2 by ring, mul_pow]
    congr 1
    rw [← sq_abs t, ← pow_mul, show 2 * (n + 1) = 2 * n + 2 by ring]
  unfold K1
  rw [diag_J1_zero, diag_Kden_zero, show -(s * t * t) = -(s * t ^ 2) by ring,
    hpow, sqrt_two_mul_sq s t hs]
  rcases eq_or_ne t 0 with ht | ht
  · subst ht
    simp
  · have htab : |t| ≠ 0 := abs_ne_zero.mpr ht
    rw [show |t| ^ (2 * n + 2) = |t| ^ (2 * n + 1) * |t| by
      rw [show 2 * n + 2 = 2 * n + 1 + 1 by ring, pow_succ]]
    rw [show ((Nat.doubleFactorial (2 * n + 1) : ℝ)) *
          ((-s) ^ (n + 1) * (|t| ^ (2 * n + 1) * |t|))
        = (((Nat.doubleFactorial (2 * n + 1) : ℝ)) * (-s) ^ (n + 1) * |t| ^ (2 * n + 1))
            * |t| by ring]
    rw [mul_div_mul_right _ _ htab]

end Work.OddVolterra.Existence
