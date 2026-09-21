import Mathlib
import Submission.Work.OddCurveB.Existence.Explicit

/-!
# The diagonal Abel kernels are "power times square root" functions

Write `X = (t + h' s) * (s t + h s)` for the radicand of the diagonal denominator.  Then the two
diagonal kernels of `Submission.Work.OddCurveB.Existence.Explicit` are

`Kdiag1 n s hs hp t = (2n+1)!! · (-1)^{n+1} / √2 · (X^n · √X)`,
`Kdiag2 n s hs hp t = (2n-1)!! · (-1)^n   / √2 · (X^{n-1} · √X) · (t + hp)`  (`n ≥ 1`).

These identities hold for **every** real `X`, because Lean's divisions and square roots return `0`
in the degenerate range: for `X ≤ 0` both sides vanish.  In particular each kernel is a
*continuous* function of `(s, hs, hp, t)` — there is no singularity at the vanishing of the
radicand, and the estimates on the perturbed data therefore reduce to the elementary Lipschitz
theory of `x ↦ x^k √x` on a bounded interval.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddCurveB.Existence

noncomputable section

/-- The radicand of the diagonal denominator. -/
def Drad (s hs hp t : ℝ) : ℝ := (t + hp) * (s * t + hs)

/-- `X^{k+1} = X^k √X √X` for `X > 0`. -/
lemma pow_succ_eq_mul_sqrt_mul_sqrt {X : ℝ} (hX : 0 < X) (k : ℕ) :
    X ^ (k + 1) = X ^ k * (Real.sqrt X * Real.sqrt X) := by
  rw [pow_succ]
  congr 1
  have h : Real.sqrt X * Real.sqrt X = X := by
    rw [← pow_two, Real.sq_sqrt (le_of_lt hX)]
  exact h.symm

/-- **The first diagonal kernel is `X^n √X` up to a constant.** -/
theorem Kdiag1_eq (n : ℕ) (s hs hp t : ℝ) :
    Kdiag1 n s hs hp t =
      ((Nat.doubleFactorial (2 * n + 1) : ℝ) * (-1) ^ (n + 1) / Real.sqrt 2) *
        (Drad s hs hp t ^ n * Real.sqrt (Drad s hs hp t)) := by
  unfold Kdiag1 Drad
  set X : ℝ := (t + hp) * (s * t + hs) with hX
  have hden : (t + hp) * (2 * (s * t + hs)) = 2 * X := by rw [hX]; ring
  rw [hden]
  by_cases hXpos : 0 < X
  · have hsqrtX : 0 < Real.sqrt X := Real.sqrt_pos.mpr hXpos
    have hmul : Real.sqrt (2 * X) = Real.sqrt 2 * Real.sqrt X := Real.sqrt_mul (by norm_num) X
    rw [hmul]
    have hcomm : (s * t + hs) * (t + hp) = X := by rw [hX]; ring
    rw [hcomm]
    have hpow : (-X) ^ (n + 1) = (-1 : ℝ) ^ (n + 1) * X ^ (n + 1) := by
      rw [show (-X : ℝ) = (-1) * X by ring, mul_pow]
    rw [hpow]
    rw [pow_succ_eq_mul_sqrt_mul_sqrt hXpos n]
    field_simp
  · have hXle : X ≤ 0 := not_lt.mp hXpos
    have hsqrt : Real.sqrt (2 * X) = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
    have hsqrtX : Real.sqrt X = 0 := Real.sqrt_eq_zero_of_nonpos hXle
    simp [hsqrt, hsqrtX]

/-- **The second diagonal kernel is `X^{n-1} √X (t + hp)` up to a constant** (for `n ≥ 1`). -/
theorem Kdiag2_eq (n : ℕ) (hn : 1 ≤ n) (s hs hp t : ℝ) :
    Kdiag2 n s hs hp t =
      ((Nat.doubleFactorial (2 * n - 1) : ℝ) * (-1) ^ n / Real.sqrt 2) *
        (Drad s hs hp t ^ (n - 1) * Real.sqrt (Drad s hs hp t)) * (t + hp) := by
  unfold Kdiag2 Drad
  set X : ℝ := (t + hp) * (s * t + hs) with hX
  have hden : (t + hp) * (2 * (s * t + hs)) = 2 * X := by rw [hX]; ring
  rw [hden]
  by_cases hXpos : 0 < X
  · have hsqrtX : 0 < Real.sqrt X := Real.sqrt_pos.mpr hXpos
    have hmul : Real.sqrt (2 * X) = Real.sqrt 2 * Real.sqrt X := Real.sqrt_mul (by norm_num) X
    rw [hmul]
    have hcomm : (s * t + hs) * (t + hp) = X := by rw [hX]; ring
    rw [hcomm]
    have hpow : (-X) ^ n = (-1 : ℝ) ^ n * X ^ n := by
      rw [show (-X : ℝ) = (-1) * X by ring, mul_pow]
    rw [hpow]
    have hXX : X ^ n = X ^ (n - 1) * (Real.sqrt X * Real.sqrt X) := by
      have h := pow_succ_eq_mul_sqrt_mul_sqrt hXpos (n - 1)
      rwa [show n - 1 + 1 = n by omega] at h
    rw [hXX]
    field_simp
  · have hXle : X ≤ 0 := not_lt.mp hXpos
    have hsqrt : Real.sqrt (2 * X) = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
    have hsqrtX : Real.sqrt X = 0 := Real.sqrt_eq_zero_of_nonpos hXle
    simp [hsqrt, hsqrtX]

end

end Work.OddCurveB.Existence
