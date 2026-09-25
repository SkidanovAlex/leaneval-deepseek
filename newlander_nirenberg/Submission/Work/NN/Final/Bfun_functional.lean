import Mathlib
import Submission.Work.NN.Final.MomentSetup

namespace Work.NN.Final

/-- The coefficient identity underlying the functional equation:
`mcoef (n+1) * 3^(n+1) = mcoef (n+1) - mcoef n`. -/
lemma mcoef_mul_three_pow (n : ℕ) :
    mcoef (n + 1) * (3 : ℝ) ^ (n + 1) = mcoef (n + 1) - mcoef n := by
  have hD : (3 : ℝ) ^ (n + 1) - 1 ≠ 0 := by
    have h := three_pow_ge_real n
    have : (0 : ℝ) < 2 * (n + 1) := by positivity
    linarith
  rw [mcoef_succ]
  field_simp
  ring

theorem Bfun_functional (u : ℝ) : Bfun (3 * u) = (1 - u) * Bfun u := by
  -- summability facts
  have hFsum : Summable (fun n => mcoef n * u ^ n) := mcoef_summable u
  have hF1sum : Summable (fun n => mcoef (n + 1) * u ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr hFsum
  have hSsum : Summable (fun n => mcoef n * u ^ (n + 1)) := by
    refine (hFsum.mul_left u).congr (fun n => ?_)
    rw [pow_succ]; ring
  have hGsum : Summable (fun n => mcoef n * (3 : ℝ) ^ n * u ^ n) := by
    refine (mcoef_summable (3 * u)).congr (fun n => ?_)
    rw [mul_pow]; ring
  -- left-hand side as a power series in the coefficients
  have hL : Bfun (3 * u) = ∑' n, mcoef n * (3 : ℝ) ^ n * u ^ n := by
    rw [Bfun]
    exact tsum_congr (fun n => by rw [mul_pow]; ring)
  -- split off the constant term
  have hGzero := Summable.tsum_eq_zero_add hGsum
  have hG0 : mcoef 0 * (3 : ℝ) ^ 0 * u ^ 0 = 1 := by simp
  rw [hG0] at hGzero
  -- termwise identity `mcoef(n+1) * 3^(n+1) * u^(n+1) = mcoef(n+1)*u^(n+1) - mcoef n * u^(n+1)`
  have hterm : ∀ n, mcoef (n + 1) * (3 : ℝ) ^ (n + 1) * u ^ (n + 1)
      = mcoef (n + 1) * u ^ (n + 1) - mcoef n * u ^ (n + 1) := by
    intro n
    have h := mcoef_mul_three_pow n
    rw [show mcoef (n + 1) * (3 : ℝ) ^ (n + 1) * u ^ (n + 1)
          = (mcoef (n + 1) * (3 : ℝ) ^ (n + 1)) * u ^ (n + 1) from by ring, h]
    ring
  have hstep : (∑' n, mcoef (n + 1) * (3 : ℝ) ^ (n + 1) * u ^ (n + 1))
      = ∑' n, mcoef (n + 1) * u ^ (n + 1) - ∑' n, mcoef n * u ^ (n + 1) := by
    rw [tsum_congr hterm]
    exact Summable.tsum_sub hF1sum hSsum
  rw [hstep] at hGzero
  -- the value `Bfun u` split at its constant term
  have hBu : Bfun u = 1 + ∑' n, mcoef (n + 1) * u ^ (n + 1) := by
    rw [Bfun, Summable.tsum_eq_zero_add hFsum]
    simp
  -- `u * Bfun u` as the shifted series
  have huBu : u * Bfun u = ∑' n, mcoef n * u ^ (n + 1) := by
    rw [Bfun, ← Summable.tsum_mul_left u hFsum]
    exact tsum_congr (fun n => by rw [pow_succ]; ring)
  calc Bfun (3 * u) = ∑' n, mcoef n * (3 : ℝ) ^ n * u ^ n := hL
    _ = 1 + (∑' n, mcoef (n + 1) * u ^ (n + 1) - ∑' n, mcoef n * u ^ (n + 1)) := hGzero
    _ = (1 - u) * Bfun u := by
          rw [sub_mul, one_mul, huBu, hBu]; ring

end Work.NN.Final
