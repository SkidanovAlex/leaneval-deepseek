import Mathlib
import Submission.RS
import Submission.F_Psum_stable
import Submission.F_norm_Psum

/-! Section 3 objects of the paper: the cosine polynomial `c` and the even sine
polynomial `s_e`, defined from Rudin-Shapiro polynomials (paper eqs. (6),(7)). -/

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex

namespace Submission
namespace Sec3

/-- `e^{iθ}`. -/
def eθ (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

/-- `‖e^{iθ}‖ = 1`. -/
lemma norm_eθ (θ : ℝ) : ‖eθ θ‖ = 1 := by
  rw [eθ]
  exact Complex.norm_exp_ofReal_mul_I θ

/-- `z = e^{2iθ}` (paper writes `z = e^{2iθ}`). -/
def zθ (θ : ℝ) : ℂ := eθ (2 * θ)

lemma norm_zθ (θ : ℝ) : ‖zθ θ‖ = 1 := by
  rw [zθ]
  exact norm_eθ (2 * θ)

/-- A power of a unit-modulus complex number has unit modulus. -/
lemma norm_z_pow (z : ℂ) (m : ℕ) (hz : ‖z‖ = 1) : ‖z ^ m‖ = 1 := by
  rw [norm_pow, hz]
  simp

/-- The complex combination whose real part is the cosine polynomial `c(θ)` (paper (6)):

`z^T P_t(z) + z^{2T} Q_t(z)` with `z = e^{2iθ}`, `T = 2^(t+10)`. -/
def cval (t : ℕ) (θ : ℝ) : ℂ :=
  let z := zθ θ
  (z ^ 2 ^ (t + 10)) * Polynomial.eval z (RudinShapiro.P t) +
    (z ^ (2 * 2 ^ (t + 10))) * Polynomial.eval z (RudinShapiro.Q t)

/-- The cosine polynomial `c(θ) = Re(...)`. -/
def c (t : ℕ) (θ : ℝ) : ℝ := (cval t θ).re

/-- Bound `|c(θ)| ≤ sqrt(2^(t+1)) + sqrt(2^(t+1))` (Lemma 3.3 part 1: actually ≤ 2^((t+3)/2) ≤ √n later). -/
lemma abs_c_le (t : ℕ) (θ : ℝ) :
    |c t θ| ≤ Real.sqrt (2 ^ (t + 1)) + Real.sqrt (2 ^ (t + 1)) := by
  unfold c cval
  have hgen : ∀ z : ℂ, ‖z‖ = 1 →
      |(((z ^ 2 ^ (t + 10)) * Polynomial.eval z (RudinShapiro.P t)) +
          (z ^ (2 * 2 ^ (t + 10))) * Polynomial.eval z (RudinShapiro.Q t)).re|
        ≤ Real.sqrt (2 ^ (t + 1)) + Real.sqrt (2 ^ (t + 1)) := by
    intro z hz
    have hnorm := calc
      ‖((z ^ 2 ^ (t + 10)) * Polynomial.eval z (RudinShapiro.P t)) +
          (z ^ (2 * 2 ^ (t + 10))) * Polynomial.eval z (RudinShapiro.Q t)‖
          ≤ ‖(z ^ 2 ^ (t + 10)) * Polynomial.eval z (RudinShapiro.P t)‖ +
              ‖(z ^ (2 * 2 ^ (t + 10))) * Polynomial.eval z (RudinShapiro.Q t)‖ :=
            norm_add_le _ _
      _ = ‖Polynomial.eval z (RudinShapiro.P t)‖ + ‖Polynomial.eval z (RudinShapiro.Q t)‖ := by
          have h1 : ‖(z ^ 2 ^ (t + 10)) * Polynomial.eval z (RudinShapiro.P t)‖ =
              ‖Polynomial.eval z (RudinShapiro.P t)‖ := by
            rw [norm_mul]
            rw [norm_z_pow z (2 ^ (t + 10)) hz]
            simp
          have h2 : ‖(z ^ (2 * 2 ^ (t + 10))) * Polynomial.eval z (RudinShapiro.Q t)‖ =
              ‖Polynomial.eval z (RudinShapiro.Q t)‖ := by
            rw [norm_mul]
            rw [norm_z_pow z (2 * 2 ^ (t + 10)) hz]
            simp
          rw [h1, h2]
      _ ≤ Real.sqrt (2 ^ (t + 1)) + Real.sqrt (2 ^ (t + 1)) := by
          exact add_le_add (RudinShapiro.norm_P_eval_le t z hz) (RudinShapiro.norm_Q_eval_le t z hz)
    have hre : |(((z ^ 2 ^ (t + 10)) * Polynomial.eval z (RudinShapiro.P t)) +
          (z ^ (2 * 2 ^ (t + 10))) * Polynomial.eval z (RudinShapiro.Q t)).re| ≤
        ‖((z ^ 2 ^ (t + 10)) * Polynomial.eval z (RudinShapiro.P t)) +
          (z ^ (2 * 2 ^ (t + 10))) * Polynomial.eval z (RudinShapiro.Q t)‖ :=
      Complex.abs_re_le_norm _
    exact le_trans hre hnorm
  exact hgen (zθ θ) (norm_zθ θ)

/-- The combination defining the even sine polynomial `s_e(θ) = Im[...]` (paper (7)):

`P<_{n+1}(z) − z^T P_t(z) − z^{2T}P_t(z)`, where `P<_{n+1}` is the prefix `Psum s (n+1)`
with `s` a level with `n + 1 ≤ 2^s`. -/
def seval (s t n : ℕ) (θ : ℝ) : ℂ :=
  let z := zθ θ
  Polynomial.eval z (RudinShapiro.Psum s (n + 1)) -
    (z ^ 2 ^ (t + 10)) * Polynomial.eval z (RudinShapiro.P t) -
    (z ^ (2 * 2 ^ (t + 10))) * Polynomial.eval z (RudinShapiro.P t)

/-- The even sine polynomial `s_e(θ) = Im(seval ...)`. -/
def s_e (s t n : ℕ) (θ : ℝ) : ℝ := (seval s t n θ).im

/-- Bound for `s_e` (Lemma 3.3 part 2, with a loose constant):

`|s_e(θ)| ≤ 6 * sqrt (n+1) + 2 * sqrt (2^(t+1))`.  (We do not need the paper's sharp
`6 * sqrt n`; any comparable bound is fine since all final constants are flexible.) -/
lemma abs_s_e_le (s t n : ℕ) (hs : n + 1 ≤ 2 ^ s) (θ : ℝ) :
    |s_e s t n θ| ≤ 6 * Real.sqrt (n + 1) + 2 * Real.sqrt (2 ^ (t + 1)) := by
  unfold s_e seval
  have hgen : ∀ z : ℂ, ‖z‖ = 1 →
      |((Polynomial.eval z (RudinShapiro.Psum s (n + 1)) -
          (z ^ 2 ^ (t + 10)) * Polynomial.eval z (RudinShapiro.P t) -
          (z ^ (2 * 2 ^ (t + 10))) * Polynomial.eval z (RudinShapiro.P t))).im|
        ≤ 6 * Real.sqrt (n + 1) + 2 * Real.sqrt (2 ^ (t + 1)) := by
    intro z hz
    let A : ℂ := Polynomial.eval z (RudinShapiro.Psum s (n + 1))
    let B : ℂ := (z ^ 2 ^ (t + 10)) * Polynomial.eval z (RudinShapiro.P t)
    let C : ℂ := (z ^ (2 * 2 ^ (t + 10))) * Polynomial.eval z (RudinShapiro.P t)
    have hA : ‖A‖ ≤ 6 * Real.sqrt (n + 1) := by
      simpa [A] using (RudinShapiro.norm_Psum_eval_le s (n + 1) hs z hz)
    have hB : ‖B‖ ≤ Real.sqrt (2 ^ (t + 1)) := by
      rw [norm_mul]
      rw [norm_z_pow z (2 ^ (t + 10)) hz]
      simp
      exact RudinShapiro.norm_P_eval_le t z hz
    have hC : ‖C‖ ≤ Real.sqrt (2 ^ (t + 1)) := by
      rw [norm_mul]
      rw [norm_z_pow z (2 * 2 ^ (t + 10)) hz]
      simp
      exact RudinShapiro.norm_P_eval_le t z hz
    have hnorm : ‖A - B - C‖ ≤ 6 * Real.sqrt (n + 1) + 2 * Real.sqrt (2 ^ (t + 1)) := by
      calc
        ‖A - B - C‖ ≤ ‖A - B‖ + ‖C‖ := norm_sub_le (A - B) C
        _ ≤ ‖A‖ + ‖B‖ + ‖C‖ := by linarith [norm_sub_le A B]
        _ ≤ 6 * Real.sqrt (n + 1) + 2 * Real.sqrt (2 ^ (t + 1)) := by
            nlinarith [hA, hB, hC]
    have him : |(A - B - C).im| ≤ ‖A - B - C‖ := Complex.abs_im_le_norm (A - B - C)
    have hres : |(A - B - C).im| ≤ 6 * Real.sqrt (n + 1) + 2 * Real.sqrt (2 ^ (t + 1)) :=
      le_trans him hnorm
    change |(A - B - C).im| ≤ 6 * Real.sqrt (n + 1) + 2 * Real.sqrt (2 ^ (t + 1))
    exact hres
  exact hgen (zθ θ) (norm_zθ θ)

end Sec3
end Submission
