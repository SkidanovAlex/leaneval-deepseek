/-
  Work.WilE2 — area E2.  The polynomial bound produced by the Khovanskii elimination.

  The elimination replaces a system of `n` equations in `ℝⁿ` with `r+1` chain functions by a
  system of `n+1` equations in `ℝⁿ⁺¹` with `r` chain functions, and the total degree of the new
  system is at most `2 * D + n + 1` where `D` is the total degree of the old one (the Rolle
  determinant adds one equation of degree `≤ D + n + 1`; see `ESys.rolleDet_totalDegree_le`).
  Iterating this `r` times and finishing with the Bezout bound `D ^ n` gives a bound which is
  polynomial in `D` for fixed `n + r`.  This module records that bookkeeping explicitly, so
  that the final statement `s.card ≤ p.eval D` has a concrete witness polynomial `khoPoly`.
-/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Basic

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open Classical
namespace Work.WilE2

/-- The bound obtained by iterating the elimination `r` times from a system of `n` equations
with total degree `D`, followed by Bezout. -/
def Khov : ℕ → ℕ → ℕ → ℕ
  | 0, n, D => D ^ n
  | (r + 1), n, D => Khov r (n + 1) (2 * D + n + 1)

/-- The total degree after `i` eliminations is at most `2^i (D + 2(n+i) + 2)`. -/
theorem Khov_le (r n D : ℕ) : Khov r n D ≤ (2 ^ r * (D + 2 * (n + r) + 2)) ^ (n + r) := by
  induction r generalizing n D with
  | zero =>
    simp only [Khov, pow_zero, one_mul, Nat.zero_add]
    exact Nat.pow_le_pow_left (by omega) n
  | succ r ih =>
    have h₁ : Khov (r + 1) n D = Khov r (n + 1) (2 * D + n + 1) := rfl
    rw [h₁]
    refine (ih (n + 1) (2 * D + n + 1)).trans ?_
    have he : n + 1 + r = n + r + 1 := by omega
    rw [he]
    refine Nat.pow_le_pow_left ?_ (n + r + 1)
    have e1 : 2 * D + n + 1 + 2 * (n + r + 1) + 2 = 2 * D + 3 * n + 2 * r + 5 := by omega
    have e2 : D + 2 * (n + (r + 1)) + 2 = D + 2 * n + 2 * r + 4 := by omega
    rw [e1, e2, pow_succ]
    rw [mul_assoc]
    refine Nat.mul_le_mul_left _ ?_
    omega

/-- The witness polynomial: for a system with a chain of at most `F` functions and at most `F`
equations, `khoPoly F` evaluated at the total degree dominates `Khov`. -/
def khoPoly (F : ℕ) : Polynomial ℕ :=
  Polynomial.C (2 ^ (2 * F * F)) * (Polynomial.X + Polynomial.C (4 * F + 4)) ^ (2 * F)

theorem khoPoly_eval (F D : ℕ) :
    (khoPoly F).eval D = 2 ^ (2 * F * F) * (D + (4 * F + 4)) ^ (2 * F) := by
  simp [khoPoly]

/-- **The polynomial bound.**  If `n + r ≤ F`, the iterated elimination bound is dominated by
the single polynomial `khoPoly F` evaluated at the total degree `D`. -/
theorem Khov_le_khoPoly (F r n D : ℕ) (h : n + r ≤ F) :
    Khov r n D ≤ (khoPoly F).eval D := by
  rw [khoPoly_eval]
  refine (Khov_le r n D).trans ?_
  have hr : r ≤ F := by omega
  have hnr : n + r ≤ 2 * F := by omega
  have hbase : 2 ^ r * (D + 2 * (n + r) + 2) ≤ 2 ^ F * (D + (4 * F + 4)) := by
    have h1 : 2 ^ r ≤ 2 ^ F := Nat.pow_le_pow_right (by simp) hr
    have h3 : 2 * (n + r) ≤ 4 * F := by
      calc 2 * (n + r) ≤ 2 * F := Nat.mul_le_mul_left 2 h
        _ ≤ 4 * F := Nat.mul_le_mul_right F (by simp)
    have h2 : D + 2 * (n + r) + 2 ≤ D + (4 * F + 4) := by omega
    exact Nat.mul_le_mul h1 h2
  refine (Nat.pow_le_pow_left hbase (n + r)).trans ?_
  refine (Nat.pow_le_pow_right (by simp) hnr).trans ?_
  rw [mul_pow, ← pow_mul, mul_comm F (2 * F)]

end Work.WilE2
