import Mathlib
import Submission.Work.LinnikAreas.LoneLowerDefs
import Submission.Work.LinnikAreas.lamAbelIntegral

namespace Work.LinnikAreas

open DirichletCharacter Complex
open scoped BigOperators

/-- The `n`-th summand of the target series is the norm of the `LSeries.term` of `lam ψ`
at the point `s = 1 + β`, summed over `n`.  This is the pointwise identity that converts
the summability of the `L`-series of `lam ψ` (which is `ζ(s)L(s,ψ)`) into the requested
statement. -/
lemma lam_norm_term_eq {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) {β : ℝ} (hβ : 0 < β)
    (n : ℕ) :
    ‖LSeries.term (fun n => lam ψ n) ((1 + β : ℝ) : ℂ) n‖
      = ‖lam ψ n * (n : ℂ) ^ (-(β : ℂ))‖ / (n : ℝ) ^ (1 : ℝ) := by
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · have hz : (0 : ℂ) ^ (-(β : ℂ)) = 0 := Complex.zero_cpow (by
      simp only [ne_eq, neg_eq_zero, Complex.ofReal_eq_zero]
      exact hβ.ne')
    simp [hz]
  · rw [if_neg hn, Complex.ofReal_re, norm_mul,
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
    simp only [Complex.neg_re, Complex.ofReal_re]
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have h2 : (n : ℝ) ^ (-β) / (n : ℝ) ^ (1:ℝ) = (n : ℝ) ^ (-(1 + β)) := by
      rw [← Real.rpow_sub hnpos]
      congr 1
      ring
    rw [div_eq_mul_inv, (Real.rpow_neg hnpos.le (1 + β)).symm, mul_div_assoc, h2]

theorem lamCoeffSummable {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) {β : ℝ} (hβ : 0 < β) :
    Summable (fun n : ℕ => ‖Work.LinnikAreas.lam ψ n * (n : ℂ) ^ (-(β : ℂ))‖ / (n : ℝ) ^ (1 : ℝ)) := by
  have hs1 : 1 < (((1 + β : ℝ) : ℂ)).re := by
    rw [Complex.ofReal_re]
    linarith
  exact ((LSeriesSummable_lam ψ hs1).norm).congr (fun n => lam_norm_term_eq ψ hβ n)

end Work.LinnikAreas
