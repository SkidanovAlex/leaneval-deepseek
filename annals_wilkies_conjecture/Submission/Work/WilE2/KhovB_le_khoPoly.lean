import Mathlib
import Submission.Work.WilE2.KhovB
import Submission.Work.WilE2.Bound

namespace Work.WilE2

/-- Unwinding the recursion: after `r` elimination steps the running total degree is at most
`2 ^ r * (D + n + 8)` and the number of variables is `n + 2 * r`. -/
lemma KhovB_le_two_pow_mul (r n D : ℕ) :
    KhovB r n D ≤ (2 ^ r * (D + n + 8)) ^ (n + 2 * r) := by
  induction r generalizing n D with
  | zero =>
    rw [KhovB]
    simp only [pow_zero, one_mul, mul_zero, Nat.add_zero]
    exact Nat.pow_le_pow_left (by omega) n
  | succ r ih =>
    have hstep : KhovB (r + 1) n D = KhovB r (n + 2) (2 * D + n + 6) := rfl
    rw [hstep]
    refine (ih (n + 2) (2 * D + n + 6)).trans ?_
    have he : n + 2 * (r + 1) = (n + 2) + 2 * r := by ring
    rw [he]
    refine Nat.pow_le_pow_left ?_ ((n + 2) + 2 * r)
    rw [pow_succ, mul_assoc]
    exact Nat.mul_le_mul_left _ (by omega)

theorem KhovB_le_khoPoly (F r n D : ℕ) (h : n + r ≤ F) :
    KhovB r n D ≤ (khoPoly F).eval (D + n) := by
  rw [khoPoly_eval]
  rcases Nat.eq_zero_or_pos F with hF | hF
  · subst hF
    have hn : n = 0 := by omega
    have hr : r = 0 := by omega
    subst hn
    subst hr
    simp [KhovB]
  · refine (KhovB_le_two_pow_mul r n D).trans ?_
    have hrF : r ≤ F := by omega
    have hnr : n + 2 * r ≤ 2 * F := by omega
    have hbase : 2 ^ r * (D + n + 8) ≤ 2 ^ F * (D + n + (4 * F + 4)) :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hrF) (by omega)
    refine (Nat.pow_le_pow_left hbase (n + 2 * r)).trans ?_
    rw [mul_pow, ← pow_mul]
    refine Nat.mul_le_mul ?_ ?_
    · refine Nat.pow_le_pow_right (by norm_num) ?_
      calc F * (n + 2 * r) ≤ F * (2 * F) := Nat.mul_le_mul_left F hnr
        _ = 2 * F * F := by ring
    · exact Nat.pow_le_pow_right (by omega) hnr

end Work.WilE2
