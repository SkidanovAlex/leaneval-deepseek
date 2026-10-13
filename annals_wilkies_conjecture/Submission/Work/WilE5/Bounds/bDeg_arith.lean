import Mathlib
import Submission.Work.WilE5.Profile

namespace Work.WilE5.Bounds

/-- The arithmetic core: replacing the "coefficient" `B` by `D + 1` (which it is bounded by)
and the a-priori sum-bound `S` by its profile value `P` (which it is bounded by) can only
increase the total. -/
private theorem arith (B D P S a b : ℕ) (hB : B ≤ D + 1) (hS : S ≤ P) :
    D + B * (S + a + b) + S ≤ (D + 1) + P + (D + 1) * (P + a + b) := by
  have hab : S + a + b ≤ P + a + b := by omega
  have h1 : B * (S + a + b) ≤ (D + 1) * (P + a + b) := Nat.mul_le_mul hB hab
  have h2 : D + B * (S + a + b) + S ≤ (D + 1) + (D + 1) * (P + a + b) + P :=
    Nat.add_le_add (Nat.add_le_add (Nat.le_succ D) h1) hS
  calc D + B * (S + a + b) + S
      ≤ (D + 1) + (D + 1) * (P + a + b) + P := h2
    _ = (D + 1) + P + (D + 1) * (P + a + b) := by ring

theorem bDeg_arith (Me : Polynomial ℕ) (p q D B S d NQ M : ℕ)
    (hB : B ≤ D + 1)
    (hS : S ≤ (Work.WilE5.profS Me p q (2 * q + 1)).eval D)
    (hd : d = (Work.WilE5.profD Me p q (2 * q + 1)).eval D)
    (hNQ : NQ = (Work.WilE5.profN Me p q (2 * q + 1)).eval D)
    (hM : M = (Work.WilE5.profM Me p q (2 * q + 1)).eval D) :
    D + B * (S + (NQ + (D + 2 * q + 1)) * d + NQ * (M + 1) ^ q * q * d) + S ≤
      (Work.WilE5.bDeg Me p q).eval D := by
  have hdeg : (Work.WilE5.bDeg Me p q).eval D =
      (D + 1) + (Work.WilE5.profS Me p q (2 * q + 1)).eval D +
        (D + 1) * ((Work.WilE5.profS Me p q (2 * q + 1)).eval D +
          (NQ + (D + 2 * q + 1)) * d + NQ * (M + 1) ^ q * q * d) := by
    simp only [Work.WilE5.bDeg, Work.WilE5.profLeaf, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    rw [← hd, ← hNQ, ← hM]
    ring
  rw [hdeg]
  exact arith B D ((Work.WilE5.profS Me p q (2 * q + 1)).eval D) S
    ((NQ + (D + 2 * q + 1)) * d) (NQ * (M + 1) ^ q * q * d) hB hS

end Work.WilE5.Bounds
