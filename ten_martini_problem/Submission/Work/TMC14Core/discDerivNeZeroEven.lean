import Mathlib
import Submission.Work.TMC14Core.RatRot
import Submission.Work.TMC14Core.ceyDerivBound
import Submission.Work.TMC14Core.ceyEvenGen

namespace Work.TMC14Core

theorem discDerivNeZeroEven (p : ℤ) (q m : ℕ) (lam : ℝ) (hm : q = 2 * m + 2) (hq : 1 ≤ q)
    (hpq : Nat.Coprime p.natAbs q) (hlam : 0 < lam) (E : ℝ) (hE : E ≠ 0)
    (hU : ‖(Work.TMC14Core.disc p q lam).eval (E : ℂ)‖ ≤ 2 + 2 * lam ^ q) :
    (Polynomial.derivative (Work.TMC14Core.disc p q lam)).eval (E : ℂ) ≠ 0 := by
  -- The even-`q` Choi--Elliott--Yui bound specialised to `a = E`, `c = Δ(E)`.
  have hb := ceyEvenGen.ceyEvenDiscDerivGen p q m hm hpq lam hlam E
    ((disc p q lam).eval (E : ℂ)) hU rfl
  -- `0 < q λ^m |E| ≤ ‖Δ'(E)‖`, so `Δ'(E) ≠ 0`.
  have hpos : 0 < ‖(disc p q lam).derivative.eval (E : ℂ)‖ := by
    have h1 : 0 < (q : ℝ) * lam ^ m * |E| := by
      have hq' : 0 < (q : ℝ) := by positivity
      have hlam' : 0 < lam ^ m := pow_pos hlam m
      have hE' : 0 < |E| := abs_pos.mpr hE
      positivity
    exact lt_of_lt_of_le h1 hb
  exact norm_ne_zero_iff.mp (ne_of_gt hpos)

end Work.TMC14Core
