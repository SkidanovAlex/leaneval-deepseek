import Mathlib.Analysis.Real.Sqrt
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_zero_card
import Submission.Commons.NumberTheory.FriedlanderIwaniec.square_divisor_max_characterization

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- The number of square-zero elements of `ZMod d` is at most `√d`.

Indeed, `#{α : ZMod d | α ^ 2 = 0} = ∏_{p | d} p ^ (v_p(d) / 2)`, and the square of this
integer divides `d`, so the count itself is a nonnegative integer whose square is `≤ d`. -/
theorem sqZero_card_le_sqrt (d : ℕ) (hd : 1 ≤ d) :
    (({α : ZMod d | α ^ 2 = 0}).ncard : ℝ) ≤ Real.sqrt d := by
  have hd0 : 0 < d := hd
  rw [sq_roots_zero_card hd0]
  apply Real.le_sqrt_of_sq_le
  have hP2 : ((Nat.primeFactors d).prod (fun p => p ^ (d.factorization p / 2))) ^ 2 ∣ d :=
    (square_divisor_max_characterization hd0).1
  have hle : ((Nat.primeFactors d).prod (fun p => p ^ (d.factorization p / 2))) ^ 2 ≤ d :=
    Nat.le_of_dvd hd0 hP2
  exact_mod_cast hle

end Commons.NumberTheory.FriedlanderIwaniec