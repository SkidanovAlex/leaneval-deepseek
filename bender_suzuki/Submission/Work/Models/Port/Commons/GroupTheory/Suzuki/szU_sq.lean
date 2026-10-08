import Mathlib
import Submission.Work.Models.Port.Commons.GroupTheory.Suzuki.szU_mul

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.Suzuki

open Matrix

/-- `2 = 0` in `GF(2^(2n+1))`. -/
private lemma szU_sq_two_eq_zero (n : ℕ) : (2 : GaloisField 2 (2 * n + 1)) = 0 := by
  have := CharP.cast_eq_zero (GaloisField 2 (2 * n + 1)) 2
  simpa using this

theorem szU_sq (n : ℕ) (a b : GaloisField 2 (2 * n + 1)) :
    !![1, a, b, a ^ (2 + 2 ^ (n + 1)) + a * b + b ^ (2 ^ (n + 1));
       0, 1, a ^ (2 ^ (n + 1)), a ^ (1 + 2 ^ (n + 1)) + b;
       0, 0, 1, a;
       0, 0, 0, 1] *
    !![1, a, b, a ^ (2 + 2 ^ (n + 1)) + a * b + b ^ (2 ^ (n + 1));
       0, 1, a ^ (2 ^ (n + 1)), a ^ (1 + 2 ^ (n + 1)) + b;
       0, 0, 1, a;
       0, 0, 0, 1] =
    !![1, 0, a ^ (1 + 2 ^ (n + 1)), (a ^ (1 + 2 ^ (n + 1))) ^ (2 ^ (n + 1));
       0, 1, 0, a ^ (1 + 2 ^ (n + 1));
       0, 0, 1, 0;
       0, 0, 0, 1] := by
  have h2 : (2 : GaloisField 2 (2 * n + 1)) = 0 := szU_sq_two_eq_zero n
  have hself : ∀ x : GaloisField 2 (2 * n + 1), x + x = 0 := fun x => by
    rw [← two_mul, h2, zero_mul]
  have hp : a * a ^ (2 ^ (n + 1)) = a ^ (1 + 2 ^ (n + 1)) := by
    rw [pow_add a 1 (2 ^ (n + 1)), pow_one]
  rw [szU_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hself, hp]

end Commons.GroupTheory.Suzuki
