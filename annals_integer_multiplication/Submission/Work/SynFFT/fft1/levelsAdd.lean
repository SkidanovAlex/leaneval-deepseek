import Mathlib
import Submission.Work.SynFFT.kit2

/-!
# Splitting `levels` into a prefix and a suffix
-/

set_option autoImplicit false

namespace Work.SynFFT

theorem levelsAdd (r : ℕ) (sgn : ℤ) (t : ℕ) (a : Arr r) (i j : ℕ) :
    levels r sgn t (i + j) a = levels r sgn (t / 2 ^ i) j (levels r sgn t i a) := by
  induction i generalizing t a with
  | zero => simp [levels]
  | succ i ih =>
      have h1 : i + 1 + j = (i + j) + 1 := by omega
      rw [h1]
      rw [show levels r sgn t ((i + j) + 1) a
            = levels r sgn (t / 2) (i + j) (lvlN r t sgn a) from rfl]
      rw [ih (t / 2) (lvlN r t sgn a)]
      rw [show levels r sgn t (i + 1) a
            = levels r sgn (t / 2) i (lvlN r t sgn a) from rfl]
      rw [show (t / 2) / 2 ^ i = t / 2 ^ (i + 1) by
        rw [Nat.div_div_eq_div_mul, show 2 * 2 ^ i = 2 ^ (i + 1) by rw [pow_succ']]]

end Work.SynFFT
