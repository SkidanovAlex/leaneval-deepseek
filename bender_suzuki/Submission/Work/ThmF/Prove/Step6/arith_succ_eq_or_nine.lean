import Mathlib
import Submission.Work.ThmF.Tools.External

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.Prove.Step6

/-- If `n = 2^b` and `n + 1 = f^m` with `f` a prime and `m ≥ 1`, then `n + 1 = f` or
`n + 1 = 9`.  This is the arithmetic consequence of Huppert–Blackburn IX (2-7)
(`ArithmeticNineTwoSeven`): the only case in which `f` is even is `f = 2`, and then the equation
`2^m = 2^b + 1` forces `b = 0`, `m = 1`, so `n + 1 = 2 = f`. -/
theorem arith_succ_eq_or_nine {n f : ℕ} (hf : f.Prime) (hpow : ∃ b, n = 2 ^ b)
    (hlink : ∃ m : ℕ, 1 ≤ m ∧ n + 1 = f ^ m) (hA : Work.ThmF.ArithmeticNineTwoSeven) :
    n + 1 = f ∨ n + 1 = 9 := by
  obtain ⟨b, hb⟩ := hpow
  obtain ⟨m, hm1, hm⟩ := hlink
  -- The link equation, with `n` eliminated.
  have hfm : f ^ m = 2 ^ b + 1 := by rw [← hm, hb]
  by_cases hf2 : f = 2
  · -- `f = 2`: then `2 ^ m = 2 ^ b + 1`, which forces `2 ^ b = 1`.
    subst hf2
    have hbm : 2 ^ b < 2 ^ m := by rw [hfm]; exact Nat.lt_succ_self _
    have hb_lt : b < m := (Nat.pow_lt_pow_iff_right (show 1 < 2 by norm_num)).mp hbm
    have hdvd : 2 ^ b ∣ 2 ^ m := Nat.pow_dvd_pow 2 (le_of_lt hb_lt)
    have hdvd1 : 2 ^ b ∣ 1 :=
      (Nat.dvd_add_iff_right (dvd_refl (2 ^ b))).mpr (hfm ▸ hdvd)
    have h1 : 2 ^ b = 1 := Nat.dvd_one.mp hdvd1
    left
    calc n + 1 = 2 ^ m := hm
      _ = 2 ^ b + 1 := hfm
      _ = 1 + 1 := by rw [h1]
      _ = 2 := by norm_num
  · -- `f` odd: apply the external arithmetic input.
    have hfold : Odd f := hf.odd_of_ne_two hf2
    rcases hA f m b hfold hf.two_le (by omega) hfm with h1 | h9
    · left; rw [hm, h1, pow_one]
    · right; rw [hm, h9]

end Work.ThmF.Prove.Step6
