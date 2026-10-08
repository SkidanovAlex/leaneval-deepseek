import Mathlib
import Submission.Work.Hall.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hall.PiNat

/-- If `n` is both a `π`-number and a `π'`-number and `n ≠ 0`, then `n = 1`:
a nontrivial positive integer has a prime divisor, which cannot lie in both `π` and its
complement. -/
theorem hall_eq_one_of_isPiNat {π : ℕ → Prop} {n : ℕ} (hm : Work.Hall.IsPiNat π n)
    (hn : Work.Hall.IsPiNat (fun p => ¬ π p) n) (h0 : n ≠ 0) : n = 1 := by
  by_contra h1
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd h1
  exact (hn p hp hd) (hm p hp hd)

end Work.Hall.PiNat
