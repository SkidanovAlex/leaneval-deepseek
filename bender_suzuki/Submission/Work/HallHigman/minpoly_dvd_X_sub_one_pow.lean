import Mathlib
import Submission.Work.HallHigman.sub_one_pow_prime_pow_eq_zero

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.HallHigman

open Polynomial in
/-- In characteristic `p`, if `f ^ (p ^ n) = 1` then the minimal polynomial of `f`
divides `(X - 1) ^ (p ^ n)`. -/
lemma minpoly_dvd_X_sub_one_pow {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    {p n : ℕ} [Fact p.Prime] [CharP K p] (f : Module.End K M) (h : f ^ (p ^ n) = 1) :
    minpoly K f ∣ (X - 1) ^ (p ^ n) := by
  rw [minpoly.dvd_iff]
  rw [map_pow, aeval_sub, aeval_X, aeval_one, sub_one_pow_prime_pow_eq_zero f h]

end Work.HallHigman
