import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.HallHigman

/-- In characteristic `p`, an endomorphism of order dividing `p ^ n` is unipotent:
`(f - 1) ^ (p ^ n) = 0`. -/
lemma sub_one_pow_prime_pow_eq_zero {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    {p n : ℕ} [Fact p.Prime] [CharP K p] (f : Module.End K M) (h : f ^ (p ^ n) = 1) :
    (f - 1) ^ (p ^ n) = 0 := by
  -- In `Module.End K M`, the natural number `p` is zero because `K` has characteristic `p`.
  have hp0 : (p : Module.End K M) = 0 := by
    have : (p : K) • (1 : Module.End K M) = (p : Module.End K M) := by
      rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_one]
    rw [← this, CharP.cast_eq_zero K p, zero_smul]
  -- Freshman's dream in the (noncommutative) ring `Module.End K M`, applied to the
  -- commuting elements `f - 1` and `1`.
  have hcomm : Commute (f - 1) (1 : Module.End K M) := Commute.one_right _
  have key := hcomm.add_pow_prime_pow_eq' (Fact.out : p.Prime) n
  rw [sub_add_cancel] at key
  -- Simplify: `1 ^ (p ^ n) = 1`, and the extra `p * (...)` term vanishes as `(p : End) = 0`.
  rw [one_pow, hp0, zero_mul, add_zero] at key
  rw [h] at key
  have : (f - 1) ^ (p ^ n) = 1 - 1 := (eq_sub_iff_add_eq).mpr key.symm
  simpa using this

end Work.HallHigman
