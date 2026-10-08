import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.HallHigman

/-- If `n * n = 0`, then `(1 + n) ^ k = 1 + k * n` for every `k`. -/
lemma one_add_pow_eq_of_mul_self_eq_zero {R : Type*} [Ring R] (n : R) (hn : n * n = 0) :
    ∀ (k : ℕ), (1 + n) ^ k = 1 + (k : R) * n := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, add_mul, one_mul, mul_add, mul_one]
    rw [mul_assoc, hn, mul_zero, add_zero]
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    abel

/-- In a ring, a `b`-th root of unity which is unipotent of index `2` is trivial whenever
`b` is invertible. -/
theorem ring_eq_one_of_pow_eq_one_of_sq_sub_one_eq_zero {R : Type*} [Ring R] {b : ℕ}
    (hunit : IsUnit (b : R)) {f : R} (hpow : f ^ b = 1) (hsq : (f - 1) ^ 2 = 0) : f = 1 := by
  let n := f - 1
  have hn : n = f - 1 := rfl
  have hsq' : n * n = 0 := by rw [hn, ← pow_two]; exact hsq
  have hf : f = 1 + n := by rw [hn]; abel
  have hbn : (b : R) * n = 0 := by
    have h1 : (1 + n) ^ b = 1 := by rw [← hf]; exact hpow
    rw [one_add_pow_eq_of_mul_self_eq_zero n hsq' b] at h1
    exact add_left_cancel (show 1 + (b : R) * n = 1 + 0 by rw [h1, add_zero])
  have hn0 : n = 0 := (IsUnit.mul_right_eq_zero hunit).mp hbn
  rw [hf, hn0, add_zero]

/-- In characteristic `p`, a `b`-th root of unity with `p ∤ b` that is unipotent of index `2`
is trivial. -/
theorem eq_one_of_pow_eq_one_of_sq_sub_one_eq_zero {p : ℕ} [Fact p.Prime] {K M : Type*} [Field K]
    [CharP K p] [AddCommGroup M] [Module K M] {b : ℕ} (hb : ¬ p ∣ b) {f : Module.End K M}
    (hpow : f ^ b = 1) (hsq : (f - 1) ^ 2 = 0) : f = 1 := by
  have hunitK : IsUnit ((b : ℕ) : K) := (CharP.isUnit_natCast_iff (R := K) (Fact.out)).2 hb
  have hunit : IsUnit ((b : ℕ) : Module.End K M) := by
    rw [← map_natCast (algebraMap K (Module.End K M)) b]
    exact hunitK.map (algebraMap K (Module.End K M))
  exact ring_eq_one_of_pow_eq_one_of_sq_sub_one_eq_zero hunit hpow hsq

end Work.HallHigman
