import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki.SzAuto

/-- Arithmetic identity for the geometric-like series `∑_{i<m} 2^(s*i)`, shifted by one step. -/
private lemma sum_pow_two_step (s m : ℕ) :
    (Finset.sum (Finset.range (m+1)) (fun i => 2 ^ (s * i)))
      = 1 + (Finset.sum (Finset.range m) (fun i => 2 ^ (s * i))) * 2 ^ s := by
  rw [Finset.sum_range_succ', Finset.sum_mul, Nat.add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  show 2 ^ (s * (i+1)) = 2 ^ (s * i) * 2 ^ s
  rw [← pow_add, Nat.mul_add, Nat.mul_one]

/-- Iterates of the map `y ↦ c * y ^ (2 ^ s)` over a field of characteristic `2`.
Concretely, `m`-fold iteration multiplies by `c ^ (∑_{i<m} 2^(s*i))` and raises `y` to
`2 ^ (s*m)`. -/
theorem iterate_powmap {n : ℕ} (s : ℕ) (c : GaloisField 2 n) (m : ℕ) (y : GaloisField 2 n) :
    (fun y : GaloisField 2 n => c * y ^ (2 ^ s))^[m] y
      = c ^ (Finset.sum (Finset.range m) (fun i => 2 ^ (s * i))) * y ^ (2 ^ (s * m)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, mul_pow, ← pow_mul, ← pow_mul,
      ← mul_assoc, ← pow_succ',
      Nat.add_comm ((Finset.sum (Finset.range m) (fun i => 2 ^ (s * i))) * 2 ^ s) 1,
      ← sum_pow_two_step s m, ← pow_add, Nat.mul_succ]

end Work.ZassenhausSuzuki.SzAuto
