/-
# Dyadic arithmetic: rounding down to multiples of `2 ^ m`

The basic engine of the (one- and two-dimensional) Rademacher--Menshov inequalities is the
telescoping

`a N = ∑_{m < M} (a (rnd N m) - a (rnd N (m+1)))`,   valid whenever `2 ^ M > N`,

where `rnd N m = 2 ^ m * (N / 2 ^ m)` is the largest multiple of `2 ^ m` below `N`.  Each
summand is either `0` or the increment of a single *aligned* dyadic block `(L, L + 2 ^ m]`; this
is the whole combinatorial content of the Rademacher--Menshov inequalities
(`Work.Analysis.Variation.rademacher_menshov_one_dim`,
`…rademacher_menshov_two_dim`).
-/
import Submission.Work.Analysis.Variation.Defs

set_option autoImplicit false

open scoped BigOperators ENNReal
open Finset

namespace Work.Analysis.Variation

lemma rnd_le (N m : ℕ) : rnd N m ≤ N := Nat.mul_div_le N (2 ^ m)

lemma dvd_rnd (N m : ℕ) : 2 ^ m ∣ rnd N m := ⟨N / 2 ^ m, rfl⟩

lemma rnd_mono (m : ℕ) : Monotone (fun N => rnd N m) :=
  fun _a _b hab => Nat.mul_le_mul_left _ (Nat.div_le_div_right hab)

lemma rnd_eq_zero_of_lt {N m : ℕ} (h : N < 2 ^ m) : rnd N m = 0 := by
  rw [rnd, Nat.div_eq_of_lt h, mul_zero]

lemma rnd_eq_self {N m : ℕ} (h : 2 ^ m ∣ N) : rnd N m = N := by
  obtain ⟨c, rfl⟩ := h
  rw [rnd, Nat.mul_div_cancel_left c (by positivity : (0:ℕ) < 2 ^ m)]

lemma rnd_zero (m : ℕ) : rnd 0 m = 0 := rnd_eq_zero_of_lt (by positivity)

lemma div_two_pow_eq (N m : ℕ) : N / 2 ^ m = 2 * (N / 2 ^ (m + 1)) + (N / 2 ^ m) % 2 := by
  have h : N / 2 ^ (m + 1) = N / 2 ^ m / 2 := by rw [pow_succ, Nat.div_div_eq_div_mul]
  rw [h]
  exact (Nat.div_add_mod (N / 2 ^ m) 2).symm

lemma two_mul_div_two_pow (N m : ℕ) :
    2 * (N / 2 ^ (m + 1)) = N / 2 ^ m - (N / 2 ^ m) % 2 := by
  have h := div_two_pow_eq N m
  have hle := Nat.mod_le (N / 2 ^ m) 2
  omega

/-- The two inputs of a dyadic telescoping step: `rnd N (m+1) = 2 ^ m * k` and
`rnd N m = 2 ^ m * (k - k % 2)` where `k = N / 2 ^ m`. -/
lemma rnd_succ_eq (N m : ℕ) : rnd N (m + 1) = 2 ^ m * (N / 2 ^ m - (N / 2 ^ m) % 2) := by
  rw [rnd]
  have h : 2 ^ (m + 1) * (N / 2 ^ (m + 1)) = 2 ^ m * (2 * (N / 2 ^ (m + 1))) := by
    rw [pow_succ]; ring
  rw [h, two_mul_div_two_pow]

/-- `rnd N m` and `rnd N (m+1)` differ by `0` or by `2 ^ m`; equivalently, the block
`(rnd N (m+1), rnd N m]` is either empty or an aligned dyadic block of size `2 ^ m`. -/
lemma rnd_dichotomy (N m : ℕ) :
    rnd N m = rnd N (m + 1) ∨ rnd N m = rnd N (m + 1) + 2 ^ m := by
  obtain ⟨k, hk⟩ : ∃ k, N / 2 ^ m = k := ⟨_, rfl⟩
  have hk2 : 2 * (k / 2) = k - k % 2 := by
    have h := Nat.div_add_mod k 2
    have hle := Nat.mod_le k 2
    omega
  have hrnd1 : rnd N m = 2 ^ m * k := by rw [rnd, hk]
  have hrnd2 : rnd N (m + 1) = 2 ^ m * (k - k % 2) := by
    rw [rnd, pow_succ, ← Nat.div_div_eq_div_mul, hk, mul_assoc, hk2]
  rw [hrnd1, hrnd2]
  rcases Nat.mod_two_eq_zero_or_one k with h0 | h1
  · left; rw [h0]; simp
  · right
    rw [h1, Nat.mul_sub_left_distrib, Nat.mul_one, Nat.sub_add_cancel]
    exact Nat.le_mul_of_pos_right _ (by omega)

/-- The telescoping along the dyadic tower of `N`. -/
lemma telescope_rnd (a : ℕ → ℂ) {N M : ℕ} (h : N < 2 ^ M) :
    ∑ m ∈ Finset.range M, (a (rnd N m) - a (rnd N (m + 1))) = a N - a 0 := by
  rw [Finset.sum_range_sub' (fun m => a (rnd N m)) M]
  rw [show rnd N 0 = N from by rw [rnd_eq_self]; exact one_dvd N, rnd_eq_zero_of_lt h]

end Work.Analysis.Variation
