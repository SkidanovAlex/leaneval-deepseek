import Mathlib

namespace Work.BG

/--
Arithmetic lemma (BG, used in `fourDvdK`).

If `n = 2 ^ j` with `2 ≤ j`, `a` and `s` are odd, and `a * k = (n / 2) * s`,
then `k = (n / 2) * m` for some odd `m`.

Proof: `n / 2 = 2 ^ (j - 1)` is a power of two, hence coprime to the odd `a`;
from `2 ^ (j - 1) ∣ a * k` we get `2 ^ (j - 1) ∣ k`, say `k = 2 ^ (j - 1) * m`.
Substituting and cancelling the positive factor `2 ^ (j - 1)` yields `a * m = s`,
so `m` is odd because `a * m` is odd.
-/
theorem exists_odd_mul_of_odd_eq {n a k s : ℕ} (hn : ∃ j : ℕ, 2 ≤ j ∧ n = 2 ^ j)
    (ha : Odd a) (hs : Odd s) (h : a * k = (n / 2) * s) :
    ∃ m : ℕ, Odd m ∧ k = (n / 2) * m := by
  obtain ⟨j, hj, rfl⟩ := hn
  have hd : (2 : ℕ) ^ j / 2 = 2 ^ (j - 1) := by
    cases j with
    | zero => omega
    | succ i => rw [pow_succ]; simp
  rw [hd] at h ⊢
  have hcop : (2 ^ (j - 1)).Coprime a :=
    Nat.Coprime.pow_left (j - 1) (Nat.coprime_two_right.mpr ha).symm
  have hdvd : 2 ^ (j - 1) ∣ k :=
    hcop.dvd_of_dvd_mul_right ⟨s, by rw [mul_comm]; exact h⟩
  obtain ⟨m, rfl⟩ := hdvd
  have hpos : 0 < 2 ^ (j - 1) := pow_pos (by norm_num) _
  have ham : a * m = s := by
    have hh : 2 ^ (j - 1) * (a * m) = 2 ^ (j - 1) * s := by rw [← h]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos hh
  exact ⟨m, by have hs' : Odd (a * m) := ham ▸ hs; exact Nat.Odd.of_mul_right hs', rfl⟩

end Work.BG
