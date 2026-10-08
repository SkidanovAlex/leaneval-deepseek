import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
Basic helper lemmas about powers of two, used for the `k = 0` case of Higman's congruence.

The main content is that the "odd part" of an equality `2 ^ a * f = 2 ^ d * g` with `f, g` odd
forces `a = d` and `f = g`.
-/

namespace Work.Higman.Q3.L12

/-- If `2 ^ m` is odd then `m = 0`. -/
theorem odd_two_pow {m : ℕ} (h : Odd (2 ^ m)) : m = 0 := by
  have h' : ¬ Even (2 ^ m) := Nat.not_even_iff_odd.mpr h
  rw [Nat.even_pow] at h'
  simpa using h'

/-- `2 ^ u + 2 ^ u = 2 ^ (u + 1)`. -/
theorem two_pow_add_self (u : ℕ) : 2 ^ u + 2 ^ u = 2 ^ (u + 1) := by
  rw [pow_succ]; ring

/-- `2 ^ k` is even for `k ≥ 1`. -/
theorem even_two_pow {k : ℕ} (hk : 1 ≤ k) : Even (2 ^ k) :=
  Nat.even_pow.mpr ⟨even_two, by omega⟩

/-- `1 +` an even number is odd. -/
theorem odd_one_add_even {n : ℕ} (h : Even n) : Odd (1 + n) := odd_one.add_even h

/-- `1 + 2 ^ k` is odd for `k ≥ 1`. -/
theorem odd_one_add_two_pow {k : ℕ} (hk : 1 ≤ k) : Odd (1 + 2 ^ k) :=
  odd_one_add_even (even_two_pow hk)

/-- **Cancellation of the power of two.**  If `f` and `g` are odd and `2 ^ a * f = 2 ^ d * g`,
then `a = d` and `f = g`. -/
theorem pow_two_mul_eq {a d f g : ℕ} (hf : Odd f) (hg : Odd g)
    (h : 2 ^ a * f = 2 ^ d * g) : a = d ∧ f = g := by
  rcases le_total a d with had | hda
  · have h1 : 2 ^ a * 2 ^ (d - a) = 2 ^ d := by rw [← pow_add, Nat.add_sub_of_le had]
    have key2 : 2 ^ a * (2 ^ (d - a) * g) = 2 ^ d * g := by rw [← mul_assoc, h1]
    have key3 : 2 ^ a * f = 2 ^ a * (2 ^ (d - a) * g) := by rw [key2]; exact h
    have key : f = 2 ^ (d - a) * g := Nat.mul_left_cancel (pow_pos (by norm_num) a) key3
    have hodd : Odd (2 ^ (d - a)) := Odd.of_dvd_nat hf ⟨g, key⟩
    have hda0 : d - a = 0 := odd_two_pow hodd
    have had' : a = d := by omega
    refine ⟨had', ?_⟩
    rw [had'] at key
    simpa using key
  · have h1 : 2 ^ d * 2 ^ (a - d) = 2 ^ a := by rw [← pow_add, Nat.add_sub_of_le hda]
    have key2 : 2 ^ d * (2 ^ (a - d) * f) = 2 ^ a * f := by rw [← mul_assoc, h1]
    have key3 : 2 ^ d * g = 2 ^ d * (2 ^ (a - d) * f) := by rw [key2]; exact h.symm
    have key : g = 2 ^ (a - d) * f := Nat.mul_left_cancel (pow_pos (by norm_num) d) key3
    have hodd : Odd (2 ^ (a - d)) := Odd.of_dvd_nat hg ⟨f, key⟩
    have had0 : a - d = 0 := odd_two_pow hodd
    have had' : a = d := by omega
    refine ⟨had', ?_⟩
    rw [had'] at key
    simpa using key.symm

end Work.Higman.Q3.L12
