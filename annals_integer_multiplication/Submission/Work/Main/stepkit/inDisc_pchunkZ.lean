import Mathlib
import Submission.Work.Main.defs

namespace Work.Main.stepkit

/-- A base-`2^b` chunk (the padding value `0` included) is `< 2^b`. -/
private theorem pchunk_lt_two_pow (x b N m : ℕ) : pchunk x b N m < 2 ^ b := by
  simp only [pchunk]
  by_cases h : m < N
  · simp only [h, ite_true]
    exact Nat.mod_lt _ (by positivity)
  · simp only [h, ite_false]
    exact by positivity

/-- If `n < 2^b ≤ 2^p`, the fixed-point complex number `n · 2^{p-b} + 0·i` lies in the disc
`C̃◦` of radius `2^p` (paper §2.2: its value `n/2^b` has modulus `< 1`). -/
theorem inDisc_mul_pow {p b n : ℕ} (hb : b ≤ p) (hn : n < 2 ^ b) :
    HvdH.inDisc p (((n : ℤ) * 2 ^ (p - b), 0) : ℤ × ℤ) := by
  simp only [HvdH.inDisc]
  have hn' : (n : ℤ) ≤ (2 : ℤ) ^ b := by
    have h : n ≤ 2 ^ b := le_of_lt hn
    calc (n : ℤ) ≤ ((2 ^ b : ℕ) : ℤ) := by exact_mod_cast h
      _ = (2 : ℤ) ^ b := by push_cast; ring
  have h1 : (n : ℤ) * (2 : ℤ) ^ (p - b) ≤ (2 : ℤ) ^ p := by
    calc (n : ℤ) * (2 : ℤ) ^ (p - b) ≤ (2 : ℤ) ^ b * (2 : ℤ) ^ (p - b) :=
          mul_le_mul_of_nonneg_right hn' (by positivity)
      _ = (2 : ℤ) ^ (b + (p - b)) := by rw [pow_add]
      _ = (2 : ℤ) ^ p := by rw [Nat.add_sub_of_le hb]
  have h0 : 0 ≤ (n : ℤ) * (2 : ℤ) ^ (p - b) := by positivity
  have hsq : ((n : ℤ) * (2 : ℤ) ^ (p - b)) ^ 2 ≤ ((2 : ℤ) ^ p) ^ 2 :=
    pow_le_pow_left₀ h0 h1 2
  have h4 : (4 : ℤ) ^ p = ((2 : ℤ) ^ p) ^ 2 := by
    rw [show (4 : ℤ) = (2 : ℤ) ^ 2 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm 2 p]
  rw [h4]
  simpa using hsq

theorem inDisc_pchunkZ (x b N' S p m : ℕ) (hb : b ≤ p) :
    HvdH.inDisc p (pchunkZ x b N' S (p - b) m) := by
  have h := inDisc_mul_pow (p := p) (b := b) (n := pchunk x b N' m) hb
    (pchunk_lt_two_pow x b N' m)
  simpa [pchunkZ, pchunkN] using h

end Work.Main.stepkit
