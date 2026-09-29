import Mathlib
import Submission.Work.Main.defs

namespace Work.Main.chunks

open Work.Main

/-- Every base-`2^b` chunk of `x` is `< 2^b` (the padding branch is `0 ≤ 2^b`). -/
private theorem pchunk_lt (x b N i : ℕ) : pchunk x b N i < 2 ^ b := by
  unfold pchunk
  split
  · exact Nat.mod_lt _ (Nat.two_pow_pos b)
  · exact Nat.two_pow_pos b

/-- Crude bound on the chunk-product coefficient: at most `N` summands, each a product of two
chunks, hence each `≤ (2^b - 1)^2`. -/
private theorem hcoeff_le (x y b N m : ℕ) :
    hcoeff x y b N m ≤ N * ((2 ^ b - 1) * (2 ^ b - 1)) := by
  have hterm : ∀ i ∈ Finset.range N,
      (if i ≤ m then pchunk x b N i * pchunk y b N (m - i) else 0) ≤
        (2 ^ b - 1) * (2 ^ b - 1) := by
    intro i _
    split
    · exact Nat.mul_le_mul (Nat.le_pred_of_lt (pchunk_lt x b N i))
        (Nat.le_pred_of_lt (pchunk_lt y b N (m - i)))
    · exact Nat.zero_le _
  calc hcoeff x y b N m
      = ∑ i ∈ Finset.range N,
          (if i ≤ m then pchunk x b N i * pchunk y b N (m - i) else 0) := rfl
    _ ≤ (Finset.range N).card • ((2 ^ b - 1) * (2 ^ b - 1)) :=
        Finset.sum_le_card_nsmul _ _ _ hterm
    _ = N * ((2 ^ b - 1) * (2 ^ b - 1)) := by simp

/-- `N ≤ 2^b` further bounds the crude estimate by `2^{3b}`; the inequality is strict because
either `N = 0` or `N * (2^b - 1)^2 < N * 2^{2b} ≤ 2^{3b}`. -/
theorem hcoeff_lt {x y b N m : ℕ} (hN : N ≤ 2 ^ b) : hcoeff x y b N m < 2 ^ (3 * b) := by
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    simp [hcoeff]
  refine lt_of_le_of_lt (hcoeff_le x y b N m) ?_
  have hpow : (0 : ℕ) < 2 ^ b := Nat.two_pow_pos b
  have h1 : 2 ^ b - 1 < 2 ^ b := Nat.sub_lt hpow one_pos
  have hsq : (2 ^ b - 1) * (2 ^ b - 1) < 2 ^ b * 2 ^ b :=
    mul_lt_mul'' h1 h1 (Nat.zero_le _) (Nat.zero_le _)
  calc N * ((2 ^ b - 1) * (2 ^ b - 1)) < N * (2 ^ b * 2 ^ b) :=
        Nat.mul_lt_mul_of_pos_left hsq hpos
    _ ≤ 2 ^ b * (2 ^ b * 2 ^ b) := Nat.mul_le_mul_right _ hN
    _ = 2 ^ (3 * b) := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega

end Work.Main.chunks
